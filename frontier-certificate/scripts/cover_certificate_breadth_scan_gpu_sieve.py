#!/usr/bin/env python3
"""
GPU AP-sieve breadth scan over OPEN mod-529 sub-APs.

Replaces the trial-division kernel in
`cover_certificate_breadth_scan_gpu.py` with an arithmetic-progression
sieve, which is the algorithmically correct shape for this workload
.

Algorithm
---------
For F_k(u) = A·u + (B_sub - k) with A = 2520·46189·529 = 61,573,632,120,
factor A as 2^3 · 3^2 · 5 · 7 · 11 · 13 · 17 · 19 · 23^2.  The 9 primes
P_A = {2,3,5,7,11,13,17,19,23} divide A; the remaining primes ≤ B are
coprime to A.

For p coprime to A:
    F_k(u) ≡ 0 (mod p)  ⇔  u ≡ -A^{-1} (B_sub - k) (mod p)  =: u_0(k, p)
    Sweep u over u_0, u_0+p, u_0+2p, ..., i.e. ~U/p marks.  At each mark,
    extract the exact p-adic valuation by repeated division.

For p ∈ P_A:
    F_k(u) ≡ B_sub - k (mod p), constant in u.  Either every u or no u
    has p | F_k(u).  When every u does, compute v_p(F_k(u)) per u via
    explicit p-adic peeling (handled with a small dense kernel, not the
    sparse sieve).

Stages
------
  Stage 1 (kernel `trial_divide_PA`): trial-divide every (u, k) target by
    the 9 primes in P_A; update target_residual and tau_partial in place.
    Race-free: each thread owns one (u, k); primes iterated within thread.

  Stage 2 (kernel `sieve_marks`): for each prime p coprime to A and each
    k, mark u ≡ u_0(k, p) (mod p).  Per-mark thread computes v_p(F_k(u))
    on the *original* F_k(u) (recomputed inside the kernel — no race on
    the residual matrix).  Atomically multiplies tau_partial and
    small_product.

  Stage 3 (vectorized GPU): residual cofactor c = target_residual /
    small_product is provably 1 or prime (sqrt-scale invariant: B²>target_max).
    τ_co = (1 if c==1 else 2); τ = tau_partial · τ_co.  No host classify.

Validation:
    Drop-in compatible per-record schema with `cover_certificate_breadth_scan.py`.
    Diff-by-(r, s_class) lookup against the committed CPU output JSON
    must be byte-identical for every emitted record.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from pathlib import Path

import cupy as cp
import numpy as np
import sympy

REPO = Path(__file__).resolve().parent.parent

# Sub-AP constants (must match cover_certificate_breadth_scan.py)
M_BASE = 46189
TWENTY_FIVE_TWENTY = 2520
SUBAP_MOD = 529
A_CONST = TWENTY_FIVE_TWENTY * M_BASE * SUBAP_MOD # 61,573,632,120
PRIMES_DIVIDING_A = (2, 3, 5, 7, 11, 13, 17, 19, 23)


def _default_prime_bound() -> int:
    """Default sieve bound: floor(sqrt(target_max)) so that any cofactor
    after sieving has ≤ 1 prime > B (it is 1 or prime).  This eliminates
    the host cofactor classification step entirely.

    target_max = A·U + max_B_sub, with U from env var U_BOUND and
    max_B_sub = 2520·(46189·528 + 46188) for the canonical 41 frontier.
    """
    u_bound = int(os.environ.get('U_BOUND', '50000'))
    max_B_sub = TWENTY_FIVE_TWENTY * (M_BASE * (SUBAP_MOD - 1) + (M_BASE - 1))
    target_max = A_CONST * u_bound + max_B_sub
    return math.isqrt(target_max) + 1 # +1 ensures B² > target_max strictly

SMALL_PRIME_BOUND = int(os.environ.get('SMALL_PRIME_BOUND', str(_default_prime_bound())))


def _parse_k_cover(env_val: str, default):
    if not env_val:
        return list(default)
    try:
        return sorted({int(x.strip()) for x in env_val.split(',') if x.strip()})
    except ValueError:
        raise SystemExit(f"K_COVER env var must be comma-separated ints, got: {env_val!r}")


K_COVER = _parse_k_cover(os.environ.get('K_COVER', ''), [1, 2, 3, 4, 5, 6, 7, 8])
HIGH_K_BUCKETS = sorted([k for k in K_COVER if k >= 6])
HIGH_K_SAMPLE_LIMIT = 10

U_BOUND = int(os.environ.get('U_BOUND', '50000'))
SUB_AP_LIMIT = int(os.environ.get('SUB_AP_LIMIT', '0'))

_DEFAULT_MANIFEST = REPO / 'data' / 'residue_attack' / 'open_subap_manifest.json'
MANIFEST_PATH = Path(os.environ.get('MANIFEST_PATH', str(_DEFAULT_MANIFEST)))
_DEFAULT_OUT_DIR = REPO / 'data' / 'residue_attack'
OUT_DIR = Path(os.environ.get('OUT_DIR', str(_DEFAULT_OUT_DIR)))


def sieve_primes(bound: int) -> list[int]:
    sv = bytearray(bound + 1)
    for i in range(2, int(bound ** 0.5) + 1):
        if not sv[i]:
            sv[i * i::i] = b'\x01' * len(sv[i * i::i])
    return [i for i in range(2, bound + 1) if not sv[i]]


# ---------------------------------------------------------------------------
# CUDA kernels
# ---------------------------------------------------------------------------

# Stage 1: trial-divide every (u, k) target by the 9 primes dividing A.
# Each thread owns one (u, k) cell.  Race-free.
_KERNEL_STAGE1 = cp.RawKernel(r'''
extern "C" __global__
void trial_divide_PA(
    long long* __restrict__ target_residual,   // (N,) in/out
    long long* __restrict__ tau_partial,       // (N,) out (init = 1 from caller)
    const long long* __restrict__ primes_PA,
    const long long n_primes_PA,
    const long long N
) {
    long long idx = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;
    long long t = target_residual[idx];
    long long tp = 1;
    for (long long i = 0; i < n_primes_PA; i++) {
        long long p = primes_PA[i];
        if (t % p == 0) {
            long long e = 0;
            do { t /= p; e++; } while (t % p == 0);
            tp *= (e + 1);
        }
    }
    target_residual[idx] = t;
    tau_partial[idx] = tp;
}
''', 'trial_divide_PA')


# Stage 2 SETUP: per-(p_idx, k_idx) thread, compute u_0 and n_marks for the
# given (k, p) pair, in (n_coA, K) layout matching the sieve_marks kernel's
# pk_idx = p_idx * K + k_idx convention.
#
# Replaces the previous 7-op CuPy chain (diff / u0_by_kp / marks_by_kp /
# cp.where / .T.ravel × 2 / cumsum) with a single kernel + one cumsum.
# Eliminates ~6 intermediate (K, n_coA) device tensors per sub-AP, which
# dominated the per-sub-AP wall time in profiling at U=200k (84%) and is
# the bottleneck preventing GPU saturation at U=10⁷+.
#
# Output: u0_pk[p_idx*K + k_idx], marks_pk[p_idx*K + k_idx].
_KERNEL_STAGE2_SETUP = cp.RawKernel(r'''
extern "C" __global__
void stage2_setup(
    const long long  B_sub,
    const long long  U,
    const long long  K,
    const long long* __restrict__ primes_coA,
    const long long* __restrict__ A_inv,
    const long long* __restrict__ k_array,
    const long long  n_coA,
    long long* __restrict__ u0_pk,
    long long* __restrict__ marks_pk
) {
    long long pk_idx = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (pk_idx >= n_coA * K) return;
    long long p_idx = pk_idx / K;
    long long k_idx = pk_idx % K;
    long long p = primes_coA[p_idx];
    long long k_val = k_array[k_idx];
    // diff = (B_sub - k) mod p, non-negative residue
    // diff = (B_sub - k_val) mod p, normalized to [0, p-1].
    // C remainder of a (potentially) negative dividend by positive p is in
    // [-(p-1), 0], so a single += p correction lands the result in [0, p-1].
    long long diff = (B_sub - k_val) % p;
    if (diff < 0) diff += p;
    // u0 = -A_inv * diff mod p, normalized to [0, p-1].
    // A_inv in [1, p-1] and diff in [0, p-1], so A_inv * diff in [0, (p-1)*(p-1)].
    // Host-side guard last_prime*last_prime <= INT64_MAX ensures the multiply
    // does not overflow signed int64 before the modulo.
    long long u0 = (- (A_inv[p_idx] * diff)) % p;
    if (u0 < 0) u0 += p;
    // u must be >= 1; if u0 == 0 shift to p
    if (u0 == 0) u0 = p;
    // n_marks = floor((U - u0) / p) + 1 if u0 <= U else 0
    long long n_m = 0;
    if (u0 <= U) n_m = (U - u0) / p + 1;
    u0_pk[pk_idx] = u0;
    marks_pk[pk_idx] = n_m;
}
''', 'stage2_setup')


# Stage 2: sieve marks for primes coprime to A.
# One thread per mark.  Computes the original F_k(u), extracts v_p, atomically
# multiplies tau_partial[u, k] *= (e_p + 1) and small_product[u, k] *= p^e_p.
# small_product is later used by Stage 3 (on device) to compute residual cofactor.
_KERNEL_STAGE2 = cp.RawKernel(r'''
extern "C" __global__
void sieve_marks(
    const long long A,
    const long long B_sub,
    const long long U,
    const long long K,
    const long long* __restrict__ primes_coA,        // primes coprime to A
    const long long* __restrict__ k_array,           // (K,) values of k in K_COVER
    const long long* __restrict__ u0_kp,             // (n_primes_coA*K,) u_0
    const long long* __restrict__ marks_offset,      // (n_primes_coA*K + 1,) prefix sum
    const long long n_pk,                            // = n_primes_coA * K
    long long* __restrict__ tau_partial,             // (U*K,) atomic mul *= (e+1)
    long long* __restrict__ small_product,           // (U*K,) atomic mul *= p^e
    const long long total_marks
) {
    long long mark_idx = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (mark_idx >= total_marks) return;

    // Binary search for which (p_idx, k_idx) this mark belongs to.
    long long lo = 0, hi = n_pk - 1;
    while (lo < hi) {
        long long mid = (lo + hi + 1) / 2;
        if (marks_offset[mid] <= mark_idx) lo = mid;
        else hi = mid - 1;
    }
    long long pk_idx = lo;
    long long j = mark_idx - marks_offset[pk_idx];

    long long p_idx = pk_idx / K;
    long long k_idx = pk_idx % K;
    long long p = primes_coA[p_idx];
    long long u0 = u0_kp[pk_idx];
    long long u = u0 + j * p;
    if (u < 1 || u > U) return;

    long long t = A * u + (B_sub - k_array[k_idx]);
    long long e = 0;
    long long p_pow_e = 1;
    while (t % p == 0) {
        t /= p;
        e++;
        p_pow_e *= p;
    }
    if (e == 0) return;  // u was a marked position by construction; defensive

    long long flat = (u - 1) * K + k_idx;

    // atomicCAS-multiply on tau_partial[flat] *= (e + 1)
    long long mul1 = e + 1;
    unsigned long long *taddr = (unsigned long long*)&tau_partial[flat];
    unsigned long long old1 = *taddr, ass1;
    do {
        ass1 = old1;
        old1 = atomicCAS(taddr, ass1, (unsigned long long)((long long)ass1 * mul1));
    } while (ass1 != old1);

    // atomicCAS-multiply on small_product[flat] *= p_pow_e
    unsigned long long *saddr = (unsigned long long*)&small_product[flat];
    unsigned long long old2 = *saddr, ass2;
    do {
        ass2 = old2;
        old2 = atomicCAS(saddr, ass2,
                         (unsigned long long)((long long)ass2 * p_pow_e));
    } while (ass2 != old2);
}
''', 'sieve_marks')


# ---------------------------------------------------------------------------
# Host orchestration
# ---------------------------------------------------------------------------

def precompute_inverses(primes_coA: np.ndarray) -> np.ndarray:
    """Compute A^{-1} mod p for each prime coprime to A.  Returned as int64."""
    A = A_CONST
    out = np.empty(len(primes_coA), dtype=np.int64)
    for i, p in enumerate(primes_coA):
        out[i] = pow(int(A), -1, int(p))
    return out


def compute_tau_matrix_gpu_sieve(
    B_sub: int, U: int, k_array: list[int],
    primes_PA_dev: cp.ndarray,
    primes_coA_dev: cp.ndarray,
    A_inv_dev: cp.ndarray,
    last_prime: int,
    target_max: int,
) -> np.ndarray:
    """Returns exact (U, K) τ matrix using the AP-sieve algorithm.

    Correctness condition: SMALL_PRIME_BOUND ≥ ⌊√target_max⌋ + 1 so that
    after sieving every cofactor c satisfies c ≤ target_max < B², hence
    c is 1 or prime.  τ_co = (1 if c == 1 else 2), no host classify call.
    """
    K = len(k_array)
    N = U * K
 # Sqrt-scale correctness: cofactor c after sieve has all prime factors
 # > last_prime; for c composite, c ≥ (next prime after last_prime)².
 # Invariant: target_max < nextprime(last_prime)² so no composite cofactor
 # can exist.  Analysis showed `(last_prime+1)²` is overly strict in
 # prime-gap cases (e.g. U=1 with last_prime=350899, gap=25).
    np_lp = int(sympy.nextprime(int(last_prime)))
    if np_lp * np_lp <= target_max:
        raise SystemExit(
            f'sqrt-scale invariant violated: nextprime(last_prime)²={np_lp**2} '
            f'≤ target_max={target_max}.  Increase SMALL_PRIME_BOUND so the '
            f'sieve reaches above sqrt(target_max).  '
            f'(last_prime={last_prime}, np_lp={np_lp}.)')

 # Build target matrix on device: F_k(u) = A·u + (B_sub - k) for u=1..U.
 # Memory hardening for U=10^8 K=16 on 80GB H100: free `targets` and
 # `u_dev` immediately after `target_residual` is materialized; both
 # are 12.8 GB / 800 MB respectively at U=1e8 K=16 and are not used
 # again in this function.
    u_dev = cp.arange(1, U + 1, dtype=cp.int64)
    k_dev = cp.asarray(k_array, dtype=cp.int64)
    targets = (A_CONST * u_dev[:, None] + (B_sub - k_dev[None, :])
               ).reshape(-1).astype(cp.int64)
    target_residual = targets.copy()
    del targets, u_dev # free 13.6 GB at U=1e8 K=16; safe -- no later use
    tau_partial = cp.ones(N, dtype=cp.int64)
    small_product = cp.ones(N, dtype=cp.int64)

 # ----- Stage 1: trial-divide by primes dividing A -----
    threads = 256
    blocks = (N + threads - 1) // threads
    _KERNEL_STAGE1(
        (blocks,), (threads,),
        (target_residual, tau_partial, primes_PA_dev,
         np.int64(primes_PA_dev.size), np.int64(N)),
    )

 # ----- Stage 2: sieve over primes coprime to A -----
 # u_0(k, p) = (-A^{-1} · (B_sub - k)) mod p computed via a single fused
 # CUDA kernel (`_KERNEL_STAGE2_SETUP`). Replaces the previous 7-op CuPy
 # chain that allocated 6+ intermediate (K, n_coA) tensors per sub-AP.
 # Profile-driven optimization: at U=200k Stage 2 setup was 84% of
 # per-sub-AP wall (30 ms / 35 ms total) due to memory-pool churn and
 # kernel-launch serialization on the intermediate ops. This fused
 # kernel eliminates the intermediates entirely.
    n_coA = int(primes_coA_dev.size)
    n_pk = n_coA * K

 # Stage 2 setup memory model. Approx n_pk × 8 bytes at default bounds:
 #   U=10⁶, K=12 → n_pk ~ 1.63e8 → ~1.3 GB
 #   U=10⁶, K=16 → n_pk ~ 2.17e8 → ~1.7 GB
 #   U=10⁷, K=16 → n_pk ~ 6.46e8 → ~5.2 GB
 #   U=10⁸, K=16 → n_pk ~ 1.93e9 → ~15.5 GB
 #
 # Memory hardenings landed:
 # - Write Stage 2 marks counts directly into `marks_offset_dev[1:]`
 #   (no separate marks_pk_dev). Saves one n_pk allocation.
 # - cp.cumsum is NOT actually in-place under CuPy 14: its scan_core
 #   calls `_copy_in_args_if_needed` which materializes a fresh
 #   ~n_pk × 8 byte buffer for the input copy regardless of `out=`.
 #   Caught by a pre-launch smoke test (OOM at U=10⁸ K=16 on H100
 #   80GB). The transient copy is unavoidable under CuPy without a
 #   custom CUDA scan kernel.
 #
 # Combined Stage 2 peak with the cumsum copy transient included:
 #   3 × U·K × 8 (target_residual + tau_partial + small_product)
 # + u0_pk_dev (15.5)
 # + marks_offset_dev (15.5)
 # + cumsum copy transient (15.5)
 # + primes_coA_dev + A_inv_dev (≤ 2 GB)
 #
 # Concrete:
 #   U=10⁷, K=16: ~3.84 + ~15.6 + 2 ≈ 21 GB → fits H100 80GB easily
 #   U=10⁸, K=16: ~38.4 + ~46.5 + 2 ≈ 87 GB → DOES NOT FIT H100 80GB,
 #               fits H100 NVL 94GB or H200 141GB.
 #
 # The runpod_provision_and_run wrapper exposes `--gpu-type` to pick
 # H100 SXM5 80GB (default; works for U ≤ 10⁷ K=16) or
 # H200 141GB / H100 NVL 94GB (recommended for U=10⁸ K=16).
    u0_pk_dev = cp.empty(n_pk, dtype=cp.int64)
    marks_offset_dev = cp.empty(n_pk + 1, dtype=cp.int64)
    marks_offset_dev[0] = 0

    threads_setup = 256
    blocks_setup = (n_pk + threads_setup - 1) // threads_setup
 # Stage 2 setup kernel writes marks counts directly into the
 # marks_offset_dev[1:] slice (n_pk entries, contiguous view of the
 # base allocation offset by 8 bytes).  No intermediate marks_pk_dev.
    _KERNEL_STAGE2_SETUP(
        (blocks_setup,), (threads_setup,),
        (np.int64(B_sub), np.int64(U), np.int64(K),
         primes_coA_dev, A_inv_dev, k_dev,
         np.int64(n_coA), u0_pk_dev, marks_offset_dev[1:]),
    )

 # In-place cumulative sum on the [1:] slice.  marks_offset_dev[0]
 # remains 0 (set above); marks_offset_dev[j] for j >= 1 becomes
 # sum(marks_pk_counts[0..j-1]) — exclusive-prefix convention,
 # matching the existing sieve_marks kernel.
    cp.cumsum(marks_offset_dev[1:], out=marks_offset_dev[1:])
    total_marks = int(marks_offset_dev[-1].item())

    if total_marks > 0:
        threads2 = 256
        blocks2 = (total_marks + threads2 - 1) // threads2
        _KERNEL_STAGE2(
            (blocks2,), (threads2,),
            (np.int64(A_CONST), np.int64(B_sub), np.int64(U), np.int64(K),
             primes_coA_dev, k_dev, u0_pk_dev, marks_offset_dev,
             np.int64(n_coA * K),
             tau_partial, small_product, np.int64(total_marks)),
        )

    del u0_pk_dev, marks_offset_dev

 # ----- Stage 3: vectorized cofactor → τ -----
 # Memory hardening for U=10^8 K=16: free intermediates as soon as
 # they are no longer needed. Naive sequence at U=1e8 K=16 holds
 # target_residual + tau_partial + small_product + cofactor_dev +
 # tau_co_dev + out_dev + (target_residual % small_product transient)
 # = 7 * 12.8 GB = ~90 GB on a single H100 80GB. With targeted dels:
 #   1. Verify divisibility BEFORE allocating cofactor_dev so the
 #      sanity-check transient (12.8 GB) doesn't double-stack with
 #      cofactor_dev.
 #   2. Free target_residual + small_product immediately after
 #      cofactor_dev is materialized (no longer needed).
 #   3. Free cofactor_dev immediately after tau_co_dev is computed.
 #   4. Free tau_partial after out_dev is computed.
 # Final Stage 3 peak: ≈ 4 × 12.8 = 51 GB (target_residual +
 # small_product + tau_partial + transient). Fits 80 GB H100.

 # Cofactor c = target_residual / small_product, provably 1 or prime
 # (under sqrt-scale invariant).  τ_co = 1 if c == 1 else 2.
    if not bool(cp.all(target_residual % small_product == 0)):
        raise RuntimeError(
            'sieve invariant violated: target_residual not divisible by small_product')
    cofactor_dev = target_residual // small_product
    del target_residual, small_product # no longer needed; free 25.6 GB at U=1e8 K=16
    tau_co_dev = cp.where(cofactor_dev == 1, cp.int64(1), cp.int64(2))
    del cofactor_dev # free 12.8 GB
    out_dev = (tau_partial * tau_co_dev).reshape((U, K))
    del tau_partial, tau_co_dev # free 25.6 GB
    out_host = cp.asnumpy(out_dev)
    del out_dev
    return out_host


def first_kill_per_u(tau_matrix: np.ndarray, k_array: list[int]) -> np.ndarray:
    U, K = tau_matrix.shape
    bound = np.array([k + 2 for k in k_array], dtype=np.int64)
    kill_mask = tau_matrix > bound[None, :]
    first_idx = np.argmax(kill_mask, axis=1)
    any_kill = kill_mask.any(axis=1)
    out = np.zeros(U, dtype=np.int32)
    k_arr_np = np.array(k_array, dtype=np.int32)
    out[any_kill] = k_arr_np[first_idx[any_kill]]
    return out


def select_targets(manifest_path: Path, limit: int):
    if not manifest_path.exists():
        raise FileNotFoundError(
            f'open subap manifest not found at {manifest_path}')
    manifest = json.loads(manifest_path.read_text())
    open_pairs = manifest['open_pairs']
    pairs = [(int(p['r']), int(p['s_mod_529'])) for p in open_pairs]
    filt = os.environ.get('SUBAP_FILTER', '').strip()
    if filt:
        wanted = set()
        for token in filt.split(';'):
            token = token.strip()
            if not token:
                continue
            r_str, s_str = token.split(',')
            wanted.add((int(r_str), int(s_str)))
        manifest_set = set(pairs)
        missing = wanted - manifest_set
        if missing:
            raise SystemExit(f'SUBAP_FILTER pairs not in manifest: {sorted(missing)}')
        pairs = [p for p in pairs if p in wanted]
    if limit > 0:
        pairs = pairs[:limit]
    return pairs, manifest


def runtime_provenance() -> dict:
    import platform, subprocess
    info = {
        'python': sys.version.split()[0],
        'platform': platform.platform(),
        'hostname': platform.node(),
    }
    try:
        info['cupy'] = cp.__version__
    except Exception:
        pass
    try:
        info['gpu'] = subprocess.check_output(
            ['nvidia-smi', '--query-gpu=name', '--format=csv,noheader'],
            text=True).strip().splitlines()[0]
    except Exception:
        pass
    return info


def main():
    print(f'=== K={K_COVER} GPU AP-sieve breadth scan ===\n', file=sys.stderr)

 # Range checks
    if U_BOUND <= 0:
        raise SystemExit(f'U_BOUND must be positive, got {U_BOUND}')
    if not K_COVER:
        raise SystemExit('K_COVER must contain at least one shift')
    if min(K_COVER) < 1:
        raise SystemExit(f'K_COVER values must be ≥ 1, got {K_COVER}')
    target_max = A_CONST * U_BOUND + 2520 * (M_BASE * (SUBAP_MOD - 1) + (M_BASE - 1))
    if target_max > np.iinfo(np.int64).max:
        raise SystemExit(f'int64 overflow risk: target_max={target_max:,}')
    target_min = A_CONST - max(K_COVER)
    if target_min <= 0:
        raise SystemExit(f'F_k(1) ≤ 0 for max k={max(K_COVER)}')

    targets, manifest = select_targets(MANIFEST_PATH, limit=SUB_AP_LIMIT)
    print(f'Open sub-APs total: {manifest["aggregate"]["n_open_pairs"]}',
          file=sys.stderr)
    print(f'Targets: {len(targets)} (SUB_AP_LIMIT={SUB_AP_LIMIT or "all"})',
          file=sys.stderr)
    print(f'U={U_BOUND:,}; small-prime bound={SMALL_PRIME_BOUND:,}',
          file=sys.stderr)

 # Hardening: pre-sieve guard against oversized
 # SMALL_PRIME_BOUND that would silently overflow A_inv*diff in the
 # fused stage2_setup kernel. Faster fail than catching it post-sieve.
    INT64_MAX_PRESIEVE = (1 << 63) - 1
    if SMALL_PRIME_BOUND > math.isqrt(INT64_MAX_PRESIEVE):
        raise SystemExit(
            f'SMALL_PRIME_BOUND={SMALL_PRIME_BOUND:,} > isqrt(INT64_MAX)='
            f'{math.isqrt(INT64_MAX_PRESIEVE):,}; would overflow signed '
            f'int64 multiply in fused Stage 2 setup kernel. Cap '
            f'SMALL_PRIME_BOUND at isqrt(INT64_MAX) ≈ 3.04e9.')

    t0 = time.time()
    primes_all = sieve_primes(SMALL_PRIME_BOUND)
 # Use the explicit PRIMES_DIVIDING_A constant ,
 # so the contract is independent of SMALL_PRIME_BOUND.
    primes_PA = list(PRIMES_DIVIDING_A)
    primes_coA_h = np.asarray(
        [p for p in primes_all if p not in PRIMES_DIVIDING_A], dtype=np.int64)
    primes_PA_dev = cp.asarray(primes_PA, dtype=cp.int64)
    primes_coA_dev = cp.asarray(primes_coA_h, dtype=cp.int64)
    last_prime = primes_all[-1]
    A_inv_h = precompute_inverses(primes_coA_h)
    A_inv_dev = cp.asarray(A_inv_h, dtype=cp.int64)
    n_primes_all = len(primes_all)
    n_primes_PA = len(primes_PA)
    n_primes_coA = len(primes_coA_h)
    del primes_coA_h, A_inv_h, primes_all # free host arrays after device transfer
    print(f'Sieved {n_primes_all:,} primes  ({time.time()-t0:.1f}s); '
          f'P_A={n_primes_PA} coA={n_primes_coA}', file=sys.stderr)
    np_lp = int(sympy.nextprime(int(last_prime)))
    print(f'target_max={target_max:.3e}, last_prime={last_prime:,}, '
          f'nextprime(last_prime)²={np_lp**2:.3e}  '
          f'{"OK" if np_lp*np_lp > target_max else "INVARIANT VIOLATED"}',
          file=sys.stderr)

 # Hardening: A_inv * diff in the fused stage2_setup
 # kernel uses signed int64 multiply, so we need (p-1)² ≤ INT64_MAX.
 # Equivalently, last_prime ≤ isqrt(INT64_MAX) ≈ 3.04e9. Beyond that
 # we'd silently overflow before the modulo. Hard-fail at startup
 # instead of silently corrupting Stage 2 setup output.
    INT64_MAX = (1 << 63) - 1
    if last_prime * last_prime > INT64_MAX:
        raise SystemExit(
            f'last_prime={last_prime} too large: (last_prime)²={last_prime**2} '
            f'> INT64_MAX={INT64_MAX}. Stage 2 setup kernel uses signed int64 '
            f'multiply for A_inv * diff which would overflow. Reduce U_BOUND '
            f'(target_max < 9.2e18 → U_BOUND ≤ ~1.5e8 with the canonical 41 '
            f'frontier).')

 # Stage 2 setup peak device-memory estimate (one-time, logged here).
 # Uses n_primes_coA captured earlier (primes_all itself was deleted).
    n_pk_est = n_primes_coA * len(K_COVER)
 # u0_pk + marks_pk + marks_offset[n_pk+1]; +1 entry is one int64.
    setup_GB = (3 * n_pk_est + 1) * 8 / (1024 ** 3)
    print(f'Stage 2 setup peak device memory ≈ {setup_GB:.2f} GiB '
          f'((3·n_pk + 1) × 8 bytes; n_pk={n_pk_est:,})', file=sys.stderr)

    results = []
    grand_t0 = time.time()
    for i, (r, s_class) in enumerate(targets):
        t_sub = time.time()
        B_sub = TWENTY_FIVE_TWENTY * (M_BASE * s_class + r)
        tau_matrix = compute_tau_matrix_gpu_sieve(
            B_sub, U_BOUND, K_COVER,
            primes_PA_dev, primes_coA_dev, A_inv_dev,
            last_prime, target_max,
        )
        first_k = first_kill_per_u(tau_matrix, K_COVER)

 # Vectorized aggregation (replaces 10M-iteration Python for-loop
 # that was the dominant bottleneck at U=10⁷ scale: ~5s/sub-AP
 # of pure Python interpreter overhead, completely independent of
 # GPU work. Numpy vectorization brings it to ~1ms/sub-AP).
 # Hardening: skip astype(int64); bincount handles
 # any integer dtype, and the copy would be 800MB at U=10⁸.
        first_k_np = first_k
        K_max = max(K_COVER)
        bc = np.bincount(first_k_np, minlength=K_max + 1)
 # Coverage-total invariant: every cell is either a survivor (k=0)
 # or first-killed at some k in K_COVER. Hardening:
 # silently dropping invalid k values would undercount the result.
        coverage = int(bc[0]) + sum(int(bc[k]) for k in K_COVER)
        if coverage != U_BOUND:
            raise RuntimeError(
                f'aggregation coverage check failed: {coverage} '
                f'!= U_BOUND={U_BOUND}; first_k contains values outside '
                f'{{0}} ∪ K_COVER={K_COVER}.')
        by_k = {k: int(bc[k]) for k in K_COVER}
        by_k['none'] = int(bc[0])
        survivor_idx = np.flatnonzero(first_k_np == 0)
        survivors = [int(x) + 1 for x in survivor_idx] # u = u_idx + 1
        nonzero_k = [k for k in K_COVER if bc[k] > 0]
        max_k_seen = max(nonzero_k) if nonzero_k else 0

 # high_k_samples: collect first HIGH_K_SAMPLE_LIMIT u's per k in HIGH_K_BUCKETS
        K_INDEX = {k: idx for idx, k in enumerate(K_COVER)}
        high_k_samples = {}
        for k in HIGH_K_BUCKETS:
            if bc[k] == 0:
                high_k_samples[k] = []
                continue
            hits = np.flatnonzero(first_k_np == k)[:HIGH_K_SAMPLE_LIMIT]
            taus = tau_matrix[hits, K_INDEX[k]]
            high_k_samples[k] = [
                {'u': int(hits[j]) + 1, 'tau': int(taus[j])}
                for j in range(len(hits))
            ]

        count_ge_6 = sum(by_k[k] for k in K_COVER if k >= 6)
        count_eq_8 = by_k.get(8, 0)
        results.append({
            'r': r,
            's_class': s_class,
            'U': U_BOUND,
            'B': B_sub,
            'survivor_count': len(survivors),
            'survivor_rate': len(survivors) / U_BOUND,
            'max_required_k': max_k_seen,
            'count_first_k_ge_6': count_ge_6,
            'count_first_k_eq_8': count_eq_8,
            'by_k': by_k,
            'high_k_samples': high_k_samples,
            'survivors_sample': survivors[:30],
        })

        elapsed = time.time() - t_sub
        if (i + 1) % 25 == 0 or i == 0:
            avg = (time.time() - grand_t0) / (i + 1)
            eta_min = avg * (len(targets) - i - 1) / 60.0
            print(f'  [{i+1}/{len(targets)}] r={r} s={s_class}  '
                  f'surv={len(survivors)} max_k={max_k_seen}  '
                  f'({elapsed:.2f}s; ETA {eta_min:.1f} min)',
                  file=sys.stderr)

    grand_elapsed = time.time() - grand_t0
    print(f'\nScan done in {grand_elapsed/60:.1f} min', file=sys.stderr)

    results.sort(key=lambda d: (
        d['survivor_count'], d['count_first_k_eq_8'],
        d['count_first_k_ge_6'], d['max_required_k'],
        -d['r'], -d['s_class'],
    ), reverse=True)

    total_u = len(results) * U_BOUND
    total_survivors = sum(r['survivor_count'] for r in results)
    n_zero = sum(1 for r in results if r['survivor_count'] == 0)
    by_max_k = {}
    for rec in results:
        by_max_k[rec['max_required_k']] = by_max_k.get(rec['max_required_k'], 0) + 1

    out = {
        'date': time.strftime('%Y-%m-%d'),
        'task': f'K={K_COVER} GPU AP-sieve breadth scan over OPEN mod-529 sub-APs',
        'parameters': {
            'A_CONST': A_CONST,
            'M_BASE': M_BASE, 'TWENTY_FIVE_TWENTY': TWENTY_FIVE_TWENTY,
            'SUBAP_MOD': SUBAP_MOD,
            'U_BOUND': U_BOUND,
            'K_COVER': K_COVER,
            'HIGH_K_BUCKETS': HIGH_K_BUCKETS,
            'HIGH_K_SAMPLE_LIMIT': HIGH_K_SAMPLE_LIMIT,
            'SMALL_PRIME_BOUND': SMALL_PRIME_BOUND,
            'SUB_AP_LIMIT': SUB_AP_LIMIT,
        },
        'manifest_summary': manifest['aggregate'],
        'aggregate': {
            'n_sub_aps_scanned': len(results),
            'total_u': total_u,
            'total_survivors': total_survivors,
            'overall_survivor_rate': total_survivors / total_u,
            'n_sub_aps_zero_survivors': n_zero,
            'by_max_k': by_max_k,
        },
        'results': results,
        'elapsed_seconds': grand_elapsed,
        'provenance': runtime_provenance(),
    }
    suffix = f'_U{U_BOUND}'
    if SUB_AP_LIMIT > 0:
        suffix += f'_limit{SUB_AP_LIMIT}'
    if K_COVER != [1, 2, 3, 4, 5, 6, 7, 8]:
        suffix += f'_Kmax{max(K_COVER)}'
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = OUT_DIR / f'cover_certificate_breadth_scan_gpu_sieve{suffix}.json'
    out_path.write_text(json.dumps(out, indent=2, default=str))
    try:
        rel = out_path.relative_to(REPO)
    except ValueError:
        rel = out_path
    print(f'Wrote {rel}', file=sys.stderr)


if __name__ == '__main__':
    main()
