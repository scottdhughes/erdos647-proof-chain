# A finite-range cover certificate for Erdős Problem #647

**S. D. Hughes**

A machine-checkable certificate that **Erdős Problem #647 has no solution `n` in
the range `24 < n ≤ N₀`**, where

```
  N₀ = A · 10⁷ = 615 736 321 200 000 000  ≈  6.157 × 10¹⁷,
  A  = 2520 · 46189 · 529 = 61 573 632 120,
```

It ships with a **dependency-free verifier** (`verify.py`, Python standard
library only) that re-checks the certificate end-to-end on a laptop in seconds:
SHA-256 integrity, the residue/sub-AP partition, the aggregates, the `u = 0` row,
the closure expansion, and an independent re-factoring of the adversarial and
sampled cells. The reduction to the 41 residues of §2 is in this repository's
root `lean/` development; everything else needed to check the certificate is
included in this directory.

This is a **density-zero / finite-range** result. **It is not a resolution of
#647** and makes no claim about `n > N₀`.

## 1. The problem

Erdős Problem #647 (Erdős–Selfridge) asks whether there exists `n > 24` with

```
        max_{1 ≤ m < n} ( m + τ(m) )  ≤  n + 2,
```

equivalently (Bloom) `τ(n − k) ≤ k + 2` for every `1 ≤ k < n`, where `τ` is the
number-of-divisors function. The known solution set is
`{1, 2, 3, 4, 5, 6, 8, 10, 12, 24}`; whether any `n > 24` exists is **open**.

## 2. The search space (a Lean-verified reduction)

A candidate `n > 24` is forced into a thin set, in three Lean-verified steps,
established in this repository's root `lean/` (`Erdos647ReductionChain.lean`,
`Erdos647ResiduePartitionStage1.lean`, `Erdos647SingleOverlapClosure.lean`,
`Erdos647DirectFullValueClosure.lean`, `Erdos647Main.lean`):

1. **Layer A.** For `25 ≤ n ≤ 84` the condition fails by bounded decision.
2. **Modular reduction.** Any candidate `n > 84` has `n = 2520 N` with `N mod M`
   in one of **96** admissible classes, `M = 46189 = 11·13·17·19`.
3. **Closure.** **55** of the 96 classes are eliminated (42 single-overlap + 13
   direct full-value), leaving **41 open residue classes** (the complement,
   itself a theorem).

This certificate covers exactly those **41 open residues**, over `n ≤ N₀`. It is
**finite-range evidence for** the statement "the 41 open residues contain no
solution" — it does **not** assume that statement; the reduction in steps 1–3 is
proved independently of it, so there is no circularity.

## 3. Enumeration and the clean 21,689-pair partition

Write `N = M·(529u + s) + r` with `r = N mod M` (one of the 41 open residues),
`s ∈ {0,…,528}`, `u ≥ 0`. Then the candidate value and its shifts are

```
  n = 2520 N = A·u + B_sub,     F_k(u) = n − k = A·u + (B_sub − k),
  B_sub = 2520·(M·s + r),       A = 2520·M·529 = 2³·3²·5·7·11·13·17·19·23².
```

Two facts make the height bound exact (both re-checked by `verify.py` against all
15 140 records): `B_sub = 2520·(M·s + r)` holds identically, and
`0 ≤ B_sub < A` always (since `M·s + r ≤ M·528 + (M−1) < M·529`). Consequently
**every candidate with `n ≤ N₀ = A·10⁷` has `u ∈ {0, 1, …, 10⁷}`** (from
`u = (n − B_sub)/A` with `0 ≤ B_sub < A`). Combined with the partition below,
each such candidate lies in either a closed pair (killed for *all* `u` by a Lean
theorem) or an open pair, where `u ∈ {1,…,10⁷}` is covered by the GPU scan (§4)
and `u = 0` is covered directly by `verify.py` (the `u = 0` candidate `n = B_sub`
is either `≤ 84` — across all 15 140 open sub-APs the only such case is the
noncandidate `n = 0`, the general `≤ 84` range falling to Layer A — or killed by
some `k ≤ 16`). So there is no gap up to `N₀`.

The 41 open residues, refined modulo 529, give the disjoint partition

```
  41 × 529  =  21 689   (residue, sub-AP) pairs
            =  6 549  closed by Lean theorems   ⊔   15 140  scanned directly.
```

- **6 549 pairs are killed unconditionally by Lean theorems** — the
  `hensel_rootline_closure` lemma (`lean/Erdos647V23HenselCore.lean`). For such a
  pair there is a fixed shift `k`, a divisor `d`, and an identity
  `2520·(A'·s + b) − k = d·(α·s + c₀)` holding **for every `s`**, with `c₀ ≥ 2`
  and `τ(d·p) > k + 2` for every prime `p`. The cofactor `α·s + c₀ ≥ 2` always
  contributes a prime, forcing `τ(F_k) ≥ τ(d·p) > k + 2` for **all** `s` — a
  universal-in-`s` kill, strictly stronger than any finite search. (The 631
  generated theorems expand to 6 549 pairs: 269 mod-23 theorems × 23 + 362
  mod-529 theorems; "…RootlinePartial" denotes a `1/23` or `1/529` density slice,
  not a partial or heuristic argument. The closure shift `k` may exceed 16; that
  is fine — any `k < n` with `τ(F_k) > k+2` disqualifies `n`. The manifest also
  lists a `V23All96` provenance source, which is redundant: `verify.py`
  reproduces all 6 549 closed pairs from the shipped mod-23 and mod-529 closures
  alone.)
- **15 140 pairs are scanned cell-by-cell** for `u ∈ {1,…,10⁷}` (next section).

## 4. The scan (exact divisor counts via an AP sieve)

`scripts/cover_certificate_breadth_scan_gpu_sieve.py` (GPU, CuPy/CUDA) computes
`τ(F_k(u))` **exactly** for every `(u, k)`, `u ∈ {1,…,10⁷}`, `k ∈ {1,…,16}`
(the `u = 0` row is certified separately by `verify.py`, see §3 and §6):

- **Forced part.** The nine primes dividing `A` (`{2,3,5,7,11,13,17,19,23}`) are
  removed by explicit `p`-adic peeling.
- **Sieve part.** For each prime `p ≤ B` coprime to `A`,
  `F_k(u) ≡ 0 (mod p) ⇔ u ≡ u₀(k,p) (mod p)`; the kernel marks the progression
  and extracts the exact `p`-adic valuation at each mark.
- **Exactness invariant.** The sieve bound `B = 784 688 718` satisfies
  `B² = 615 736 384 156 483 524`, which exceeds the *largest value the scan ever
  factors*, `F₁(10⁷) = A·10⁷ + max B_sub − 1 = 615 736 382 768 587 079`
  (margin `1 387 896 445`); so `B² > F_k(u)` for every scanned `(u,k)`. Let `c`
  be the residual cofactor after dividing `F_k(u)` by all primes `≤ B`. If `c`
  were composite its least prime factor would exceed `B`, so `c ≥ (B+1)² > B² >
  F_k(u) ≥ c`, a contradiction; hence `c` is `1` or a single prime, contributing
  exactly `1` or `2` to `τ`. Every reported `τ(F_k(u))` is therefore **exact** —
  both "kill" and "survivor" verdicts are genuine. (`verify.py` checks
  `B² > A·10⁷ + max B_sub` against the actual records.)

A cell is **killed** at the first `k` with `τ(F_k(u)) > k + 2`; `n` could be a
#647 solution only if *no* `k ≤ 16` kills it (a kill at any single `k`
disqualifies `n`, since it violates `τ(n−k) ≤ k+2`).

## 5. Result

Merged scan over all **15 140** open sub-APs (`u ∈ {1,…,10⁷}`, `K = {1,…,16}`):

| Quantity | Value |
|---|---|
| Cells examined (`u = 1…10⁷`) | **151 400 000 000** (1.514 × 10¹¹) |
| **Survivors** | **0** |
| Cells with no killing `k ≤ 16` | **0** |
| Largest shift ever required | **16**, attained by **exactly one** sub-AP |

The `u = 0` row (one candidate per open sub-AP) is certified separately by
`verify.py`: of the 15 140, one is `n = 0` (not a candidate) and the rest are
each killed by some `k ≤ 9`.

Distribution of the largest first-kill shift per sub-AP (`by_max_required_k`):
`{1:861, 5:770, 7:27, 8:1179, 9:5656, 10:5389, 11:772, 12:401, 13:56, 14:23,
15:5, 16:1}`. The cover `K ≤ 16` is **exactly tight**: one sub-AP
(`r = 5291, s = 357`, at `u = 304 936`) survives `k = 1,…,15` and is killed only
at `k = 16` with `τ(F₁₆) = 320`.

Combining the three Lean-verified steps of §2 with this scan, the `u = 0` row,
and the §3 closures: Layer A handles `24 < n ≤ 84`; every candidate with
`84 < n ≤ N₀` lies in a closed pair (killed for all `u` by a Lean theorem) or an
open pair (killed at `u = 0` by `verify.py`, at `u = 1…10⁷` by the scan). Hence
**no `n` with `24 < n ≤ N₀ = 6.1573632120 × 10¹⁷` satisfies #647.**

**Partial deeper probe.** A subset of **336** sub-APs (of 15 140) was additionally
pushed to `U = 10⁸` (`≈ 6.16 × 10¹⁸`), a further `3.35 × 10¹⁰` cells, again with
**0 survivors**. This is *not* a complete frontier at `10⁸` and is reported only
as corroboration; the certified bound is `N₀`.

## 6. Independent verification (`verify.py`)

`verify.py` uses **only the Python standard library** — its own
Miller-Rabin + Pollard-rho factorizer, a code path entirely separate from the GPU
sieve:

```
$ python3 verify.py
...
RESULT: 30 passed, 0 failed
ALL CHECKS PASSED — certificate independently verified.
```

It checks: (0) **integrity** — SHA-256 of every shipped file matches
`SHA256SUMS` (and that the manifest lists every shipped file); (1) the constants
and the exactness invariant `B² > A·10⁷ + max B_sub`; (2) the
parametrization `B_sub = 2520·(M·s + r)` with `0 ≤ B_sub < A` on all records (the
no-gap fact of §3), and the partition `6549 ⊔ 15140 = 21689 = 41·529` (disjoint,
scanned set = manifest open set, residues = the Lean open set); (3) the
aggregates from the raw 15 140 records (`Σ survivors = 0`, every `u` accounted for
via `Σ by_k = 10⁷` per record, `1.514×10¹¹` cells, the full `by_max_required_k`
histogram, cover tight at 16); (4) **independent re-factoring** — all
`max_required_k ≥ 13` cells with full first-kill chains, thousands of sampled
high-`k` cells (each stored `τ` confirmed exact, each kill genuine), the entire
`u = 0` row from scratch, and a contiguous from-scratch re-scan of three full
sub-APs (anti-fabrication: independently reproduces "0 survivors" on full
`u`-blocks); (5) the 631 Lean closures' arithmetic
(`2520·A' = d·α`, `2520·b − k = d·c₀`, `c₀ ≥ 2`, `min_p τ(d·p) > k + 2`) **and**
their expansion to exactly the manifest's 6 549 closed pairs (so the two data
files cannot drift apart unnoticed). Runtime ≈ 5 s; `--full` re-factors every
sampled cell, `--rescan N` widens the contiguous re-scan.

**Scope (stated plainly).** `verify.py` re-checks the certificate's structure,
integrity, and arithmetic, re-derives the aggregates from the raw per-sub-AP
records, and re-factors the `u = 0` row, the adversarial/high-`k` cells, and
contiguous `u`-blocks **from scratch**. It does *not* re-run the full
`1.514×10¹¹`-cell sweep — that (the per-record `by_k` histograms for all `10⁷`
values of `u`) is reproduced only by the GPU scan in `scripts/`; the verifier
confirms those histograms are internally consistent and correct on every cell it
re-factors.

## 7. Contents

```
README.md                     this note
verify.py                     dependency-free independent verifier (stdlib only)
data/
  cover_certificate_U1e7_Kmax16.json.gz   merged per-sub-AP scan output (15140 records)
  open_subap_manifest.json                the 21689-pair partition (6549 closed ⊔ 15140 open)
  closures_params.json                    parameters of the 631 Lean closure theorems
scripts/
  cover_certificate_breadth_scan_gpu_sieve.py   the GPU AP-sieve scan
  runpod_breadth_scan_launcher.py               shard orchestration
lean/
  Erdos647V23HenselCore.lean              the hensel_rootline_closure lemma
  Mod23RootlinePartial.lean               269 closure theorems
  Mod529RootlinePartial.lean              362 closure theorems
SHA256SUMS                    integrity manifest
LICENSE                       Apache-2.0
```

The `lean/` files are from the full #647 Lean development (where they compile —
`Erdos647V23HenselCore` imports `Erdos647QuotientCover`, which is *not* part of
this repository); they are included here **for inspection only** and are not
built by this repo's `lake` target. Their arithmetic content is re-checked
independently by `verify.py` via `closures_params.json`, so the certificate is
fully checkable without a Lean toolchain. (Source paths recorded inside
`open_subap_manifest.json` are relative to the original development tree, and one
listed source, `V23All96.lean`, is external and redundant — `verify.py`
reproduces all 6 549 closed pairs from the shipped `Mod23`/`Mod529` closures
alone.)

## 8. Provenance

- Scan hardware: NVIDIA H100 80 GB HBM3; CuPy 14.0.1; Python 3.11.10; Linux.
- Run date 2026-04-29; 8 shards merged; ≈ 2 300 s per shard; per-shard SHA-256
  manifests with `checksum_mismatch_count = 0`, postprocess `integrity_status =
  PASS`.
- A `u ≤ 100` subset of these certificates is independently re-verified by the
  Lean kernel (`TailKillUpTo` slice modules, `native_decide`), giving a
  machine-checked core of the computational scan.

## 9. What is and is not claimed

- **Claimed (unconditional):** no #647 solution with
  `24 < n ≤ N₀ = 6.1573632120 × 10¹⁷`; every candidate eliminated by an explicit
  `k ≤ 16` (scanned pairs and the `u = 0` row) or a Lean congruence theorem
  (closed pairs), with exact divisor counts; the shift cover `K ≤ 16` is tight on
  this window.
- **Not claimed:** anything about `n > N₀`; finiteness of the solution set; any
  resolution of #647. The obstruction to finiteness is the prime-tuples /
  Schinzel-Hypothesis-H barrier, not the height of this search.

## 10. Reproducing the scan

Requires CUDA GPUs with CuPy. The launcher exposes `shard` / `merge` / `multigpu`
subcommands; the full run is, e.g.

```
python3 scripts/runpod_breadth_scan_launcher.py multigpu \
    --u-bound 10000000 \
    --k-cover 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 \
    --manifest-path data/open_subap_manifest.json
```

which launches one `cover_certificate_breadth_scan_gpu_sieve.py` shard per GPU and
merges them. (The shipped launcher writes under its configured output directory;
the merged result is the `cover_certificate_…_merged_…json` reproduced here as
`data/cover_certificate_U1e7_Kmax16.json.gz`.) Key parameters:
`A_CONST = 61573632120`, `M_BASE = 46189`, `SUBAP_MOD = 529`,
`U_BOUND = 10000000`, `K_COVER = 1..16`, `SMALL_PRIME_BOUND = 784688718`.
