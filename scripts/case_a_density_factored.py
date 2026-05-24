#!/usr/bin/env python3
"""Refined case-A density model: empirically factored by per-k pass rates.

For each hard residue r, sample many t ∈ [T_lo, T_hi] and record:
  - per-k pass status: whether τ(2520N - k) ≤ k+2
  - the B^eff at each k for each t

Compute:
  - per-k empirical pass rate: p_{r, k}
  - per-B^eff pass rate conditional on B^eff: P(pass | B^eff = b, r, scale)
  - overall case-A pass rate (product heuristic under independence)

Compare the independence-product estimate to the empirical full-pass rate
(0/5000 per earlier scan). If the product is much smaller than 6e-4, we
have a first-principles lower bound on rarity. If it's larger, correlations
matter.

Output: data/case_a_density_factored.json
"""

import json
import random
from collections import Counter, defaultdict
from pathlib import Path

from sympy import factorint

REPO = Path(__file__).parent.parent
M = 46189
A_CONST = 2520 * M

CORE_K = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24}
BASE_ENRICHED = {
    0:    CORE_K | {20},
    1716: CORE_K | {20, 15, 30},
    4862: CORE_K | {20, 14},
    16302: CORE_K | {20, 30},
    17160: CORE_K | {20, 36, 28},
}
PRIMES_P0 = [2, 3, 5, 7, 11, 13, 17, 19]
A_VAL = {2: 3, 3: 2, 5: 1, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1}


def tau(n):
    if n <= 0: return 0
    if n == 1: return 1
    f = factorint(n)
    t = 1
    for e in f.values(): t *= (e + 1)
    return t


def v_p(n, p):
    if n == 0: return None
    n = abs(n); c = 0
    while n % p == 0:
        n //= p; c += 1
    return c


def compute_B_eff(r, k, t):
    C = 2520 * r - k
    F = A_CONST * t + C
    if F == 0: return None
    S = []; c_p = {}
    for p in PRIMES_P0:
        cp = v_p(C, p) if C != 0 else None
        c_p[p] = cp
        if cp is not None and cp >= A_VAL[p]: S.append(p)
    lam = {}
    for p in S:
        lam[p] = v_p(F, p) - A_VAL[p]
    T_fix_tau = 1
    for p in PRIMES_P0:
        if p not in S:
            cp = c_p[p] or 0
            T_fix_tau *= (cp + 1)
    active_factor = 1
    for p in S:
        active_factor *= (A_VAL[p] + lam[p] + 1)
    return (k + 2) // (T_fix_tau * active_factor)


def main():
    N_SAMPLE = 2000
    T_LO = 10**8
    T_HI = 10**9
    results = {"description": "Factored case-A density: per-k and per-B^eff empirical pass rates.",
               "t_range": [T_LO, T_HI], "n_sample": N_SAMPLE,
               "per_residue": {}}
    for r in (0, 1716, 4862, 16302, 17160):
        ban = BASE_ENRICHED[r]
        k_range = [k for k in range(1, 101) if k not in ban]
        random.seed(42 + r)
        # Per-k counts
        per_k_pass = Counter()
        per_k_sample = Counter()
        per_B_eff_pass = defaultdict(lambda: [0, 0])  # {B_eff: [pass, sample]}
        full_pass_count = 0
        for sample_idx in range(N_SAMPLE):
            t = random.randint(T_LO, T_HI)
            full_pass = True
            for k in k_range:
                N = M * t + r
                x = 2520 * N - k
                if x <= 0:
                    full_pass = False; continue
                tau_x = tau(x)
                passes = tau_x <= k + 2
                B_eff = compute_B_eff(r, k, t)
                per_k_sample[k] += 1
                per_B_eff_pass[B_eff][1] += 1
                if passes:
                    per_k_pass[k] += 1
                    per_B_eff_pass[B_eff][0] += 1
                else:
                    full_pass = False
            if full_pass:
                full_pass_count += 1

        per_k_rate = {k: (per_k_pass[k] / per_k_sample[k] if per_k_sample[k] else None)
                       for k in k_range}
        # Product estimate under independence
        from functools import reduce
        product_rate = reduce(lambda a, b: a * b, [per_k_rate[k] for k in k_range if per_k_rate[k] is not None], 1.0)
        per_B_eff_rate = {str(b): (v[0]/v[1] if v[1] else None, v[1]) for b, v in per_B_eff_pass.items()}

        # Tightest k's (lowest per-k pass rate)
        sorted_k = sorted(k_range, key=lambda k: per_k_rate[k] if per_k_rate[k] is not None else 1)
        bottleneck_ks = sorted_k[:10]

        results["per_residue"][str(r)] = {
            "n_sampled": N_SAMPLE,
            "full_case_a_pass_count": full_pass_count,
            "empirical_full_pass_rate": full_pass_count / N_SAMPLE,
            "independence_product_estimate": product_rate,
            "per_k_pass_rate_sample": {str(k): per_k_rate[k] for k in k_range[:20]},
            "bottleneck_ks_top10": [(k, per_k_rate[k]) for k in bottleneck_ks],
            "per_B_eff_rate": per_B_eff_rate,
        }
        print(f"\nr={r}:")
        print(f"  empirical full-pass rate: {full_pass_count}/{N_SAMPLE}")
        print(f"  independence-product estimate: {product_rate:.3g}")
        print(f"  per-B^eff rates: {dict((b, (round(r[0], 4), r[1])) for b, r in per_B_eff_rate.items() if r[0] is not None)}")
        print(f"  tightest 5 k (lowest pass rate): {bottleneck_ks[:5]}")
        for k in bottleneck_ks[:5]:
            print(f"    k={k}: {per_k_rate[k]:.3g}")

    with open(REPO / "data" / "case_a_density_factored.json", "w") as f:
        json.dump(results, f, indent=2, default=float)
    print(f"\nWrote data/case_a_density_factored.json")


if __name__ == "__main__":
    main()
