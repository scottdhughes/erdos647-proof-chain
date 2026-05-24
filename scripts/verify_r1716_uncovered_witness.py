#!/usr/bin/env python3
"""Verify that r=1716 has explicit uncovered B≤1 witnesses.

At r ∈ {0, 4862, 16302, 17160} the B≤1 noncovering is proven by
measure sum < 1 (pigeonhole). At r=1716, measure sum is 1.14 > 1, so
the pigeonhole proof does not apply. We need explicit witnesses.

This script reads data/b_le1_uncovered_certificates.json and for each
candidate witness t at r=1716, independently checks:
  For every k ∈ [1, 100] \\ base_enriched(1716):
    compute the atlas branch λ(t) on which t lives at (r=1716, k).
    check B^eff_{r, k, λ(t)} ≥ 2 (i.e., not in the B≤1 automatic-fail
    layer).

If all sampled witnesses pass, the B≤1 noncovering claim at r=1716 is
established by explicit witness, not just by Monte Carlo.
"""

import json
from pathlib import Path

REPO = Path(__file__).parent.parent
M = 46189
A_CONST = 2520 * M

CORE_K = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24}
BASE_ENRICHED_1716 = CORE_K | {20, 15, 30}
PRIMES_P0 = [2, 3, 5, 7, 11, 13, 17, 19]
A_VAL = {2: 3, 3: 2, 5: 1, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1}


def v_p(n, p):
    if n == 0:
        return None
    n = abs(n); c = 0
    while n % p == 0:
        n //= p; c += 1
    return c


def b_eff_at(r, k, t):
    C = 2520 * r - k
    F = A_CONST * t + C
    if F == 0:
        return None
    S = []
    c_p = {}
    for p in PRIMES_P0:
        cp = v_p(C, p) if C != 0 else None
        c_p[p] = cp
        if cp is not None and cp >= A_VAL[p]:
            S.append(p)
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


def verify_witness(r, t):
    """Return (ok, min_B_eff, k_at_min) where ok = True iff t is uncovered by B≤1."""
    ban = BASE_ENRICHED_1716 if r == 1716 else set()
    min_B = 10**9
    min_k = None
    for k in range(1, 101):
        if k in ban:
            continue
        B = b_eff_at(r, k, t)
        if B is None:
            continue
        if B < min_B:
            min_B = B
            min_k = k
    return min_B > 1, min_B, min_k


def main():
    data = json.load(open(REPO / "data" / "b_le1_uncovered_certificates.json"))
    r1716 = data["residues"]["1716"]
    certs = r1716["escape_certificates"]
    print(f"Testing {len(certs)} claimed B≤1-uncovered witnesses at r=1716...")

    all_ok = True
    for i, c in enumerate(certs):
        t = c["t"]
        ok, min_B, min_k = verify_witness(1716, t)
        if not ok:
            all_ok = False
            print(f"  FAIL: witness t={t} has min B_eff={min_B} at k={min_k}")
            if i > 5:
                break
    if all_ok:
        print(f"PROVEN — all {len(certs)} witnesses at r=1716 are rigorously uncovered by B≤1.")
        # Print 3 sample witnesses for the paper
        print(f"\nSample witnesses (for paper citation):")
        for c in certs[:3]:
            t = c["t"]
            ok, min_B, min_k = verify_witness(1716, t)
            print(f"  t = {t}:")
            print(f"    min B^eff across k ∈ [1,100] \\ base_enriched(1716): {min_B} (at k={min_k})")
            print(f"    N = M·t + r = {M*t + 1716}")


if __name__ == "__main__":
    main()
