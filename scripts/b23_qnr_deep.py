#!/usr/bin/env python3
"""Deeper scan of the B=3 QNR-collapse theorem: extend to k ≤ 1000, record
which prime q is the QNR excluder at each branch, and look for patterns.

If there's a structural reason why β is always QNR mod q for some q | α,
we should be able to identify the responsible prime.

Output: data/b23_qnr_deep.json
"""

import json
from collections import Counter, defaultdict
from math import gcd
from pathlib import Path

from sympy import factorint, isprime, legendre_symbol

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
K_MAX = 1000


def v_p(n, p):
    if n == 0:
        return None
    n = abs(n)
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def extended_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def mod_inv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    return x % m if g == 1 else None


def hensel_root(r, k, p, lam_p):
    if lam_p == 0:
        return 0, 1
    C = 2520 * r - k
    ap = A_VAL[p]
    pap = p ** ap
    if A_CONST % pap != 0 or C % pap != 0:
        return None
    A_red = A_CONST // pap
    C_red = C // pap
    mod = p ** lam_p
    A_red_mod = A_red % mod
    inv = mod_inv(A_red_mod, mod)
    if inv is None:
        return None
    return (-C_red * inv) % mod, mod


def enumerate_branches_for_rk(r, k, max_lambda=6):
    C = 2520 * r - k
    S = []
    c_p = {}
    for p in PRIMES_P0:
        cp = v_p(C, p) if C != 0 else None
        c_p[p] = cp
        if cp is not None and cp >= A_VAL[p]:
            S.append(p)
    T_fix_tau = 1
    fixed_content = 1
    for p in PRIMES_P0:
        if p not in S:
            cp = c_p[p] or 0
            T_fix_tau *= (cp + 1)
            fixed_content *= p ** cp
    branches = []
    if not S:
        B = (k + 2) // T_fix_tau
        branches.append({
            "lambda": {}, "B_eff": B, "active_primes": [],
            "T_fix_tau": T_fix_tau, "fixed_content": fixed_content,
        })
    else:
        def recurse(idx, partial):
            if idx == len(S):
                pfactor = 1
                for p in S:
                    pfactor *= (A_VAL[p] + partial[p] + 1)
                B = (k + 2) // (T_fix_tau * pfactor)
                branches.append({
                    "lambda": dict(partial), "B_eff": B, "active_primes": S,
                    "T_fix_tau": T_fix_tau, "fixed_content": fixed_content,
                })
                return
            p = S[idx]
            for v in range(max_lambda + 1):
                partial[p] = v
                recurse(idx + 1, partial)
                del partial[p]
        recurse(0, {})
    return branches, S, c_p


def compute_alpha_beta(r, k, branch, S):
    lam = branch["lambda"]
    crt_mod = 1
    crt_residue = 0
    Q_pin = 1
    valid = True
    for p, lam_p in lam.items():
        if lam_p == 0:
            continue
        result = hensel_root(r, k, p, lam_p)
        if result is None:
            valid = False
            break
        t_p, p_mod = result
        if p_mod == 1:
            continue
        inv = mod_inv(crt_mod, p_mod)
        if inv is None:
            valid = False
            break
        diff = (t_p - crt_residue) % p_mod
        k_val = (inv * diff) % p_mod
        crt_residue = crt_residue + crt_mod * k_val
        crt_mod *= p_mod
        Q_pin *= p_mod
    if not valid:
        return None
    A_fixed = branch["fixed_content"]
    for p in S:
        lam_p = lam.get(p, 0)
        A_fixed *= p ** (A_VAL[p] + lam_p)
    C = 2520 * r - k
    numerator_0 = A_CONST * crt_residue + C
    if numerator_0 % A_fixed != 0:
        return None
    beta = numerator_0 // A_fixed
    num_slope = A_CONST * Q_pin
    if num_slope % A_fixed != 0:
        return None
    alpha = num_slope // A_fixed
    return alpha, beta


def find_qnr_excluders(alpha, beta):
    """Return list of primes q | α where β is a non-square mod q (thus p² impossible)."""
    if alpha == 0:
        return []
    q_powers = factorint(alpha)
    excluders = []
    for q, e in q_powers.items():
        if q == 2:
            # mod-4 / mod-8 analysis for p²: p odd ⇒ p² ≡ 1 mod 4 (in fact mod 8).
            if e >= 3:
                # 8 | α, so Z ≡ β (mod 8). Z = p² requires β ≡ 1 mod 8.
                if beta % 8 != 1:
                    excluders.append(("2", 8, beta % 8))
            elif e >= 2:
                if beta % 4 != 1:
                    excluders.append(("2", 4, beta % 4))
            # else: 2 | α but 4 ∤ α → β odd ≡ 1 mod 2, no obstruction
            continue
        # Odd prime q: β nonzero mod q (gcd(α, β) = 1 by atlas primitivity)
        ls = legendre_symbol(beta, q)
        if ls != 1:
            excluders.append((str(q), int(q), int(ls)))
    return excluders


def main():
    results = {"description": "Deeper B=3 QNR scan to k ≤ 1000", "k_max": K_MAX,
               "residues": {}}
    total_B3 = 0
    total_B3_with_excluder = 0
    excluder_q_counter = Counter()
    first_excluder_counter = Counter()
    problematic_branches = []  # B=3 branches with NO QNR excluder (if any)
    for r in (0, 1716, 4862, 16302, 17160):
        ban = BASE_ENRICHED[r]
        r_B3 = 0
        r_with_excluder = 0
        r_excluder_q = Counter()
        r_first_q = Counter()
        for k in range(1, K_MAX + 1):
            if k in ban:
                continue
            branches, S, c_p = enumerate_branches_for_rk(r, k, max_lambda=6)
            for b in branches:
                if b["B_eff"] != 3:
                    continue
                ab = compute_alpha_beta(r, k, b, S)
                if ab is None:
                    continue
                alpha, beta = ab
                excluders = find_qnr_excluders(alpha, beta)
                r_B3 += 1
                total_B3 += 1
                if excluders:
                    r_with_excluder += 1
                    total_B3_with_excluder += 1
                    for (q_label, _, _) in excluders:
                        r_excluder_q[q_label] += 1
                        excluder_q_counter[q_label] += 1
                    first_q = excluders[0][0]
                    r_first_q[first_q] += 1
                    first_excluder_counter[first_q] += 1
                else:
                    problematic_branches.append({
                        "r": r, "k": k, "B_eff": 3,
                        "lambda": {int(p): v for p, v in b["lambda"].items()},
                        "alpha": alpha, "beta": beta,
                    })
        results["residues"][str(r)] = {
            "B3_branches": r_B3,
            "B3_with_qnr_excluder": r_with_excluder,
            "qnr_coverage_pct": 100 * r_with_excluder / r_B3 if r_B3 else None,
            "excluder_q_counts": dict(r_excluder_q),
            "first_excluder_counts": dict(r_first_q),
        }
        print(f"r={r}: B=3 branches {r_B3}, with QNR excluder {r_with_excluder} "
              f"({100*r_with_excluder/r_B3:.2f}% if r_B3 else '0%)")
        print(f"  excluder q (any): {dict(r_excluder_q.most_common(5))}")
        print(f"  first q: {dict(r_first_q.most_common(5))}")
    results["global"] = {
        "total_B3": total_B3,
        "total_B3_with_qnr_excluder": total_B3_with_excluder,
        "qnr_coverage_pct": 100 * total_B3_with_excluder / total_B3 if total_B3 else None,
        "excluder_q_counts": dict(excluder_q_counter),
        "first_excluder_counts": dict(first_excluder_counter),
        "problematic_count": len(problematic_branches),
        "problematic_branches": problematic_branches,
    }
    with open(REPO / "data" / "b23_qnr_deep.json", "w") as f:
        json.dump(results, f, indent=2, default=int)
    print(f"\nGlobal: {total_B3_with_excluder}/{total_B3} B=3 branches "
          f"have QNR excluder ({100*total_B3_with_excluder/total_B3:.4f}%)")
    print(f"Problematic branches (no QNR excluder): {len(problematic_branches)}")
    print(f"First-excluder q distribution: {dict(first_excluder_counter.most_common())}")
    print(f"Any-excluder q distribution: {dict(excluder_q_counter.most_common())}")


if __name__ == "__main__":
    main()
