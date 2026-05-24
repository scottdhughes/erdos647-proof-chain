#!/usr/bin/env python3
"""B=2/B=3 shape-contradiction scan.

For each atlas branch (r, k, λ) with B^eff ∈ {2, 3}, compute the primitive
cofactor linear form Z(u) = α·u + β (as u ranges over the branch parameter)
and look for rigorous contradictions with the branch's shape requirement:

  * B^eff = 2: requires Z = 1 or Z prime.
    - If g := gcd(α, β) > 1 and g composite: Z always has a composite
      fixed factor → Z prime impossible → RIGOROUS BRANCH KILL.
    - If g prime: Z prime forces Z = g, i.e., (α/g)·u + (β/g) = 1,
      at most ONE u → branch has finitely many candidates (→ for large N,
      the branch is vacuous).
    - If g = 1: check for fixed-divisor obstructions at small primes q
      with q | α (then Z ≡ β mod q is fixed).

  * B^eff = 3: requires Z ∈ {1, prime, p²}.
    - g > 1 composite: same as B=2 — RIGOROUS kill (forces composite
      factor > 1 which is not the whole of Z for large u).
      More precisely: if g = p₁·p₂·... is a product of ≥2 primes (even with repetition),
      Z always has that product as a factor; Z can be p² only if Z = g
      exactly AND g = p² (and g | Z yields Z prime only if Z = g, g prime).
    - g prime: Z = g·(α'·u + β') with gcd(α', β') = 1. Z prime ⇒ Z = g
      and α'·u + β' = 1 (≤ 1 u). Z = p² ⇒ Z = g² iff g² | Z, which
      requires g | (α'·u + β'). Since gcd(α', β') = 1, this happens in one
      residue class of u. On that residue class, Z = g² = constant,
      again ≤ 1 u. So branch has ≤ 2 candidates.
    - g square of a prime p: Z = p²·(α'·u + β'). Z = p² ⇒ α'·u + β' = 1.
      Z prime: need Z ≠ p²·k for k > 1; but p² always divides Z.
      So branch has finitely many candidates.

The scan outputs, per residue:
  * count of B=2 branches total, rigorous-kill count (g > 1 composite),
    forced-g-prime count (≤ 1 candidate per branch), no-fixed-gcd count.
  * count of B=3 branches with the analogous categories.
  * list of rigorous-kill (r, k, λ) triples with the forced factor.

Output: data/b23_shape_contradictions.json
"""

import json
from collections import Counter, defaultdict
from math import gcd
from pathlib import Path

from sympy import factorint, isprime

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
    """t mod p^{lam_p} such that v_p(A·t + C) = a_p + lam_p exactly.
    Returns residue class of t; lam_p must be ≥ 0."""
    if lam_p == 0:
        # For λ_p = 0, no pinning at p — t ranges over all residues, but
        # the branch requires v_p(F) = a_p exactly, i.e., p | F/p^{a_p - 1}
        # and p ∤ F/p^{a_p}. We don't pin t in this case.
        return 0, 1  # placeholder residue with modulus 1
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
    """Enumerate atlas branches as in exact_tight_branches.py.

    Each branch record carries two quantities:
      T_fix_tau : product of (c_p + 1) over non-active primes (divisor count)
      fixed_content : product of p^{c_p} over non-active primes (actual integer)
    """
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
            "lambda": {},
            "B_eff": B,
            "active_primes": [],
            "T_fix_tau": T_fix_tau,
            "fixed_content": fixed_content,
        })
    else:
        def recurse(idx, partial):
            if idx == len(S):
                pfactor = 1
                for p in S:
                    pfactor *= (A_VAL[p] + partial[p] + 1)
                B = (k + 2) // (T_fix_tau * pfactor)
                branches.append({
                    "lambda": dict(partial),
                    "B_eff": B,
                    "active_primes": S,
                    "T_fix_tau": T_fix_tau,
                    "fixed_content": fixed_content,
                })
                return
            p = S[idx]
            for v in range(max_lambda + 1):
                partial[p] = v
                recurse(idx + 1, partial)
                del partial[p]
        recurse(0, {})
    return branches, S, c_p


def compute_Z_linear_form(r, k, branch, S, c_p):
    """Given a branch (r, k, λ), compute the primitive cofactor Z as a
    linear form α·u + β where u parameterizes t within the branch.

    Parameterization: t pinned to t_0 mod Q, where Q = ∏_{p ∈ S} p^{λ_p}
    (the "pinning" modulus — we don't include the +1 to stay on the exact-λ
    class; we treat t = t_0 + u·Q, acknowledging that u will occasionally
    jump to a higher valuation, but this is a measure-zero event).

    Z = F(t) / A_fixed where A_fixed = T_fix · ∏_{p ∈ S} p^{a_p + λ_p}.

    Returns (alpha, beta, Q) or None if the branch has no valid t_0.
    """
    lam = branch["lambda"]
    # Compute t_0: unique solution mod Q of the CRT system.
    crt_mod = 1
    crt_residue = 0
    valid = True
    Q_pin = 1
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
        # CRT combine
        inv = mod_inv(crt_mod, p_mod)
        if inv is None:
            # gcd(crt_mod, p_mod) > 1 — shouldn't happen with distinct primes
            valid = False
            break
        diff = (t_p - crt_residue) % p_mod
        k_val = (inv * diff) % p_mod
        crt_residue = crt_residue + crt_mod * k_val
        crt_mod = crt_mod * p_mod
        Q_pin *= p_mod
    if not valid:
        return None

    A_fixed = branch["fixed_content"]
    for p in S:
        lam_p = lam.get(p, 0)
        A_fixed *= p ** (A_VAL[p] + lam_p)

    # Z(u) = (A_CONST·(t_0 + u·Q_pin) + C) / A_fixed
    # For this to be integer at all u, need A_fixed | (A_CONST·t_0 + C) and A_fixed | A_CONST·Q_pin.
    # The first holds by construction (t_0 is the pinned residue).
    # The second: A_CONST·Q_pin / A_fixed should be integer.
    C = 2520 * r - k
    numerator_0 = A_CONST * crt_residue + C
    if numerator_0 % A_fixed != 0:
        # Shouldn't happen — sanity check
        return None
    beta = numerator_0 // A_fixed
    num_slope = A_CONST * Q_pin
    if num_slope % A_fixed != 0:
        return None
    alpha = num_slope // A_fixed
    return alpha, beta, Q_pin, crt_residue, A_fixed


def qnr_primes_dividing_alpha(alpha, beta):
    """Return list of (q, is_qr) for each prime q | α: is_qr = (β is QR mod q).
    For q=2: treat as a special case (every nonzero residue is a square mod 2).
    For odd prime q: β nonzero mod q (since gcd(α,β)=1); β QR iff legendre = 1.
    """
    from sympy import legendre_symbol
    if alpha == 0:
        return []
    q_powers = factorint(alpha)
    out = []
    for q in q_powers:
        if q == 2:
            # β odd (since gcd(α, β) = 1 and 2 | α ⇒ 2 ∤ β). Odd β ≡ 1 (mod 2),
            # and 1 is a square mod 2 trivially. But mod 4 matters: squares mod 4 ∈ {0, 1}.
            # If 4 | α, then Z ≡ β mod 4. β odd ⇒ β ≡ 1 or 3 mod 4.
            # For Z = p², p must be odd (since 2 ∤ Z), so p² ≡ 1 mod 4 (or mod 8).
            # So if β ≡ 3 mod 4, Z ≠ p² for any u.
            # Check mod 4 and mod 8 if 4 | α.
            if alpha % 4 == 0:
                mod4 = beta % 4
                out.append((2, mod4 in (0, 1), {"mod_4": mod4}))
            else:
                # Just q=2: β ≡ 1 (mod 2), always QR mod 2 trivially.
                out.append((2, True, None))
            continue
        # Odd prime q
        ls = legendre_symbol(beta, q)
        out.append((q, ls == 1, {"legendre": ls}))
    return out


def classify_b23_branch(alpha, beta, B_eff):
    """Classify the branch's shape-contradiction status."""
    g = gcd(alpha, beta)
    if g == 0:
        return "Z_zero", {"g": 0}
    qnr_info = qnr_primes_dividing_alpha(alpha, beta)
    # Identify QNR primes q | α that exclude Z = p²
    qnr_excluders = [(q, detail) for (q, is_qr, detail) in qnr_info if not is_qr]

    if g == 1:
        if B_eff == 2:
            # B=2 requires Z prime. Z ≡ β mod q for q | α (with q ∤ β).
            # This never blocks Z prime. No rigorous kill from this analysis.
            return "B2_no_rigorous_kill", {
                "g": 1, "alpha": alpha, "beta": beta,
                "qnr_primes": [q for q, _, _ in qnr_info if not _],
            }
        # B=3: requires Z ∈ {prime, p²}. If any q | α has β QNR mod q (or q=2 has β ≡ 3 mod 4),
        # then Z = p² is impossible → the branch reduces to "Z prime" (B=2-tightness).
        if qnr_excluders:
            return "B3_p2_excluded", {
                "g": 1, "alpha": alpha, "beta": beta,
                "qnr_excluders": [q for q, _ in qnr_excluders],
            }
        # No QNR exclusion: Z can still be p² in principle.
        return "B3_no_rigorous_kill", {
            "g": 1, "alpha": alpha, "beta": beta,
        }
    # g > 1
    g_factors = factorint(g)
    total_prime_factors = sum(g_factors.values())
    distinct = len(g_factors)
    if total_prime_factors == 1:
        return "g_prime_finite", {
            "g": g,
            "alpha_reduced": alpha // g,
            "beta_reduced": beta // g,
        }
    # g composite
    if B_eff == 2:
        return "rigorous_kill_B2", {"g": g, "g_factorization": {str(p): e for p, e in g_factors.items()}}
    if total_prime_factors == 2 and distinct == 1:
        p, _ = next(iter(g_factors.items()))
        return "g_prime_square_finite", {"g": g, "p": p}
    return "rigorous_kill_B3", {"g": g, "g_factorization": {str(p): e for p, e in g_factors.items()}}


def main():
    results = {
        "description": "B=2/B=3 shape-contradiction scan",
        "residues": {},
    }
    global_counter = Counter()
    for r in (0, 1716, 4862, 16302, 17160):
        ban = BASE_ENRICHED[r]
        r_counter = Counter()
        rigorous_kills = []
        g_prime_finite = []
        for k in range(1, 101):
            if k in ban:
                continue
            branches, S, c_p = enumerate_branches_for_rk(r, k, max_lambda=6)
            for b in branches:
                if b["B_eff"] not in (2, 3):
                    continue
                z_info = compute_Z_linear_form(r, k, b, S, c_p)
                if z_info is None:
                    r_counter["compute_err"] += 1
                    continue
                alpha, beta, Q, t_0, A_fixed = z_info
                status, detail = classify_b23_branch(alpha, beta, b["B_eff"])
                r_counter[f"B{b['B_eff']}_{status}"] += 1
                global_counter[f"B{b['B_eff']}_{status}"] += 1
                if status in ("rigorous_kill_B2", "rigorous_kill_B3"):
                    rigorous_kills.append({
                        "r": r, "k": k, "B_eff": b["B_eff"],
                        "lambda": {int(p): v for p, v in b["lambda"].items()},
                        "alpha": alpha, "beta": beta,
                        "g": detail["g"],
                        "g_factorization": detail.get("g_factorization"),
                    })
                elif status in ("g_prime_finite", "g_prime_square_finite"):
                    g_prime_finite.append({
                        "r": r, "k": k, "B_eff": b["B_eff"],
                        "lambda": {int(p): v for p, v in b["lambda"].items()},
                        "alpha": alpha, "beta": beta,
                        "g": detail["g"],
                    })
                elif status == "B3_p2_excluded":
                    r_counter["B3_p2_excluded_detail"] = r_counter.get("B3_p2_excluded_detail", 0) + 1
        # Totals
        total_B2 = sum(v for key, v in r_counter.items() if key.startswith("B2_"))
        total_B3 = sum(v for key, v in r_counter.items() if key.startswith("B3_"))
        results["residues"][str(r)] = {
            "counts": dict(r_counter),
            "total_B2": total_B2,
            "total_B3": total_B3,
            "rigorous_kills": rigorous_kills,
            "g_prime_finite": g_prime_finite[:50],  # only first 50 per residue
            "g_prime_finite_count": len(g_prime_finite),
        }
        print(f"r={r}: total B=2={total_B2}, B=3={total_B3}")
        for key in sorted(r_counter):
            print(f"    {key}: {r_counter[key]}")

    results["global"] = dict(global_counter)
    with open(REPO / "data" / "b23_shape_contradictions.json", "w") as f:
        json.dump(results, f, indent=2, default=int)
    print(f"\nGlobal: {dict(global_counter)}")
    print(f"Wrote data/b23_shape_contradictions.json")


if __name__ == "__main__":
    main()
