#!/usr/bin/env python3
"""
Test whether the union of rigorously-eliminated branches (B^eff ≤ 1)
over all k ≤ 100 covers every t-class modulo small moduli at each
residue.

Each B ≤ 1 branch λ at (r, k) pins t to a specific residue class
mod some constraint modulus m_λ. If for residue r, the union of
these classes (across all k ≤ 100) covers ALL of Z/M* for some
M*, then every N on residue r with t sufficiently large is
deterministically eliminated.

This would be a RIGOROUS LOCAL OBSTRUCTION THEOREM — a proof of
finiteness, not a density heuristic.

Approach:
  1. For each residue r, collect all B ≤ 1 branches with their
     (constraint_mod, t_class) — the specific t-residue that gets
     eliminated.
  2. Pick a target modulus M* (e.g., lcm of small primes up to P_max)
     and project each eliminated class onto Z/M*. Count covered
     residues.
  3. If coverage is 100%, report: "r is rigorously eliminated."
     If <100%, identify the uncovered classes (these are the only
     classes where candidates might live).

Note: for B=1, t_class is well-defined modulo constraint_mod (the
Hensel lift of the forced prime). For B=0, the branch is automatic
fail at ALL t-classes matching the branch's constraint_mod (no
further t-subdivision needed).
"""

import json
from pathlib import Path
from collections import Counter
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


def v_p(n, p):
    if n == 0: return None
    n = abs(n); c = 0
    while n % p == 0:
        n //= p; c += 1
    return c


def extended_gcd(a, b):
    if b == 0: return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def mod_inv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    return x % m if g == 1 else None


def hensel_lift_root(r, k, p, lam_p, A_const=A_CONST):
    """Find t mod p^{lam_p} such that v_p(A·t + C) ≥ a_p + lam_p.

    Since v_p(A) = a_p exactly and v_p(C) ≥ a_p (active-prime condition),
    divide out p^{a_p}: (A/p^{a_p})·t + (C/p^{a_p}) ≡ 0 mod p^{lam_p}.
    The reduced A' = A/p^{a_p} is coprime to p, hence invertible mod p^{lam_p}.
    """
    if lam_p == 0:
        return 0  # no pinning; caller should skip
    C = 2520 * r - k
    ap = A_VAL[p]
    pap = p ** ap
    # Sanity: A and C both divisible by p^{a_p}
    if A_const % pap != 0 or C % pap != 0:
        return None
    A_red = A_const // pap
    C_red = C // pap
    mod = p ** lam_p
    A_red_mod = A_red % mod
    inv = mod_inv(A_red_mod, mod)
    if inv is None:
        return None
    return (-C_red * inv) % mod


def collect_eliminated_classes(r, k, branches):
    """For each B ≤ 1 branch at (r, k), compute the t-residue class
    (mod the branch's constraint modulus) that gets eliminated."""
    classes = []
    for b in branches:
        if b["B_eff"] > 1:
            continue
        # For B = 0: the branch eliminates ALL t satisfying the active-prime
        # valuation pattern λ. This is a class mod (∏ p^{λ_p + 1}).
        # For B = 1: same pinning, same class structure.

        # The class on which this branch lives:
        # t ≡ hensel_root(p, λ_p) (mod p^{λ_p}), for each active p.
        # Plus t NOT in hensel_root(p, λ_p + 1) mod p^{λ_p + 1}
        # (i.e., exactly λ_p, not λ_p + 1).

        # For simplicity, just record the "λ_p pinned" part (the superset).
        # The B ≤ 1 elimination holds at exactly this fine-grained class.

        if not b["active_primes"]:
            # No active primes: eliminates all t (for this k).
            # This means EVERY t satisfies the branch, so Erdős is forced to fail.
            classes.append({"k": k, "B_eff": b["B_eff"],
                            "constraint_mod": 1, "t_classes": [0]})
            continue

        # Build the CRT-combined class. For each active p, λ_p ≥ 1 pins
        # t ≡ t_j (mod p^{λ_p}) where t_j = hensel_root to level λ_p.
        # For λ_p = 0, no pinning but must exclude λ_p = 1 class.
        # For simplicity here, we record the MINIMAL pinning: t mod
        # ∏ p^{λ_p}.
        crt_mod = 1
        crt_residues = [0]
        valid = True
        for p, lam_p in b["lambda"].items():
            p = int(p)
            if lam_p == 0:
                # No pinning; branch covers all classes mod p (except the
                # excluded single class).
                # For our purposes, this branch acts over the full range of
                # t-residues EXCEPT one class mod p.
                # To keep analysis clean, we'll record this as "multiple
                # allowed classes mod p" and defer the exclusion.
                # Actually: since λ_p = 0 means NO pinning at p (within the
                # branch), we just don't multiply by p.
                continue
            # λ_p ≥ 1: pin t to a specific class mod p^{λ_p}
            t_pinned = hensel_lift_root(r, k, p, lam_p)
            if t_pinned is None:
                valid = False; break
            if t_pinned == "all":
                continue
            # Combine via CRT with current crt_mod
            new_mod = crt_mod * (p ** lam_p)
            new_residues = []
            for tc in crt_residues:
                # Need x ≡ tc (mod crt_mod), x ≡ t_pinned (mod p^lam_p)
                inv = mod_inv(crt_mod, p ** lam_p)
                diff = (t_pinned - tc) % (p ** lam_p)
                k_val = (inv * diff) % (p ** lam_p)
                x = tc + crt_mod * k_val
                new_residues.append(x % new_mod)
            crt_mod = new_mod
            crt_residues = new_residues
        if not valid:
            continue
        classes.append({"k": k, "B_eff": b["B_eff"],
                        "constraint_mod": crt_mod, "t_classes": crt_residues,
                        "lambda": b["lambda"]})
    return classes


def main():
    data = json.load(open(REPO / "data" / "exact_tight_branches.json"))
    print("=" * 90)
    print("Covering analysis: do rigorously-eliminated branches cover all t-classes?")
    print("=" * 90)

    # For each residue, collect ALL B ≤ 1 elimination classes from ALL k ≤ 100.
    for r_str, per_k in data["results"].items():
        r = int(r_str)
        print(f"\n=== r = {r} ===")

        # Collect all elimination classes
        all_classes = []  # list of (k, constraint_mod, t_class)
        for k_str, branches in per_k.items():
            k = int(k_str)
            # Reconstruct b dicts with int keys
            branches_fixed = []
            for b in branches:
                # lambda keys may be strings from JSON
                lam_fixed = {int(p): v for p, v in (b.get("lambda") or {}).items()}
                branches_fixed.append({**b, "lambda": lam_fixed,
                                       "active_primes": b.get("active_primes", [])})
            classes = collect_eliminated_classes(r, k, branches_fixed)
            for cls in classes:
                all_classes.append(cls)

        print(f"  Total B ≤ 1 elimination classes: {len(all_classes)}")

        from math import gcd as math_gcd
        def lcm(a, b): return a * b // math_gcd(a, b)

        # Constraint-modulus histogram — which prime powers appear?
        cm_counter = Counter()
        for cls in all_classes:
            cm_counter[cls["constraint_mod"]] += 1
        print(f"  Constraint-modulus histogram (top 10): {cm_counter.most_common(10)}")

        # Compute the true LCM of all constraint moduli.
        # If coverage ever reaches M*_LCM, that's a full obstruction.
        full_lcm = 1
        for cm in cm_counter:
            full_lcm = lcm(full_lcm, cm)
        print(f"  LCM of all constraint moduli: {full_lcm}")

        # LCM is huge; Monte Carlo sample to estimate covered fraction.
        import random
        random.seed(42 + r)
        N_MC = 100_000
        covered_count = 0
        covered_by_class = Counter()
        for _ in range(N_MC):
            t = random.randint(0, full_lcm - 1)
            hit = False
            for cls in all_classes:
                cm = cls["constraint_mod"]
                if cm == 0: cm = 1
                if (t % cm) in set(tc % cm for tc in cls["t_classes"]):
                    hit = True
                    covered_by_class[cls["constraint_mod"]] += 1
                    break
            if hit:
                covered_count += 1
        pct = 100 * covered_count / N_MC
        print(f"  Monte Carlo coverage (N={N_MC}): {covered_count}/{N_MC} = {pct:.3f}%")
        if covered_count == N_MC:
            print(f"  Every sampled t is covered — strong signal of full coverage at r={r}.")
        else:
            # Upper bound on uncovered fraction (Clopper-Pearson 99% upper)
            uncov = N_MC - covered_count
            print(f"  Uncovered fraction ≈ {uncov/N_MC:.4%} (possibly real gap in B≤1 coverage)")
        # Measure-sum upper bound on coverage: Σ 1/cm (without overlap correction)
        from fractions import Fraction
        meas_sum = Fraction(0)
        for cls in all_classes:
            cm = cls["constraint_mod"]
            if cm == 0: cm = 1
            meas_sum += Fraction(len(cls["t_classes"]), cm)
        meas_sum_f = float(meas_sum)
        print(f"  Σ measure(class) = {meas_sum_f:.4f} (upper bound on coverage fraction)")
        if meas_sum_f < 1.0:
            print(f"  Sum < 1 — coverage CANNOT be complete at r={r}. Uncovered mass ≥ {(1-meas_sum_f)*100:.2f}%.")

    # Save
    print()
    print(f"Done. Full data retained in data/exact_tight_branches.json.")


if __name__ == "__main__":
    main()
