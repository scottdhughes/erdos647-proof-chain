#!/usr/bin/env python3
"""Independent verifier for the B=3 QNR square-kill certificates at k ≤ 100.

This script reads data/b3_qnr_certificates_k100.json and independently
re-derives each claim without reusing the generator's compute logic.

Verifies, per certificate:
  1. The branch is in-scope: r ∈ hardResidues_5, k ∈ [1,100] \\ base_enriched(r).
  2. B^eff_{r,k,λ} = 3 (recomputed from the atlas).
  3. α and β are as claimed (recomputed from atlas definitions).
  4. gcd(α, β) = 1.
  5. The certificate is valid:
       - odd q: q | α, β not ≡ 0 mod q, and (β/q) = −1 (Legendre).
       - q=2: v_2(α) ≥ 2 and β ≢ 1 (mod 4) [or v_2(α) ≥ 3 and β ≢ 1 (mod 8)].
  6. Saturation: branches enumerated at max_lambda=50 agree with max_lambda=30.
  7. No duplicate branch (each (r, k, λ) appears at most once).
  8. Exhaustive: every B^eff=3 branch in the finite universe is covered.

If all checks pass, print PROVEN. Else print specific failure diagnostics.
"""

import json
from collections import Counter
from math import gcd
from pathlib import Path

from sympy import factorint, legendre_symbol

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
HARD_RESIDUES = (0, 1716, 4862, 16302, 17160)


def v_p(n, p):
    if n == 0:
        return None
    n = abs(n); c = 0
    while n % p == 0:
        n //= p; c += 1
    return c


def ext_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x, y = ext_gcd(b, a % b)
    return g, y, x - (a // b) * y


def mod_inv(a, m):
    g, x, _ = ext_gcd(a % m, m)
    return x % m if g == 1 else None


def recompute_branch(r, k, lam):
    """Recompute B_eff, alpha, beta from atlas structure. Returns None on error."""
    C = 2520 * r - k
    # Active primes
    S = []
    c_p = {}
    for p in PRIMES_P0:
        cp = v_p(C, p) if C != 0 else None
        c_p[p] = cp
        if cp is not None and cp >= A_VAL[p]:
            S.append(p)
    # Validate lam keys are exactly S
    lam_primes = set(int(p) for p in lam)
    if lam_primes != set(S):
        return None, f"lambda keys {lam_primes} don't match active primes {set(S)}"

    # T_fix_tau and fixed_content
    T_fix_tau = 1
    fixed_content = 1
    for p in PRIMES_P0:
        if p not in S:
            cp = c_p[p] or 0
            T_fix_tau *= (cp + 1)
            fixed_content *= p ** cp

    # A_fixed
    A_fixed = fixed_content
    for p in S:
        lp = int(lam[p]) if p in lam else int(lam[str(p)])
        A_fixed *= p ** (A_VAL[p] + lp)

    # pfactor and B_eff
    pfactor = 1
    for p in S:
        lp = int(lam[p]) if p in lam else int(lam[str(p)])
        pfactor *= (A_VAL[p] + lp + 1)
    B_eff = (k + 2) // (T_fix_tau * pfactor)

    # Compute Hensel-lifted t_0 to get the branch residue
    crt_residue = 0
    crt_mod = 1
    Q_pin = 1
    for p in S:
        lp = int(lam[p]) if p in lam else int(lam[str(p)])
        if lp == 0:
            continue
        ap = A_VAL[p]
        pap = p ** ap
        if A_CONST % pap != 0 or C % pap != 0:
            return None, f"A_CONST or C not divisible by p^{ap} at p={p}"
        A_red = A_CONST // pap
        C_red = C // pap
        mod = p ** lp
        inv = mod_inv(A_red % mod, mod)
        if inv is None:
            return None, f"no inverse of A_red mod p^{lp} at p={p}"
        t_p = (-C_red * inv) % mod
        # CRT combine
        inv2 = mod_inv(crt_mod, mod)
        if inv2 is None:
            return None, f"no CRT inverse"
        diff = (t_p - crt_residue) % mod
        kv = (inv2 * diff) % mod
        crt_residue = crt_residue + crt_mod * kv
        crt_mod *= mod
        Q_pin *= mod

    num0 = A_CONST * crt_residue + C
    if num0 % A_fixed != 0:
        return None, "A_fixed doesn't divide A·t_0 + C"
    beta = num0 // A_fixed
    slope_num = A_CONST * Q_pin
    if slope_num % A_fixed != 0:
        return None, "A_fixed doesn't divide A·Q_pin"
    alpha = slope_num // A_fixed
    return (B_eff, alpha, beta, A_fixed), None


def verify_certificate(cert):
    """Verify one certificate. Returns (True, None) on pass, (False, reason) on fail."""
    r = cert["r"]
    k = cert["k"]
    lam = cert["lambda"]

    # Check 1: in-scope
    if r not in HARD_RESIDUES:
        return False, f"r={r} not a hard residue"
    if k < 1 or k > 100:
        return False, f"k={k} out of range"
    if k in BASE_ENRICHED[r]:
        return False, f"k={k} is in base_enriched({r})"

    # Check 2-4: recompute B_eff, alpha, beta
    result, err = recompute_branch(r, k, lam)
    if result is None:
        return False, f"branch recompute failed: {err}"
    B_eff, alpha, beta, A_fixed = result
    if B_eff != 3:
        return False, f"recomputed B_eff={B_eff}, expected 3"
    if alpha != cert["alpha"]:
        return False, f"alpha mismatch: computed {alpha}, cert claims {cert['alpha']}"
    if beta != cert["beta"]:
        return False, f"beta mismatch: computed {beta}, cert claims {cert['beta']}"
    g = gcd(alpha, beta)
    if g != 1:
        return False, f"gcd(alpha, beta) = {g}, expected 1"

    # Check 5: certificate validity
    c = cert["certificate"]
    q = c["q"]
    cert_type = c["certificate_type"]
    if cert_type == "odd_prime_QNR":
        if q == 2:
            return False, f"odd_prime_QNR with q=2"
        if alpha % q != 0:
            return False, f"q={q} does not divide alpha"
        if beta % q == 0:
            return False, f"q={q} divides beta (gcd should preclude this)"
        ls = legendre_symbol(beta, q)
        if ls != -1:
            return False, f"Legendre (beta/q) = {ls}, expected -1 (QNR)"
    elif cert_type == "2_adic_mod8":
        if q != 2:
            return False, f"2_adic_mod8 but q={q}"
        v2_alpha = v_p(alpha, 2)
        if v2_alpha is None or v2_alpha < 3:
            return False, f"v_2(alpha) = {v2_alpha}, expected >= 3 for mod-8"
        b8 = beta % 8
        if b8 == 1:
            return False, f"beta mod 8 = 1 (consistent with p^2), not excluded"
        if b8 != c["beta_mod_q"]:
            return False, f"beta mod 8 mismatch"
    elif cert_type == "2_adic_mod4":
        if q != 2:
            return False, f"2_adic_mod4 but q={q}"
        v2_alpha = v_p(alpha, 2)
        if v2_alpha is None or v2_alpha < 2:
            return False, f"v_2(alpha) = {v2_alpha}, expected >= 2 for mod-4"
        b4 = beta % 4
        if b4 == 1:
            return False, f"beta mod 4 = 1 (consistent with p^2), not excluded"
    else:
        return False, f"unknown certificate_type {cert_type}"

    return True, None


def enumerate_b3_branches_max_lambda(max_lambda):
    """Enumerate all B_eff=3 branches at k <= 100 up to given max lambda."""
    count = 0
    branches = []
    for r in HARD_RESIDUES:
        ban = BASE_ENRICHED[r]
        for k in range(1, 101):
            if k in ban:
                continue
            C = 2520 * r - k
            S = []
            c_p = {}
            for p in PRIMES_P0:
                cp = v_p(C, p) if C != 0 else None
                c_p[p] = cp
                if cp is not None and cp >= A_VAL[p]:
                    S.append(p)
            T_fix_tau = 1
            for p in PRIMES_P0:
                if p not in S:
                    cp = c_p[p] or 0
                    T_fix_tau *= (cp + 1)
            if not S:
                B = (k + 2) // T_fix_tau
                if B == 3:
                    count += 1
                    branches.append((r, k, {}))
                continue

            def rec(idx, partial):
                nonlocal count
                if idx == len(S):
                    pfactor = 1
                    for p in S:
                        pfactor *= (A_VAL[p] + partial[p] + 1)
                    B = (k + 2) // (T_fix_tau * pfactor)
                    if B == 3:
                        count += 1
                        branches.append((r, k, dict(partial)))
                    return
                p = S[idx]
                for v in range(max_lambda + 1):
                    partial[p] = v
                    rec(idx + 1, partial)
                    del partial[p]
            rec(0, {})
    return count, branches


def main():
    data = json.load(open(REPO / "data" / "b3_qnr_certificates_k100.json"))
    certificates = data["certificates"]
    exceptions = data.get("exceptions", [])

    # Check 1: no claimed exceptions
    if exceptions:
        print(f"FAIL: data file claims {len(exceptions)} exceptions")
        return

    # Check 2: saturation — enumerate at max_lambda = 30 and 50
    count30, _ = enumerate_b3_branches_max_lambda(30)
    count50, branches50 = enumerate_b3_branches_max_lambda(50)
    if count30 != count50:
        print(f"FAIL: max_lambda=30 gives {count30}, max_lambda=50 gives {count50}")
        return
    if count50 != len(certificates):
        print(f"FAIL: enumeration gives {count50} branches, certs file has {len(certificates)}")
        return

    # Check 3: uniqueness of (r, k, λ) in certs
    seen = set()
    for c in certificates:
        key = (c["r"], c["k"], tuple(sorted(c["lambda"].items())))
        if key in seen:
            print(f"FAIL: duplicate branch (r={c['r']}, k={c['k']}, λ={c['lambda']})")
            return
        seen.add(key)

    # Check 4: every enumerated branch has a certificate
    enum_set = set()
    for r, k, lam in branches50:
        enum_set.add((r, k, tuple(sorted((int(p), v) for p, v in lam.items()))))
    cert_set = set()
    for c in certificates:
        cert_set.add((c["r"], c["k"], tuple(sorted((int(p), v) for p, v in c["lambda"].items()))))
    if enum_set != cert_set:
        missing = enum_set - cert_set
        extra = cert_set - enum_set
        print(f"FAIL: enumerated set ≠ certified set. Missing: {len(missing)}, Extra: {len(extra)}")
        if missing:
            print(f"  Sample missing: {list(missing)[:3]}")
        return

    # Check 5: verify each certificate independently
    fail_count = 0
    fail_reasons = Counter()
    for cert in certificates:
        ok, reason = verify_certificate(cert)
        if not ok:
            fail_count += 1
            fail_reasons[reason] += 1
    if fail_count:
        print(f"FAIL: {fail_count} of {len(certificates)} certificates failed verification")
        print(f"  Reasons: {dict(fail_reasons.most_common(5))}")
        return

    # All checks passed
    print(f"PROVEN — B=3 QNR square-kill theorem verified independently.")
    print(f"  Branches enumerated (max_lambda=30): {count30}")
    print(f"  Branches enumerated (max_lambda=50): {count50}")
    print(f"  Certificates in file: {len(certificates)}")
    print(f"  All match; all certificates independently verified.")
    print(f"  Saturation lemma: B_eff=3 ⇒ τ(A) ≤ (k+2)/3 ≤ 34 (k ≤ 100) ⇒ λ_p ≤ 32 per prime.")


if __name__ == "__main__":
    main()
