#!/usr/bin/env python3
"""Batch autopsy of all 143 monitor-escape records.

Per convergent directive: classify all monitor-escapes by
(B^eff, Z-shape) signature at each offset in the network
{7, 11, 13, 14, 15, 16, 27}. Cluster into families.

Output: data/batch_autopsy_143_escapes.json
       docs/batch_autopsy_143_memo.md
"""

import json
from collections import Counter, defaultdict
from pathlib import Path

from sympy import factorint, isprime

REPO = Path(__file__).parent.parent
M = 46189
A_CONST = 2520 * M
r_res = 0

PRIMES_P0 = [2, 3, 5, 7, 11, 13, 17, 19]
A_VAL = {2: 3, 3: 2, 5: 1, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1}
CORE_K = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24}
BASE_ENRICHED_0 = CORE_K | {20}
MONITOR = [7, 11, 13, 16]
NETWORK_K = [7, 11, 13, 14, 15, 16, 27]


def v_p(n, p):
    if n == 0: return None
    n = abs(n); c = 0
    while n % p == 0:
        n //= p; c += 1
    return c


def tau(n):
    if n <= 0: return 0
    if n == 1: return 1
    f = factorint(n)
    t = 1
    for e in f.values():
        t *= (e + 1)
    return t


def passes_at_k(k, t):
    N = M * t + r_res
    x = 2520 * N - k
    if x <= 0: return False
    return tau(x) <= k + 2


def shape_tuple(n):
    """Return (omega, total_exponent) for clustering."""
    if n <= 1: return (0, 0)
    f = factorint(n)
    return (len(f), sum(f.values()))


def analyze_k(k, t):
    C = 2520 * r_res - k
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
    fixed_content = 1
    for p in PRIMES_P0:
        if p not in S:
            cp = c_p[p] or 0
            T_fix_tau *= (cp + 1)
            fixed_content *= p ** cp
    active_factor = 1
    for p in S:
        active_factor *= (A_VAL[p] + lam[p] + 1)
    B_eff = (k + 2) // (T_fix_tau * active_factor)
    A_fixed = fixed_content
    for p in S:
        A_fixed *= p ** (A_VAL[p] + lam[p])
    Z = F // A_fixed if F % A_fixed == 0 else None
    tau_F = tau(F)
    passes = tau_F <= k + 2
    return {
        "pass": passes,
        "tau_F": tau_F, "bound": k + 2,
        "B_eff": B_eff,
        "Z": Z,
        "Z_shape": shape_tuple(Z),
        "Z_omega": shape_tuple(Z)[0],
        "Z_prime": isprime(Z) if Z and Z > 1 else False,
        "S_size": len(S),
    }


def main():
    records = [json.loads(l) for l in open(REPO / "data" / "all_phases_merged.jsonl")]
    print(f"Loaded {len(records)} records")

    # Find all monitor-escape records
    escapes = []
    for rec in records:
        t = rec["t"]
        if all(passes_at_k(k, t) for k in MONITOR):
            escapes.append(rec)
    print(f"Monitor-escape records: {len(escapes)}")

    # For each escape, compute the branch signature across network
    details = []
    for rec in escapes:
        t = rec["t"]
        sig = {}
        for k in NETWORK_K:
            info = analyze_k(k, t)
            if info:
                sig[k] = info
        details.append({"t": t, "primes": rec["primes"], "sig": sig})

    # Cluster by signature pattern
    # Pattern 1: (B^eff at each network k, pass/fail at each)
    signature_pattern = Counter()
    first_fail_B_distribution = Counter()
    all_b_eff_profile = Counter()
    z_omega_profile = Counter()

    for rec in details:
        t = rec["t"]
        sig = rec["sig"]
        # Build pass/fail pattern
        pass_pattern = tuple((k, sig[k]["pass"]) for k in NETWORK_K if k in sig)
        signature_pattern[pass_pattern] += 1

        # Find first failure in network
        first_fail_k = None
        for k in NETWORK_K:
            if k in sig and not sig[k]["pass"]:
                first_fail_k = k
                break
        if first_fail_k is not None:
            info = sig[first_fail_k]
            first_fail_B_distribution[(first_fail_k, info["B_eff"])] += 1

        # B_eff profile across network: tuple of B_eff values
        b_profile = tuple(sig[k]["B_eff"] if k in sig else None for k in NETWORK_K)
        all_b_eff_profile[b_profile] += 1

        # Z-omega profile (just at passing offsets)
        z_omegas = []
        for k in NETWORK_K:
            if k in sig and sig[k]["pass"]:
                z_omegas.append(sig[k]["Z_omega"])
        z_omega_profile[tuple(z_omegas)] += 1

    print(f"\n=== Pass/fail patterns across network ===")
    print(f"Distinct patterns: {len(signature_pattern)}")
    for pattern, count in signature_pattern.most_common(10):
        # Compact display
        pass_str = " ".join(f"k{k}:{'P' if p else 'F'}" for k, p in pattern)
        print(f"  {count:>3} × {pass_str}")

    print(f"\n=== First-fail (k, B^eff) distribution ===")
    for (k, B), count in first_fail_B_distribution.most_common(10):
        pct = 100 * count / len(escapes)
        print(f"  k={k}, B^eff={B}: {count:>4} ({pct:.1f}%)")

    print(f"\n=== B^eff profile across network (top-10 patterns) ===")
    for profile, count in all_b_eff_profile.most_common(10):
        profile_str = " ".join(str(b) for b in profile)
        print(f"  {count:>3} × B={profile_str}")

    # Output
    output = {
        "total_monitor_escapes": len(escapes),
        "distinct_pass_patterns": len(signature_pattern),
        "top10_pass_patterns": [
            {"pattern": [{"k": k, "pass": p} for k, p in pat], "count": c}
            for pat, c in signature_pattern.most_common(10)
        ],
        "first_fail_B_eff_distribution": {f"k{k}_B{B}": c for (k, B), c in first_fail_B_distribution.most_common(20)},
        "top10_B_eff_profiles": [
            {"network_k": NETWORK_K, "B_profile": list(p), "count": c}
            for p, c in all_b_eff_profile.most_common(10)
        ],
        "network_k": NETWORK_K,
        "n_details_saved": min(30, len(details)),
        "details_sample": [
            {"t": r["t"], "primes": r["primes"],
             "sig_compact": {k: {
                 "pass": r["sig"][k]["pass"],
                 "B": r["sig"][k]["B_eff"],
                 "tau_F": r["sig"][k]["tau_F"],
                 "Z_omega": r["sig"][k]["Z_omega"],
                 "Z_prime": r["sig"][k]["Z_prime"],
             } for k in NETWORK_K if k in r["sig"]}}
            for r in details[:30]
        ],
    }

    with open(REPO / "data" / "batch_autopsy_143_escapes.json", "w") as f:
        json.dump(output, f, indent=2, default=int)
    print(f"\nWrote data/batch_autopsy_143_escapes.json")


if __name__ == "__main__":
    main()
