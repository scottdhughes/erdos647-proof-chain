#!/usr/bin/env python3
"""Full ledger of all records passing the full network {7,11,13,14,15,16,27}.

Per consistency-audit request: produce exact first-fail k for each of
the 5 deep-network escapes, and catalog their full {7,11,13,14,15,16,17,21,27}
+ tail structure.

Output: data/deep_escape_ledger.json
       docs/deep_escape_ledger_memo.md
"""

import json
from collections import Counter
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
NETWORK = [7, 11, 13, 14, 15, 16, 27]
EXTENDED = [7, 11, 13, 14, 15, 16, 17, 21, 27]


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
        "pass": passes, "tau_F": tau_F, "bound": k + 2,
        "B_eff": B_eff, "Z_omega": shape_tuple(Z)[0],
        "Z_prime": isprime(Z) if Z and Z > 1 else False,
        "S": S, "lambda": {int(p): lam[p] for p in S},
    }


def first_fail_in_range(t, k_range):
    for k in k_range:
        if k in BASE_ENRICHED_0: continue
        if not passes_at_k(k, t):
            return k
    return None


def first_fail_block(t, K_lo, K_hi):
    k_range = [k for k in range(K_lo, K_hi + 1) if k not in BASE_ENRICHED_0]
    return first_fail_in_range(t, k_range)


def main():
    records = [json.loads(l) for l in open(REPO / "data" / "all_phases_merged.jsonl")]
    print(f"Loaded {len(records)} records")

    # Find all records passing full network
    print(f"Scanning for records passing network {NETWORK}...")
    deep_escapes = []
    for rec in records:
        t = rec["t"]
        if all(passes_at_k(k, t) for k in NETWORK):
            deep_escapes.append(rec)
    print(f"Deep-network escapes: {len(deep_escapes)}")

    # For each, full autopsy
    print("\n=== Deep-escape ledger ===")
    print(f"{'t':>18} {'primes':>6} {'first-fail k':>14} {'tau':>4} {'bound':>6} {'block':>15}")
    ledger = []
    for rec in deep_escapes:
        t = rec["t"]
        # Find first fail across k ∈ [1, 1000] \ base_enriched
        first_fail = None
        for k in range(1, 1001):
            if k in BASE_ENRICHED_0: continue
            if not passes_at_k(k, t):
                first_fail = k
                break
        if first_fail is None:
            block_label = "passes_k_le_1000"
            first_tau = None; first_bound = None
        else:
            N = M * t + r_res
            x = 2520 * N - first_fail
            first_tau = tau(x)
            first_bound = first_fail + 2
            if first_fail <= 100:
                block_label = "[1, 100]"
            elif first_fail <= 200:
                block_label = "[101, 200]"
            elif first_fail <= 500:
                block_label = "[201, 500]"
            else:
                block_label = "[501, 1000]"
        tau_str = f"{first_tau}" if first_tau is not None else "-"
        bound_str = f"{first_bound}" if first_bound is not None else "-"
        print(f"  {t:>16,} {rec['primes']:>6} {first_fail if first_fail else 'ALL_PASS':>14} {tau_str:>4} {bound_str:>6} {block_label:>15}")

        # Detailed analysis at EXTENDED offsets
        sig = {}
        for k in EXTENDED:
            info = analyze_k(k, t)
            if info:
                sig[k] = info

        ledger.append({
            "t": t, "primes": rec["primes"],
            "first_fail": first_fail,
            "first_fail_tau": first_tau,
            "first_fail_bound": first_bound,
            "first_fail_block": block_label,
            "passes_network": True,
            "extended_sig": {k: sig[k] for k in EXTENDED if k in sig},
        })

    # Summary
    print(f"\n=== Summary ===")
    block_counts = Counter()
    first_fail_counts = Counter()
    for rec in ledger:
        block_counts[rec["first_fail_block"]] += 1
        if rec["first_fail"] is not None:
            first_fail_counts[rec["first_fail"]] += 1
    print(f"First-fail k distribution: {dict(first_fail_counts.most_common(10))}")
    print(f"First-fail block distribution: {dict(block_counts)}")

    # The critical question: do all 5 first-fail at k ≤ 100?
    n_fail_at_100 = sum(1 for r in ledger if r["first_fail"] is not None and r["first_fail"] <= 100)
    n_fail_beyond_100 = len(ledger) - n_fail_at_100
    print(f"\nCONSISTENCY CHECK:")
    print(f"  # first-fail at k ≤ 100: {n_fail_at_100} / {len(ledger)}")
    print(f"  # first-fail at k > 100: {n_fail_beyond_100} / {len(ledger)}")

    if n_fail_beyond_100 == 0:
        print(f"  CONCLUSION: full k ≤ 100 screen catches all {len(ledger)} deep-network escapes.")
        print(f"  Paper statement 'full k ≤ 100 catches 143/143' is CORRECT.")
    else:
        print(f"  CONCLUSION: {n_fail_beyond_100} deep escapes pass k ≤ 100 and require moving tail.")
        print(f"  Paper statement needs UPDATE: full k ≤ 100 catches {143 - n_fail_beyond_100}/143, tail catches rest.")

    # Save
    with open(REPO / "data" / "deep_escape_ledger.json", "w") as f:
        json.dump({
            "n_deep_escapes": len(ledger),
            "first_fail_distribution": dict(first_fail_counts),
            "first_fail_block_distribution": dict(block_counts),
            "n_fail_at_k_le_100": n_fail_at_100,
            "n_fail_beyond_k_100": n_fail_beyond_100,
            "ledger": ledger,
        }, f, indent=2, default=int)
    print(f"\nWrote data/deep_escape_ledger.json")


if __name__ == "__main__":
    main()
