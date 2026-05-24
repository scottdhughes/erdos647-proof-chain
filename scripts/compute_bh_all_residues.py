"""
Compute Bateman-Horn singular series constants for all 5 hard residues.

Extends scripts/compute_bh_constant.py (which covers r=0 only) to all
5 hard residues at higher prime precision, and computes leading-order
expected witness counts at X = 10^13 and 10^14.

Key technical point: the "naive BH" prediction treats forms as if they
were independent random primes. The singular series captures the actual
per-prime correlation — ν(p) = number of distinct forbidden t-residues
mod p is smaller than 13·p/p when forms share residue classes mod p.
So the singular series IS correlation-aware at the local level.

What naive independence additionally ignores: higher-order corrections
(prime-power contributions, archimedean effects). The leading-order
formula is thus correlation-aware but not "fully refined."

Output: data/bh_all_residues.json
"""

from __future__ import annotations

import json
import math
from pathlib import Path


M = 46189


def sieve_primes(limit: int) -> list[int]:
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_p[i]:
            is_p[i * i::i] = bytearray(len(is_p[i * i::i]))
    return [i for i in range(2, limit + 1) if is_p[i]]


def tau(n: int) -> int:
    if n <= 0:
        raise ValueError
    c = 0
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            c += 2 if i != n // i else 1
    return c


def get_forms(r: int) -> list[tuple[int, int]]:
    """Return the budget-<=3 prime core forms (alpha, beta) at residue r."""
    forms = []
    for k in range(1, 301):
        g = math.gcd(k, 2520)
        a = 2520 // g
        b = k // g
        alpha = a * M
        beta = a * r - b
        fg = math.gcd(alpha, abs(beta)) if beta != 0 else alpha
        content = g * fg
        budget = (k + 2) // tau(content) if content > 0 else float('inf')
        if budget <= 3:
            forms.append((alpha, beta))
    return forms


def nu_at_prime(forms: list[tuple[int, int]], p: int) -> int:
    """Number of distinct forbidden t-residues mod p for the tuple."""
    forbidden = set()
    for alpha, beta in forms:
        a_mod = alpha % p
        b_mod = beta % p
        if a_mod == 0:
            if b_mod == 0:
                # Form is 0 mod p for all t — bad, contributes 0 forbidden
                pass
            else:
                # Form is b_mod ≠ 0 mod p for all t — never 0 mod p, 0 forbidden
                pass
        else:
            # α t + β ≡ 0 mod p ⟺ t ≡ -β α^{-1} mod p
            inv_a = pow(a_mod, p - 2, p)
            forbidden.add((-b_mod * inv_a) % p)
    return len(forbidden)


def compute_c_bh(forms: list[tuple[int, int]], prime_bound: int) -> tuple[float, list]:
    """Bateman-Horn singular series for the given form list."""
    K = len(forms)
    primes = sieve_primes(prime_bound)
    log_prod = 0.0
    partial_values = []
    milestones = {10_000, 100_000, 500_000, 1_000_000, 5_000_000, 10_000_000}
    for p in primes:
        nu = nu_at_prime(forms, p)
        local = (1.0 - nu / p) * ((1.0 - 1.0 / p) ** (-K))
        if local > 0:
            log_prod += math.log(local)
        else:
            return 0.0, partial_values
        if p in milestones:
            partial_values.append((p, math.exp(log_prod)))
    return math.exp(log_prod), partial_values


def bh_predict(forms: list[tuple[int, int]], c_bh: float, X: float) -> float:
    """Leading-order BH prediction for witness count up to X."""
    denom = 1.0
    for alpha, _ in forms:
        denom *= math.log(alpha * X)
    return c_bh * X / denom


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    results: dict = {
        'description': 'Bateman-Horn singular series for all 5 hard residues',
        'generated_by': 'scripts/compute_bh_all_residues.py',
        'prime_bound': 1_000_000,
        'residues': {},
    }

    prime_bound = 1_000_000

    print(f"Computing BH constants for all 5 hard residues (primes up to {prime_bound:,}):")
    print()
    for r in [0, 1716, 4862, 16302, 17160]:
        forms = get_forms(r)
        K = len(forms)
        c_bh, partials = compute_c_bh(forms, prime_bound)

        pred_13 = bh_predict(forms, c_bh, 1e13)
        pred_14 = bh_predict(forms, c_bh, 1e14)
        pred_15 = bh_predict(forms, c_bh, 1e15)
        pred_16 = bh_predict(forms, c_bh, 1e16)

        print(f"r = {r}:  {K}-form tuple")
        print(f"  C_BH (primes <= {prime_bound:,}): {c_bh:.6e}")
        for pp, cv in partials:
            print(f"    at primes <= {pp:>10,}: C_BH = {cv:.6e}")
        print(f"  BH predictions (leading order, independence-across-forms):")
        print(f"    at X = 10^13: {pred_13:.4f} expected witnesses")
        print(f"    at X = 10^14: {pred_14:.4f} expected witnesses")
        print(f"    at X = 10^15: {pred_15:.4f} expected witnesses")
        print(f"    at X = 10^16: {pred_16:.4f} expected witnesses")
        print()

        results['residues'][str(r)] = {
            'tuple_size': K,
            'c_bh': c_bh,
            'partials_by_prime_bound': [(pp, cv) for pp, cv in partials],
            'predictions': {
                '1e13': pred_13, '1e14': pred_14,
                '1e15': pred_15, '1e16': pred_16,
            },
        }

    # Summary table
    print("=" * 84)
    print(f"{'r':>6}  {'K':>4}  {'C_BH':>12}  {'pred 1e13':>10}  {'pred 1e14':>10}  "
          f"{'pred 1e15':>10}  {'pred 1e16':>10}")
    print("-" * 84)
    for r, data in results['residues'].items():
        print(f"{r:>6}  {data['tuple_size']:>4}  {data['c_bh']:>12.4e}  "
              f"{data['predictions']['1e13']:>10.4f}  "
              f"{data['predictions']['1e14']:>10.4f}  "
              f"{data['predictions']['1e15']:>10.4f}  "
              f"{data['predictions']['1e16']:>10.4f}")

    out_path = root / 'data' / 'bh_all_residues.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print()
    print(f"Wrote {out_path.relative_to(root)}")

    # Calibration vs paper's quoted 0.48 / 2.5 (at r=0).
    r0 = results['residues']['0']
    print()
    print("Calibration: paper quotes 0.48 (X=10^13) and 2.5 (X=10^14) for r=0.")
    print(f"This script computes: {r0['predictions']['1e13']:.4f}, {r0['predictions']['1e14']:.4f}.")

    return 0


if __name__ == '__main__':
    raise SystemExit(main())
