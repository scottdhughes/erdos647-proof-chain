"""
Higher-budget closure attempt for the 5 hard residues.

The frozen classifier (`classify_all_96.py`) attempts closure at each
level via (a) budget-<=1 contradiction and (b) budget-<=2
inadmissibility covering Z/pZ at a prime p in {2, 3, 5, 17, 19}. The
classifier CODE defines a budget-<=3 version (`check_inadmissible_budget23`)
but does NOT invoke it in the branch loop. Nor does anything at budget
>= 4.

This script closes that gap for each of the 5
hard residues, enumerate all forms up to a higher budget cap and try
closure at each budget level 2, 3, 4, 5, 6, 7. If any mechanism closes
a currently-hard residue, the hard set shrinks unconditionally.

Output: `data/higher_budget_attempts.json` with per-(r, c) verdicts.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


M = 46189
BRANCH_MOD = 30
INADMISSIBILITY_PRIME_BOUND = 1000


def tau(n: int) -> int:
    if n <= 1:
        return max(n, 0)
    c = 0
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            c += 2 if i != n // i else 1
    return c


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


SMALL_PRIMES = [p for p in range(2, INADMISSIBILITY_PRIME_BOUND + 1) if is_prime(p)]
HARD_RESIDUES_5 = [0, 1716, 4862, 16302, 17160]


def compute_forms(r: int, c_eff: int, branch_mod: int,
                  k_max: int = 10000, budget_cap: int = 10) -> list[dict]:
    """Copy of the frozen classifier's form-computation, extended to higher cap."""
    forms = []
    for k in range(1, k_max + 1):
        raw_b = 2520 * r - k
        if raw_b == 0:
            continue
        g = math.gcd(2520 * M, abs(raw_b))
        tg = tau(g)
        if tg == 0:
            continue
        # Caveat promotions
        g_k = math.gcd(k, 2520)
        d = 2520 // g_k
        new_g = g
        for p in [2, 3, 5, 7]:
            if g_k % p != 0:
                continue
            if d % p == 0:
                continue
            val = (d * (46189 * c_eff + r) - 1) % p
            if val == 0:
                new_g *= p
        # U-level form
        a_orig = (2520 * M) // g
        b_orig = raw_b // g
        a_u = a_orig * branch_mod
        b_u = a_orig * c_eff + b_orig
        extra = math.gcd(abs(a_u), abs(b_u))
        total_g = new_g * extra
        total_tg = tau(total_g)
        final_budget = (k + 2) // total_tg
        if final_budget <= budget_cap:
            a_red = a_u // extra
            b_red = b_u // extra
            forms.append({
                'k': k,
                'a_red': a_red,
                'b_red': b_red,
                'budget': final_budget,
                'g_total': total_g,
                'tg_total': total_tg,
            })
    return forms


def check_budget_le_1(forms: list[dict]) -> tuple[bool, int | None]:
    for f in forms:
        if f['budget'] <= 1:
            return True, f['k']
    return False, None


def check_inadmissible_at_budget(forms: list[dict], budget_cap: int) -> tuple[bool, int | None, int | None]:
    """Check inadmissibility for forms with budget <= budget_cap.

    For a covering prime p: every t has some form f with p | L_f(t).
    For budget-b forms with p | L_f(t) and L_f(t) > p^{b-1}, tau(L_f) >= b+1,
    contradicting the budget. So budget-2, 3, ..., b forms all contribute
    to covering arguments at sufficiently large u.

    Returns (is_closed, prime, budget_threshold).
    """
    pool = [(f['a_red'], f['b_red']) for f in forms if f['budget'] <= budget_cap]
    if not pool:
        return False, None, None
    for p in SMALL_PRIMES:
        if len(pool) < p:
            break
        forbidden = set()
        hit_zero = False
        for a, b in pool:
            am = a % p
            bm = b % p
            if am == 0:
                if bm == 0:
                    hit_zero = True
                    break
            else:
                inv_a = pow(am, p - 2, p)
                forbidden.add(((-bm) * inv_a) % p)
        if hit_zero or len(forbidden) >= p:
            return True, p, budget_cap
    return False, None, None


def attempt_closure(r: int, c_eff: int, branch_mod: int,
                    max_budget: int = 10, k_max: int = 10000,
                    prime_bound: int = 1000) -> dict:
    """Attempt to close (r, c_eff, branch_mod) at progressively higher budgets.

    Valid closure mechanisms (per paper Section 4 b23 theorem):
      - budget_le_1: a form has content forcing tau > k+2.
      - budget_le_2: covering of Z/pZ at prime p by budget-<=2 forms.
      - budget_le_3: covering of Z/pZ at prime p by budget-<=3 forms
        (b23 mechanism; valid because covering + L_f(t) > p^2 forces
        tau >= 4 > budget when budget <= 3).

    At budget = 4, covering + L_f(t) > p^3 gives tau >= 4 = budget,
    which is ALLOWED. So budget-<=4 inadmissibility is NOT a rigorous
    closure mechanism. Labeled 'tentative_budget_le_N' for N >= 4.
    """
    forms = compute_forms(r, c_eff, branch_mod, k_max=k_max, budget_cap=max_budget)
    n_forms = len(forms)
    budgets_dist = {}
    for f in forms:
        budgets_dist[f['budget']] = budgets_dist.get(f['budget'], 0) + 1

    # Rigorous closure mechanisms: budget <= 1 (immediate), budget <= 2, budget <= 3.
    ok, k = check_budget_le_1(forms)
    if ok:
        return {
            'status': 'closed', 'mechanism': 'budget_le_1', 'rigorous': True,
            'k': k, 'n_forms': n_forms, 'budget_dist': budgets_dist,
        }
    ok, p, _ = check_inadmissible_at_budget(forms, 2)
    if ok:
        return {
            'status': 'closed', 'mechanism': 'inadmissible_budget_le_2',
            'rigorous': True, 'prime': p,
            'n_forms': n_forms, 'budget_dist': budgets_dist,
        }
    ok, p, _ = check_inadmissible_at_budget(forms, 3)
    if ok:
        return {
            'status': 'closed', 'mechanism': 'inadmissible_budget_le_3',
            'rigorous': True, 'prime': p,
            'n_forms': n_forms, 'budget_dist': budgets_dist,
        }

    # Tentative closures at budget >= 4 — would need extra argument to justify.
    for b_cap in range(4, max_budget + 1):
        ok, p, _ = check_inadmissible_at_budget(forms, b_cap)
        if ok:
            return {
                'status': 'tentative',
                'mechanism': f'tentative_budget_le_{b_cap}',
                'rigorous': False, 'prime': p,
                'note': ('Covering by budget-<=b_cap forms with b_cap>=4 does NOT '
                         'automatically give tau > budget; requires extra argument '
                         '(e.g., p^2-covering or tuple-inadmissibility).'),
                'n_forms': n_forms, 'budget_dist': budgets_dist,
            }

    return {
        'status': 'open', 'n_forms': n_forms, 'budget_dist': budgets_dist,
    }


def run_for_residue(r: int, max_budget: int, k_max: int, prime_bound: int) -> dict:
    """Run closure attempts at level 0 + all 30 level-1 branches for residue r."""
    # Temporarily override prime bound (module-level)
    global SMALL_PRIMES
    old_primes = SMALL_PRIMES
    SMALL_PRIMES = [p for p in range(2, prime_bound + 1) if is_prime(p)]

    try:
        lvl0 = attempt_closure(r, 0, 1, max_budget=max_budget, k_max=k_max,
                               prime_bound=prime_bound)
        branch_results = {}
        for c in range(BRANCH_MOD):
            lvl1 = attempt_closure(r, c, BRANCH_MOD, max_budget=max_budget,
                                   k_max=k_max, prime_bound=prime_bound)
            branch_results[c] = lvl1
        return {'level0': lvl0, 'branches': branch_results}
    finally:
        SMALL_PRIMES = old_primes


def summarize(label: str, results: dict) -> dict:
    print(f"\n{label}")
    print(f"{'r':>7}  {'rigorous closed':>16}  {'tentative':>10}  {'open':>6}  "
          f"mechanisms (rigorous)")
    print("-" * 100)
    summary = {}
    for r in HARD_RESIDUES_5:
        branches = results[r]['branches']
        n_rigorous = sum(1 for v in branches.values() if v.get('rigorous') is True)
        n_tentative = sum(1 for v in branches.values() if v['status'] == 'tentative')
        n_open = sum(1 for v in branches.values() if v['status'] == 'open')
        rigorous_mechs = sorted(set(v.get('mechanism', '') for v in branches.values()
                                    if v.get('rigorous') is True))
        print(f"{r:>7}  {n_rigorous:>16}  {n_tentative:>10}  {n_open:>6}  {rigorous_mechs}")
        summary[str(r)] = {
            'rigorous_closed': n_rigorous,
            'tentative': n_tentative,
            'open': n_open,
            'all_rigorously_closed': n_rigorous == BRANCH_MOD,
        }
    return summary


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    print("Higher-budget closure attempts for the 5 hard residues")
    print("Rigorous mechanisms: budget_le_1, inadm_budget_le_2, inadm_budget_le_3")
    print("Tentative (requires extra argument): inadm_budget_le_{4,5,...}")
    print()

    # Pass A: match the frozen classifier exactly (k_max=5000, prime_bound=500).
    print("=" * 100)
    print("PASS A — match frozen classifier params (k_max=5000, prime_bound=500, budget_cap=6)")
    print("=" * 100)
    results_A = {}
    for r in HARD_RESIDUES_5:
        results_A[r] = run_for_residue(r, max_budget=6, k_max=5000, prime_bound=500)
    summary_A = summarize("PASS A summary:", results_A)

    # Pass B: extend k_max and prime_bound — might catch closures the frozen classifier missed.
    print()
    print("=" * 100)
    print("PASS B — extended params (k_max=10000, prime_bound=1000, budget_cap=10)")
    print("=" * 100)
    results_B = {}
    for r in HARD_RESIDUES_5:
        results_B[r] = run_for_residue(r, max_budget=10, k_max=10000, prime_bound=1000)
    summary_B = summarize("PASS B summary:", results_B)

    # Compare passes — any new rigorous closures found in B but not A?
    print()
    print("=" * 100)
    print("DELTA (pass B finds closures pass A missed)")
    print("=" * 100)
    deltas = {}
    for r in HARD_RESIDUES_5:
        gained = []
        for c in range(BRANCH_MOD):
            a = results_A[r]['branches'][c]
            b = results_B[r]['branches'][c]
            if (a.get('rigorous') is not True) and (b.get('rigorous') is True):
                gained.append({'c': c,
                               'A_status': a['status'],
                               'A_mech': a.get('mechanism', '-'),
                               'B_status': b['status'],
                               'B_mech': b.get('mechanism'),
                               'B_prime': b.get('prime')})
        deltas[r] = gained
        if gained:
            print(f"  r = {r}: {len(gained)} new rigorous closures in pass B:")
            for g in gained:
                print(f"    c={g['c']}: A={g['A_mech']} -> B={g['B_mech']} at p={g['B_prime']}")
        else:
            print(f"  r = {r}: no new rigorous closures (same as pass A)")

    out_path = root / 'data' / 'higher_budget_attempts.json'
    out_path.write_text(json.dumps({
        'description': 'Higher-budget closure attempts comparing frozen-params vs extended-params',
        'generated_by': 'scripts/higher_budget_enumeration.py',
        'pass_A': {'k_max': 5000, 'prime_bound': 500, 'budget_cap': 6,
                   'summary': summary_A},
        'pass_B': {'k_max': 10000, 'prime_bound': 1000, 'budget_cap': 10,
                   'summary': summary_B},
        'deltas': {str(r): deltas[r] for r in HARD_RESIDUES_5},
    }, indent=2, default=str) + '\n')
    print(f"\nWrote {out_path.relative_to(root)}")

    # Final verdict
    print()
    print("=" * 100)
    print("VERDICT")
    print("=" * 100)
    any_resolved = False
    for r in HARD_RESIDUES_5:
        if summary_B[str(r)]['all_rigorously_closed']:
            print(f"  r = {r}: ALL 30 branches rigorously closed. Residue is NOT hard.")
            any_resolved = True
        else:
            rem = summary_B[str(r)]['open']
            tent = summary_B[str(r)]['tentative']
            print(f"  r = {r}: {summary_B[str(r)]['rigorous_closed']}/30 rigorously closed, "
                  f"{tent} tentative, {rem} open. Still hard.")
    if not any_resolved:
        print("\n  No hard residue rigorously closes under budget <= 3 + branching mod 30.")
        print("  The 91/5 partition stands. This pass does not shrink the hard set.")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
