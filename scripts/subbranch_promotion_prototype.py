"""
Plan A / sub-branching version of the local-promotion prototype.

For each tentative hard branch (r, c) with tentative covering prime
p_cover (either 2 or 3), sub-branch into p_cover mod-(30 * p_cover)
sub-branches and test whether EACH sub-branch closes at budget <= 3.

Rationale: within a mod-30 branch, the promotion "p | L(u) for every
u" is impossible after reduction (gcd(alpha_red, beta_red) = 1). But
sub-branching on u mod p_cover creates p_cover sub-branches, in each
of which u has a fixed residue mod p_cover. Under the substitution
u = p_cover * v + r_p, any form L(u) with L(r_p) = 0 mod p_cover
becomes identically divisible by p_cover in the sub-branch, and the
reduced form L(u)/p_cover has smaller leading coefficient -- a form
of smaller nominal budget, computed automatically by compute_forms
with branch_mod = 30 * p_cover.

For the parent branch to close, ALL p_cover sub-branches must close
rigorously at budget <= 3.

Output: per-branch pass/fail verdict + per-sub-branch detail.
"""
from __future__ import annotations

import json
import math
from pathlib import Path


M = 46189


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


def tau(n: int) -> int:
    if n <= 1:
        return max(n, 0)
    c = 0
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            c += 2 if i != n // i else 1
    return c


SMALL_PRIMES = [p for p in range(2, 1000) if is_prime(p)]


def compute_forms(r: int, c_eff: int, branch_mod: int,
                  k_max: int = 10000, budget_cap: int = 3) -> list[dict]:
    """Matches higher_budget_enumeration.py's compute_forms."""
    forms = []
    for k in range(1, k_max + 1):
        raw_b = 2520 * r - k
        if raw_b == 0:
            continue
        g = math.gcd(2520 * M, abs(raw_b))
        if tau(g) == 0:
            continue
        g_k = math.gcd(k, 2520)
        d = 2520 // g_k
        new_g = g
        for p in [2, 3, 5, 7]:
            if g_k % p != 0:
                continue
            if d % p == 0:
                continue
            if (d * (46189 * c_eff + r) - 1) % p == 0:
                new_g *= p
        a_orig = (2520 * M) // g
        b_orig = raw_b // g
        a_u = a_orig * branch_mod
        b_u = a_orig * c_eff + b_orig
        extra = math.gcd(abs(a_u), abs(b_u))
        total_g = new_g * extra
        final_budget = (k + 2) // tau(total_g)
        if final_budget <= budget_cap:
            forms.append({
                'k': k,
                'a_red': a_u // extra,
                'b_red': b_u // extra,
                'budget': final_budget,
            })
    return forms


def check_inadm(forms: list[dict], budget_cap: int) -> tuple[int | None, list[int] | None]:
    """Return (covering_prime, list_of_k_per_forbidden_residue) or (None, None)."""
    pool = [(f['a_red'], f['b_red'], f['k']) for f in forms if f['budget'] <= budget_cap]
    if not pool:
        return None, None
    for p in SMALL_PRIMES:
        if len(pool) < p:
            break
        forbidden = {}
        hit_zero_k = None
        for a, b, k in pool:
            am = a % p
            bm = b % p
            if am == 0:
                if bm == 0:
                    hit_zero_k = k
                    break
            else:
                inv_a = pow(am, p - 2, p)
                forb = ((-bm) * inv_a) % p
                forbidden.setdefault(forb, []).append(k)
        if hit_zero_k is not None:
            return p, [hit_zero_k]
        if len(forbidden) >= p:
            cover_ks = [min(ks) for ks in forbidden.values()]
            return p, cover_ks
    return None, None


def analyze_subbranches(r: int, c: int, p_cover: int) -> dict:
    """Sub-branch (r, c) mod 30 into p_cover sub-branches mod (30 * p_cover).

    For each sub-branch c' in {c + 30*i : i in range(p_cover)}, check
    whether closure at budget <= 3 holds.
    """
    new_branch_mod = 30 * p_cover
    sub_cs = [c + 30 * i for i in range(p_cover)]

    sub_results = []
    all_close = True
    for sub_c in sub_cs:
        forms = compute_forms(r, sub_c, new_branch_mod,
                              k_max=10000, budget_cap=3)
        bd = {'b1': 0, 'b2': 0, 'b3': 0}
        for f in forms:
            if f['budget'] <= 1:
                bd['b1'] += 1
            elif f['budget'] == 2:
                bd['b2'] += 1
            elif f['budget'] == 3:
                bd['b3'] += 1

        # Direct budget-1 closure: any budget-1 form is a direct
        # contradiction (reduced form L(u) has tau <= 1 for all u in the
        # branch, but L(u) -> infinity so tau >= 2 for large u).
        has_b1 = bd['b1'] > 0

        # Covering closure at budget <= 2 and <= 3
        p_b2, _ = check_inadm(forms, 2)
        p_b3, _ = check_inadm(forms, 3)

        closes = has_b1 or (p_b2 is not None) or (p_b3 is not None)
        if not closes:
            all_close = False

        sub_results.append({
            'sub_c': sub_c,
            'branch_mod': new_branch_mod,
            'n_forms': len(forms),
            'budget_dist': bd,
            'closes_b1_direct': has_b1,
            'closes_b2': p_b2,
            'closes_b3': p_b3,
            'closes': closes,
        })

    return {
        'r': r,
        'c': c,
        'p_cover': p_cover,
        'new_branch_mod': new_branch_mod,
        'n_sub_branches': p_cover,
        'all_close': all_close,
        'sub_results': sub_results,
    }


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    tentative = json.load(open(root / 'data' / 'tentative_hard_branches.json'))
    states = tentative['tentative_states']

    print(f"Sub-branching promotion prototype on {len(states)} tentative hard branches")
    print(f"(Plan A: sub-branch by covering prime p, check budget<=3 closure per sub-branch)")
    print()
    header = f"{'r':>6} {'c':>3}  p  {'M_new':>5}  {'sub_branches_closing':>25}  verdict"
    print(header)
    print('-' * len(header))

    n_closed = 0
    results = []
    for s in states:
        result = analyze_subbranches(s['r'], s['c'], s['p_needed'])
        n_sub_close = sum(1 for sr in result['sub_results'] if sr['closes'])
        n_sub_total = result['n_sub_branches']

        if result['all_close']:
            n_closed += 1
            verdict = f"CLOSES: all {n_sub_total} sub-branches close at b<=3"
        else:
            verdict = f"resistant: {n_sub_total - n_sub_close}/{n_sub_total} sub-branches stay open"

        print(f"{s['r']:>6} {s['c']:>3}  {s['p_needed']}  {result['new_branch_mod']:>5}  "
              f"{n_sub_close}/{n_sub_total}                        {verdict}")
        results.append(result)

    print()
    print('=' * 80)
    print(f"SUMMARY: {n_closed}/{len(states)} branches close via sub-branching on the covering prime.")
    print('=' * 80)

    out = {
        'description': 'Sub-branching promotion (Plan A) on 18 tentative branches',
        'generated_by': 'scripts/subbranch_promotion_prototype.py',
        'mechanism': ('Sub-branch each tentative (r, c) mod-30 branch on u mod p_cover '
                      '(the tentative covering prime). This gives p_cover sub-branches '
                      'mod (30 * p_cover). For the parent branch to close rigorously at '
                      'budget <= 3, every sub-branch must close individually. The natural '
                      'reduction inside compute_forms handles the "promotion" of forms '
                      'whose leading term gains a factor of p_cover in the sub-branch, '
                      'lowering their effective budget.'),
        'n_branches_tested': len(states),
        'n_closed': n_closed,
        'results': results,
    }
    out_path = root / 'data' / 'subbranch_promotion_attempts.json'
    out_path.write_text(json.dumps(out, indent=2, default=str) + '\n')
    print(f"\nWrote {out_path.relative_to(root)}")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
