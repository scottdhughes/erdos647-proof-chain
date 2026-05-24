"""
Quadratic-nonresidue (QNR) elimination prototype for the 18 tentative
hard branches in the budget-3 elimination pass.

Mechanism:
  For a budget-3 form L(u) = alpha*u + beta, the constraint tau(L) <= 3
  allows L = p or L = p^2. If we can rule out L = p^2 for all u in the
  branch, the form effectively becomes budget-2 (prime-only), which has
  a tighter covering argument.

How to rule out L(u) = p^2 uniformly in u:
  For any prime q with q | alpha, L(u) mod q = beta mod q (constant in u).
  If beta mod q is a NON-zero quadratic non-residue (NR) mod q, then
  L(u) is always a NR mod q, hence L(u) is NEVER a perfect square.

For gcd(q, alpha) = 1, L(u) mod q varies over all residues as u varies,
so some u gives a QR — we can't uniformly rule out squares. QNR
elimination therefore requires q | alpha.

Non-trivial elimination requires q | alpha AND gcd(beta, q) = 1 AND
beta mod q is a NR mod q.

After QNR-eliminating some budget-3 forms, we re-run the covering
argument:
  - original budget-<=2 forms stay budget-2
  - QNR-eliminated budget-3 forms become effectively budget-2
  - non-eliminated budget-3 forms stay budget-3
If the augmented budget-<=2 pool covers Z/pZ at any operative prime p,
the branch closes via a NEW rigorous mechanism (budget-2 inadmissibility
after square elimination, call it "inadm_b2_with_qnr").

This prototype tests: for each of the 18 tentative branches, does QNR
elimination enable a new rigorous closure?

Output: data/qnr_elimination_attempts.json with per-branch verdict.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


M = 46189
BRANCH_MOD = 30
INADMISSIBILITY_PRIME_BOUND = 1000


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


SMALL_PRIMES = [p for p in range(2, INADMISSIBILITY_PRIME_BOUND + 1) if is_prime(p)]


def prime_factors(n: int, bound: int = 10**6) -> list[int]:
    """Return the distinct prime factors of n, using trial division up to bound."""
    factors = []
    n = abs(n)
    if n == 0:
        return []
    for p in SMALL_PRIMES:
        if p > bound:
            break
        if p * p > n:
            break
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
    if n > 1:
        factors.append(n)
    return factors


def is_qr(a: int, p: int) -> bool:
    """Is a a quadratic residue mod p? (p odd prime assumed, or p=2.)"""
    a = a % p
    if a == 0:
        return True  # 0 is trivially a square
    if p == 2:
        return True  # every odd number is a QR mod 2 trivially
    return pow(a, (p - 1) // 2, p) == 1


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


def qnr_eliminate(form: dict) -> dict:
    """Attempt to eliminate the p^2 option for a budget-3 form.

    Returns:
      {'eliminated': bool, 'via_q': int | None, 'reason': str}
    """
    if form['budget'] != 3:
        return {'eliminated': False, 'via_q': None, 'reason': 'not_budget_3'}
    alpha = form['a_red']
    beta = form['b_red']
    alpha_primes = prime_factors(alpha)
    for q in alpha_primes:
        if q == 2:
            # Mod 2: every odd integer is a square mod 2 (= 1^2 = 1) and
            # every even integer is also trivially a square. Mod-2 QR
            # elimination doesn't exist.
            continue
        beta_mod_q = beta % q
        if beta_mod_q == 0:
            # Beta divisible by q — L can be any multiple of q; can't rule out squares this way.
            continue
        if not is_qr(beta_mod_q, q):
            # Non-trivial QNR elimination: L(u) ≡ beta (mod q) is a non-zero NR mod q,
            # so L(u) is never a perfect square.
            return {'eliminated': True, 'via_q': q, 'reason': f'beta={beta_mod_q} is NR mod {q}'}
    return {'eliminated': False, 'via_q': None, 'reason': 'no_q_with_beta_NR_found'}


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
            # Every residue covered.
            cover_ks = [min(ks) for ks in forbidden.values()]
            return p, cover_ks
    return None, None


def attempt_qnr_closure(r: int, c: int, branch_mod: int = BRANCH_MOD) -> dict:
    """Try QNR elimination then re-run budget-2 covering on a branch."""
    forms = compute_forms(r, c, branch_mod, k_max=10000, budget_cap=3)

    budget_dist = {'b1': 0, 'b2': 0, 'b3': 0}
    for f in forms:
        if f['budget'] <= 1:
            budget_dist['b1'] += 1
        elif f['budget'] == 2:
            budget_dist['b2'] += 1
        elif f['budget'] == 3:
            budget_dist['b3'] += 1

    # Baseline: without QNR elimination, can we close at budget-2?
    base_prime, _ = check_inadm(forms, 2)
    if base_prime is not None:
        return {
            'status': 'already_closed_baseline_b2',
            'prime': base_prime,
            'budget_dist': budget_dist,
            'eliminated_forms': [],
        }

    # Baseline at b3 (rigorous): already known to close for some branches per
    # earlier analysis, but not the 18 tentative.
    b3_prime, _ = check_inadm(forms, 3)
    if b3_prime is not None:
        return {
            'status': 'already_closed_baseline_b3',
            'prime': b3_prime,
            'budget_dist': budget_dist,
            'eliminated_forms': [],
        }

    # Apply QNR elimination to each budget-3 form.
    eliminated = []
    augmented_forms = []
    for f in forms:
        if f['budget'] == 3:
            result = qnr_eliminate(f)
            if result['eliminated']:
                eliminated.append({
                    'k': f['k'], 'via_q': result['via_q'], 'reason': result['reason'],
                })
                # Form becomes effectively budget-2
                augmented_forms.append({
                    'k': f['k'], 'a_red': f['a_red'], 'b_red': f['b_red'], 'budget': 2,
                })
            else:
                augmented_forms.append(f)
        else:
            augmented_forms.append(f)

    # Check if augmented budget-<=2 pool closes at some prime.
    new_prime, covering_ks = check_inadm(augmented_forms, 2)
    if new_prime is not None:
        return {
            'status': 'closed_via_qnr',
            'prime': new_prime,
            'eliminated_forms': eliminated,
            'n_eliminated': len(eliminated),
            'covering_ks': covering_ks,
            'budget_dist': budget_dist,
        }

    return {
        'status': 'open',
        'eliminated_forms': eliminated,
        'n_eliminated': len(eliminated),
        'budget_dist': budget_dist,
    }


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    tentative = json.load(open(root / 'data' / 'tentative_hard_branches.json'))
    states = tentative['tentative_states']

    print(f"QNR-elimination prototype on {len(states)} tentative hard branches")
    print()
    print(f"{'r':>7}  {'c':>3}  {'status':>30}  {'prime':>6}  "
          f"{'elim_count':>11}  detail")
    print('-' * 100)

    results = []
    n_closed = 0
    for s in states:
        r, c = s['r'], s['c']
        result = attempt_qnr_closure(r, c)
        detail = ''
        if result['status'] == 'closed_via_qnr':
            n_closed += 1
            ks_eliminated = sorted(e['k'] for e in result['eliminated_forms'])
            detail = f"closes at p={result['prime']}; eliminated k's: {ks_eliminated[:8]}"
            if len(ks_eliminated) > 8:
                detail += f" (+{len(ks_eliminated)-8} more)"
        elif result['status'] == 'open':
            detail = f"still open; QNR eliminated {result['n_eliminated']} of "\
                     f"{result['budget_dist']['b3']} budget-3 forms but covering "\
                     f"doesn't close"
        else:
            detail = f"baseline closure at p={result.get('prime')}"

        prime_str = str(result.get('prime', '-'))
        elim_str = str(result.get('n_eliminated', '-'))
        print(f"{r:>7}  {c:>3}  {result['status']:>30}  {prime_str:>6}  "
              f"{elim_str:>11}  {detail}")
        results.append({'r': r, 'c': c, **result})

    print()
    print("=" * 100)
    print(f"SUMMARY: {n_closed}/{len(states)} tentative branches newly close via QNR elimination")
    print("=" * 100)
    if n_closed == 0:
        print("QNR-elimination-at-q|alpha does not close any tentative branch.")
        print("Paper still has 18 tentative branches at budget <= 3.")
    elif n_closed == len(states):
        print("ALL tentative branches close via QNR elimination.")
        print("The 91/5 hard set would close at the branch level entirely.")
    else:
        print(f"Partial success: {n_closed} branches close.")
        print("Paper's 18 tentative branches reduce to "
              f"{len(states) - n_closed}.")

    out_path = root / 'data' / 'qnr_elimination_attempts.json'
    out_path.write_text(json.dumps({
        'description': 'QNR-elimination prototype on 18 tentative hard branches',
        'generated_by': 'scripts/qnr_elimination_prototype.py',
        'mechanism': 'For budget-3 form L(u) = alpha*u + beta, eliminate p^2 option via: prime q | alpha AND beta mod q is a non-zero NR mod q. Then re-run budget-2 covering with QNR-eliminated forms treated as budget-2.',
        'n_branches_tested': len(states),
        'n_newly_closed': n_closed,
        'results': results,
    }, indent=2, default=str) + '\n')
    print(f"\nWrote {out_path.relative_to(root)}")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
