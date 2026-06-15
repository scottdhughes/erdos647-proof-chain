import Mathlib
import Bridge2
import Erdos647QuotientCover

/-!
# v₂₃ Hensel rootline closure theorem — core lemma

The `hensel_rootline_closure` theorem (main repo namespace).

This is the load-bearing lemma for the 41 per-residue partial closures
in the `Erdos647V23Closures` directory.

## Statement

Given:
- An arithmetic progression `A·s + b` and shift `k`
- An algebraic factorization `2520·(A·s + b) - k = d · (α·s + c₀)`
  holding for every s
- `c₀ ≥ 2` (so `α·s + c₀ ≥ 2` for every s)
- `τ(d·p) > k + 2` for every prime p

Then for every `s : ℕ`, `¬ goodOn {k} (A·s + b)` in the
`Erdos647QuotientCover` sense.

Mechanism: since `α·s + c₀ ≥ 2`, it has a prime factor p
(via `Nat.minFac`). Then `d·p ∣ 2520·(A·s + b) - k`, so by
divisor-count monotonicity `τ(2520·(A·s + b) - k) ≥ τ(d·p) > k+2`.
-/

set_option maxHeartbeats 400000

namespace Erdos647V23Hensel

open Erdos647QuotientCover

theorem hensel_rootline_closure
    (k d A b α c₀ : ℕ)
    (h_eq : ∀ s : ℕ, 2520 * (A * s + b) - k = d * (α * s + c₀))
    (_h_d_pos : 0 < d)
    (hc₀ : 2 ≤ c₀)
    (h_tau : ∀ p : ℕ, Nat.Prime p → k + 2 < (d * p).divisors.card) :
    ∀ s : ℕ, ¬ goodOn {k} (A * s + b) := by
  intro s hgood
  -- goodOn {k} N says τ(m N k) ≤ k + 2.
  have hbnd : (m (A * s + b) k).divisors.card ≤ k + 2 := by
    simpa [goodOn] using hgood k (by simp)
  -- The cofactor q = α·s + c₀ is ≥ 2, so it has a prime factor p.
  set q : ℕ := α * s + c₀ with hq_def
  have hq_ge : 2 ≤ q := by
    have : 2 ≤ α * s + c₀ := by omega
    simpa [hq_def] using this
  have hq_pos : 0 < q := by omega
  let p : ℕ := q.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp_dvd_q : p ∣ q := Nat.minFac_dvd q
  -- From the algebraic identity, m (A·s+b) k = d · q.
  have hm_eq : m (A * s + b) k = d * q := by
    simpa [m, hq_def] using h_eq s
  -- So d·p ∣ d·q ∣ m.
  have hdp_dvd_m : d * p ∣ m (A * s + b) k := by
    rw [hm_eq]
    exact Nat.mul_dvd_mul_left d hp_dvd_q
  have hm_pos : 0 < m (A * s + b) k := by
    rw [hm_eq]
    exact Nat.mul_pos _h_d_pos hq_pos
  -- Divisor-count monotonicity.
  have hmono : (d * p).divisors.card ≤ (m (A * s + b) k).divisors.card :=
    Finset.card_le_card
      (Nat.divisors_subset_of_dvd (Nat.ne_of_gt hm_pos) hdp_dvd_m)
  have htau : k + 2 < (d * p).divisors.card := h_tau p hp_prime
  omega

end Erdos647V23Hensel
