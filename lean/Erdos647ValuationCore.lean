import Mathlib
import Erdos647BridgeV1
import Erdos647SieveCertificate

/-!
# Full-value valuation core for the Stage-1 reduction

This file contains only reusable lemmas about the full integer
`2520 * N - k`. It does not mention `BudgetForm`, `branchForms`,
`SatisfiesBudgets`, or Bridge 3.
-/

namespace Erdos647ValuationCore

open Erdos647BridgeV1

private lemma natCard_div_eq_card (m : ℕ) :
    Nat.card (Nat.divisors m) = (Nat.divisors m).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The direct divisor-count bound extracted from `IsErdos647` at a fixed shift. -/
theorem tau_bound_at_k (N k : ℕ) (hE : IsErdos647 (2520 * N))
    (hk : 1 ≤ k) (hklt : k < 2520 * N) :
    (Nat.divisors (2520 * N - k)).card ≤ k + 2 := by
  have h := hE (2520 * N - k) (by omega) (by omega)
  rw [natCard_div_eq_card] at h
  have hkle : k ≤ 2520 * N := Nat.le_of_lt hklt
  have hsub : (2520 * N - k) + k = 2520 * N := Nat.sub_add_cancel hkle
  omega

/-- A single shift with divisor count above budget kills `IsErdos647`. -/
theorem not_isErdos647_of_tau_gt_at {N k : ℕ}
    (hk : 1 ≤ k) (hklt : k < 2520 * N)
    (htau : k + 2 < (Nat.divisors (2520 * N - k)).card) :
    ¬ IsErdos647 (2520 * N) := by
  intro hE
  have hbound := tau_bound_at_k N k hE hk hklt
  omega

/-- Prime factors outside the prime-factor support are coprime. -/
theorem coprime_of_prime_notin_primeFactors {a p : ℕ} (ha0 : a ≠ 0) (hp : Nat.Prime p)
    (hnot : p ∉ a.primeFactors) :
    Nat.Coprime p a := by
  refine hp.coprime_iff_not_dvd.mpr ?_
  intro hpdvd
  exact hnot <| Nat.mem_primeFactors.mpr ⟨hp, hpdvd, ha0⟩

/-- Any integer greater than `1` has a prime divisor. -/
theorem exists_prime_dvd_of_gt_one {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n := by
  exact Nat.exists_prime_and_dvd (by omega)

/-- Convert a residue equality modulo `M` into the standard quotient-plus-residue
decomposition. -/
theorem decompose_mod (N r : ℕ) (hr : N % Erdos647SieveCertificate.M = r) :
    N = Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) + r := by
  calc
    N = Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) + N % Erdos647SieveCertificate.M := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod N Erdos647SieveCertificate.M).symm
    _ = Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) + r := by
      rw [hr]

/-- If `N ≡ r (mod M)`, then `a * N ≡ a * r (mod a*M)`. -/
theorem cast_mul_mod_eq (a N r : ℕ) (hr : N % Erdos647SieveCertificate.M = r) :
    (((a * N : ℕ) : ZMod (a * Erdos647SieveCertificate.M))) =
      (((a * r : ℕ) : ZMod (a * Erdos647SieveCertificate.M))) := by
  have hdecomp := decompose_mod N r hr
  have hcast :
      (((a * N : ℕ) : ZMod (a * Erdos647SieveCertificate.M))) =
        (((a * (Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) + r) : ℕ)
          : ZMod (a * Erdos647SieveCertificate.M))) := by
    exact congrArg (fun t : ℕ => ((a * t : ℕ) : ZMod (a * Erdos647SieveCertificate.M))) hdecomp
  calc
    (((a * N : ℕ) : ZMod (a * Erdos647SieveCertificate.M)))
        = (((a * (Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) + r) : ℕ)
            : ZMod (a * Erdos647SieveCertificate.M))) := hcast
    _ = (((a * Erdos647SieveCertificate.M) * (N / Erdos647SieveCertificate.M) + a * r : ℕ)
          : ZMod (a * Erdos647SieveCertificate.M)) := by
            congr 1
            ring
    _ = (((a * r : ℕ) : ZMod (a * Erdos647SieveCertificate.M))) := by
          simp

end Erdos647ValuationCore
