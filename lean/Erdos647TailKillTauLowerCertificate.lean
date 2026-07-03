import Mathlib.NumberTheory.Divisors

/-!
# TailKillUpTo tau lower-bound certificates

This module contains only the generic divisor-certificate lemma used by the
TailKillUpTo witness-certificate prototype.  It does not import TailKill slice
coverage files, adapters, lookup modules, generated evidence, or any aggregate
finite-prefix theorem.
-/

namespace Erdos647TailKillTauLowerCertificate

/-- A finite set of certified divisors gives a lower bound for `Nat.divisors`. -/
def TauLowerFinsetCertValid (n threshold : Nat) (ds : Finset Nat) : Prop :=
  n ≠ 0 ∧ threshold < ds.card ∧ ∀ d ∈ ds, d ≠ 0 ∧ n % d = 0

/--
If a certificate supplies more than `threshold` distinct positive divisors of
`n`, then the divisor-count lower bound `threshold < (Nat.divisors n).card`
holds.
-/
theorem tau_gt_of_valid_divisor_finset_cert
    {n threshold : Nat} {ds : Finset Nat}
    (h : TauLowerFinsetCertValid n threshold ds) :
    threshold < (Nat.divisors n).card := by
  rcases h with ⟨hn, hcard, hvalid⟩
  have hsub : ds ⊆ Nat.divisors n := by
    intro d hd
    rcases hvalid d hd with ⟨_hdpos, hmod⟩
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero hmod, hn⟩
  exact lt_of_lt_of_le hcard (Finset.card_le_card hsub)

/--
List-shaped certificates are accepted by first forgetting ordering.  The
`Nodup` field is retained so executable checkers can emit ordinary lists while
the theorem consumes their finite set of distinct divisors.
-/
def TauLowerListCertValid (n threshold : Nat) (ds : List Nat) : Prop :=
  ds.Nodup ∧ TauLowerFinsetCertValid n threshold ds.toFinset

theorem tau_gt_of_valid_divisor_list_cert
    {n threshold : Nat} {ds : List Nat}
    (h : TauLowerListCertValid n threshold ds) :
    threshold < (Nat.divisors n).card :=
  tau_gt_of_valid_divisor_finset_cert h.2

/-- Array-shaped certificate interface for generated data payloads. -/
def TauLowerArrayCertValid (n threshold : Nat) (ds : Array Nat) : Prop :=
  TauLowerListCertValid n threshold ds.toList

theorem tau_gt_of_valid_divisor_array_cert
    {n threshold : Nat} {ds : Array Nat}
    (h : TauLowerArrayCertValid n threshold ds) :
    threshold < (Nat.divisors n).card :=
  tau_gt_of_valid_divisor_list_cert h

/-- TailKill witness certificates use threshold `k + 2`. -/
def TailKillWitnessTauCertValid (n k : Nat) (ds : Array Nat) : Prop :=
  TauLowerArrayCertValid n (k + 2) ds

theorem tau_gt_k_plus_two_of_tailkill_witness_cert
    {n k : Nat} {ds : Array Nat}
    (h : TailKillWitnessTauCertValid n k ds) :
    k + 2 < (Nat.divisors n).card :=
  tau_gt_of_valid_divisor_array_cert h

#print axioms tau_gt_of_valid_divisor_finset_cert
#print axioms tau_gt_of_valid_divisor_list_cert
#print axioms tau_gt_of_valid_divisor_array_cert
#print axioms tau_gt_k_plus_two_of_tailkill_witness_cert

end Erdos647TailKillTauLowerCertificate
