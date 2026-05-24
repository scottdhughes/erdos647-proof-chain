import Mathlib
import Bridge2
import Erdos647BridgeV1
import Erdos647SieveCertificate
import Erdos647ValuationCore
import Erdos647SingleOverlap_4199_13_draft
import Erdos647SingleOverlap_14535_45_draft
import ShapeDecomposition

/-!
# Single-overlap full-value closures

This file starts the replacement of Bridge 3's dead budget-transfer lane
with direct full-value closure theorems.

Phase 1 target:

* the load-bearing `ble1` family `(g_exact, k) = (260, 20)`, which covers
  38 residues.

The proof is fully at the level of `2520 * N - k`; it does not route through
`BudgetForm`, `branchForms`, or `SatisfiesBudgets`.
-/

namespace Erdos647SingleOverlapClosure

open Erdos647BridgeV1
open Erdos647ValuationCore

private lemma natCard_div_eq_card (m : ℕ) :
    Nat.card (Nat.divisors m) = (Nat.divisors m).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The 38-residue `ble1` family with `g_exact = 260`, `k = 20`. -/
def residues26020 : Finset ℕ :=
  {55, 484, 1342, 3344, 4631, 6919, 8635, 12210, 14212, 15070, 15499,
   15928, 16786, 19074, 19503, 20361, 22363, 23221, 24079, 26367, 26796,
   27225, 27654, 30514, 31229, 31372, 34089, 34518, 34947, 35376, 38522,
   38665, 39380, 41382, 42240, 42669, 43527, 45815}

private lemma residue26020_div (r : ℕ) (hr : r ∈ residues26020) :
    260 ∣ 2520 * r - 20 := by
  native_decide +revert

private lemma residue26020_b_ge_two (r : ℕ) (hr : r ∈ residues26020) :
    2 ≤ (2520 * r - 20) / 260 := by
  native_decide +revert

private lemma residue26020_b_odd (r : ℕ) (hr : r ∈ residues26020) :
    Odd ((2520 * r - 20) / 260) := by
  native_decide +revert

private lemma residue26020_ge55 (r : ℕ) (hr : r ∈ residues26020) :
    55 ≤ r := by
  native_decide +revert

private lemma tau_bound_at_k (N k : ℕ) (hE : IsErdos647 (2520 * N))
    (hk : 1 ≤ k) (hklt : k < 2520 * N) :
    (Nat.divisors (2520 * N - k)).card ≤ k + 2 := by
  have h := hE (2520 * N - k) (by omega) (by omega)
  rw [natCard_div_eq_card] at h
  have hkle : k ≤ 2520 * N := Nat.le_of_lt hklt
  have hsub : (2520 * N - k) + k = 2520 * N := Nat.sub_add_cancel hkle
  omega

private lemma coprime_of_prime_notin_primeFactors {a p : ℕ} (ha0 : a ≠ 0) (hp : Nat.Prime p)
    (hnot : p ∉ a.primeFactors) :
    Nat.Coprime p a := by
  refine hp.coprime_iff_not_dvd.mpr ?_
  intro hpdvd
  exact hnot <| Nat.mem_primeFactors.mpr ⟨hp, hpdvd, ha0⟩

private lemma exists_prime_ne_of_not_primepow
    {n p : ℕ} (hn0 : n ≠ 0) (hp : Nat.Prime p) (hpdvd : p ∣ n)
    (hnotpow : ∀ s : ℕ, n ≠ p ^ s) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ q ≠ p := by
  have hp_mem : p ∈ n.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn0⟩
  by_contra hnone
  have hall : ∀ q : ℕ, q ∈ n.primeFactors → q = p := by
    intro q hq
    by_cases hqp : q = p
    · exact hqp
    · exfalso
      exact hnone ⟨q, Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq, hqp⟩
  have hsingle : n.primeFactors = {p} := by
    ext q
    constructor
    · intro hq
      simp [hall q hq]
    · intro hq
      simp at hq
      simpa [hq] using hp_mem
  have hpow := eq_prime_pow_of_primeFactors_singleton n p hn0 hsingle
  exact hnotpow _ hpow

private lemma primeFactors_260 : (260).primeFactors = {2, 5, 13} := by
  native_decide

private lemma primeFactors_1300 : (1300).primeFactors = {2, 5, 13} := by
  native_decide

private lemma primeFactors_3380 : (3380).primeFactors = {2, 5, 13} := by
  native_decide

private lemma divisors_card_260 : (260).divisors.card = 12 := by
  native_decide

private lemma divisors_card_1300 : (1300).divisors.card = 18 := by
  native_decide

private lemma divisors_card_3380 : (3380).divisors.card = 18 := by
  native_decide

private lemma divisors_card_16900 : (16900).divisors.card = 27 := by
  native_decide

private lemma no_solution_260_20_pow5 (N s : ℕ) :
    2520 * N ≠ 20 + 260 * 5 ^ s := by
  intro h
  have h126 : 126 * N = 1 + 13 * 5 ^ s := by omega
  have hz : (((126 * N : ℕ) : ZMod 126)) = (((1 + 13 * 5 ^ s : ℕ) : ZMod 126)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 126)) h126
  have hsdecomp : s = 6 * (s / 6) + s % 6 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  have h15625 : (15625 : ZMod 126) = 1 := by native_decide
  simp [h15625] at hz
  have h126zero : ((126 : ℕ) : ZMod 126) = 0 := by native_decide
  have hzL : (((126 * N : ℕ) : ZMod 126)) = 0 := by
    rw [Nat.cast_mul, h126zero, zero_mul]
  have hzR : (((1 + 13 * 5 ^ (s % 6) : ℕ) : ZMod 126)) = 0 := by
    calc
      (((1 + 13 * 5 ^ (s % 6) : ℕ) : ZMod 126)) = (((126 * N : ℕ) : ZMod 126)) := by
        simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((1 + 13 * 5 ^ (s % 6) : ℕ) : ZMod 126)) ≠ 0 := by
    have hmod : s % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 6 <;> native_decide
  exact hbad hzR

private lemma no_solution_260_20_pow13 (N s : ℕ) :
    2520 * N ≠ 20 + 260 * 13 ^ s := by
  intro h
  have h126 : 126 * N = 1 + 13 * 13 ^ s := by omega
  have hz : (((126 * N : ℕ) : ZMod 9)) = (((1 + 13 * 13 ^ s : ℕ) : ZMod 9)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 9)) h126
  have hsdecomp : s = 3 * (s / 3) + s % 3 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  have h2197 : (2197 : ZMod 9) = 1 := by native_decide
  simp [h2197] at hz
  have h126zero : ((126 : ℕ) : ZMod 9) = 0 := by native_decide
  have hzL : (((126 * N : ℕ) : ZMod 9)) = 0 := by
    rw [Nat.cast_mul, h126zero, zero_mul]
  have hzR : (((1 + 13 * 13 ^ (s % 3) : ℕ) : ZMod 9)) = 0 := by
    calc
      (((1 + 13 * 13 ^ (s % 3) : ℕ) : ZMod 9)) = (((126 * N : ℕ) : ZMod 9)) := by
        simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((1 + 13 * 13 ^ (s % 3) : ℕ) : ZMod 9)) ≠ 0 := by
    have hmod : s % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 3 <;> native_decide
  exact hbad hzR

/-- The load-bearing `ble1` family `(g_exact, k) = (260, 20)` closes directly
at the full-value level. -/
theorem family_260_20_closes (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues26020) :
    ¬ IsErdos647 (2520 * N) := by
  intro hE
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 20) / 260
  let eval := 447678 * q + b
  let m := 2520 * N - 20

  have hr_div : 260 ∣ 2520 * r - 20 := residue26020_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue26020_b_ge_two r (by simpa [r] using hr)
  have hb_odd : Odd b := residue26020_b_odd r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 20 = 260 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 260 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 260 * 447678 := by native_decide
    calc
      m = 2520 * N - 20 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 20 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 20) := by
        rw [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (260 * 447678) * q + 260 * b := by rw [hmul, hb_eq]
      _ = 260 * eval := by
        dsimp [eval]
        ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 55 ≤ N := by
      have hr_ge : 55 ≤ r := residue26020_ge55 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  have h_eval_odd : Odd eval := by
    rcases hb_odd with ⟨t, ht⟩
    refine ⟨223839 * q + t, ?_⟩
    dsimp [eval]
    omega

  have h2not_eval : ¬ 2 ∣ eval := by
    intro h2
    rcases h_eval_odd with ⟨t, ht⟩
    rcases h2 with ⟨u, hu⟩
    omega

  have h_tau : m.divisors.card ≤ 22 := by
    dsimp [m]
    have h20lt : 20 < 2520 * N := by
      have hN_ge : 55 ≤ N := by
        have hr_ge : 55 ≤ r := residue26020_ge55 r (by simpa [r] using hr)
        have : r ≤ N := by
          dsimp [r]
          exact Nat.mod_le _ _
        omega
      omega
    simpa using tau_bound_at_k N 20 hE (by decide) h20lt

  by_cases h5 : 5 ∣ eval
  · by_cases h13 : 13 ∣ eval
    · have h65 : 65 ∣ eval := by
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 5 13) h5 h13
      have h16900 : 16900 ∣ m := by
        rcases h65 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]
        ring
      have hmono := Bridge2.Nat.divisors_card_le_of_dvd h16900 hm_ne
      rw [divisors_card_16900] at hmono
      omega
    · have hnotpow5 : ∀ s : ℕ, eval ≠ 5 ^ s := by
        intro s hs
        have hpow : 2520 * N = 20 + 260 * 5 ^ s := by
          omega
        exact no_solution_260_20_pow5 N s hpow
      obtain ⟨p, hp, hpdvd_eval, hp_ne_5⟩ :=
        exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 5) h5 hnotpow5
      have hp_notin_1300 : p ∉ (1300).primeFactors := by
        rw [primeFactors_1300]
        intro hpin
        simp at hpin
        rcases hpin with rfl | rfl | rfl
        · exact h2not_eval hpdvd_eval
        · exact hp_ne_5 rfl
        · exact h13 hpdvd_eval
      have hcop : Nat.Coprime p 1300 := coprime_of_prime_notin_primeFactors (by decide : (1300 : ℕ) ≠ 0) hp hp_notin_1300
      have h1300 : 1300 ∣ m := by
        rcases h5 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]
        ring
      have hpdvd_m : p ∣ m := by
        rw [hm_eq]
        exact dvd_mul_of_dvd_right hpdvd_eval 260
      have hge := Bridge2.Nat.divisors_card_ge_two_mul h1300 hp hpdvd_m hcop hm_ne
      rw [divisors_card_1300] at hge
      omega
  · by_cases h13 : 13 ∣ eval
    · have hnotpow13 : ∀ s : ℕ, eval ≠ 13 ^ s := by
        intro s hs
        have hpow : 2520 * N = 20 + 260 * 13 ^ s := by
          omega
        exact no_solution_260_20_pow13 N s hpow
      obtain ⟨p, hp, hpdvd_eval, hp_ne_13⟩ :=
        exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 13) h13 hnotpow13
      have hp_notin_3380 : p ∉ (3380).primeFactors := by
        rw [primeFactors_3380]
        intro hpin
        simp at hpin
        rcases hpin with rfl | rfl | rfl
        · exact h2not_eval hpdvd_eval
        · exact h5 hpdvd_eval
        · exact hp_ne_13 rfl
      have hcop : Nat.Coprime p 3380 := coprime_of_prime_notin_primeFactors (by decide : (3380 : ℕ) ≠ 0) hp hp_notin_3380
      have h3380 : 3380 ∣ m := by
        rcases h13 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]
        ring
      have hpdvd_m : p ∣ m := by
        rw [hm_eq]
        exact dvd_mul_of_dvd_right hpdvd_eval 260
      have hge := Bridge2.Nat.divisors_card_ge_two_mul h3380 hp hpdvd_m hcop hm_ne
      rw [divisors_card_3380] at hge
      omega
    · have heval_ne_one : eval ≠ 1 := by omega
      obtain ⟨p, hp, hpdvd_eval⟩ := Nat.exists_prime_and_dvd heval_ne_one
      have hp_notin_260 : p ∉ (260).primeFactors := by
        rw [primeFactors_260]
        intro hpin
        simp at hpin
        rcases hpin with rfl | rfl | rfl
        · exact h2not_eval hpdvd_eval
        · exact h5 hpdvd_eval
        · exact h13 hpdvd_eval
      have hcop : Nat.Coprime p 260 := coprime_of_prime_notin_primeFactors (by decide : (260 : ℕ) ≠ 0) hp hp_notin_260
      have h260 : 260 ∣ m := by
        exact ⟨eval, hm_eq⟩
      have hpdvd_m : p ∣ m := by
        rw [hm_eq]
        exact dvd_mul_of_dvd_right hpdvd_eval 260
      have hge := Bridge2.Nat.divisors_card_ge_two_mul h260 hp hpdvd_m hcop hm_ne
      rw [divisors_card_260] at hge
      omega

/-- The 2-residue `ble1` family with `g_exact = 3553`, `k = 11`. -/
def residues355311 : Finset ℕ := {9493, 41470}

private lemma residue355311_div (r : ℕ) (hr : r ∈ residues355311) :
    3553 ∣ 2520 * r - 11 := by
  native_decide +revert

private lemma residue355311_b_ge_two (r : ℕ) (hr : r ∈ residues355311) :
    2 ≤ (2520 * r - 11) / 3553 := by
  native_decide +revert

private lemma residue355311_ge9493 (r : ℕ) (hr : r ∈ residues355311) :
    9493 ≤ r := by
  native_decide +revert

private lemma primeFactors_3553 : (3553).primeFactors = {11, 17, 19} := by
  native_decide

private lemma primeFactors_39083 : (39083).primeFactors = {11, 17, 19} := by
  native_decide

private lemma primeFactors_60401 : (60401).primeFactors = {11, 17, 19} := by
  native_decide

private lemma primeFactors_67507 : (67507).primeFactors = {11, 17, 19} := by
  native_decide

private lemma divisors_card_3553 : (3553).divisors.card = 8 := by
  native_decide

private lemma divisors_card_39083 : (39083).divisors.card = 12 := by
  native_decide

private lemma divisors_card_60401 : (60401).divisors.card = 12 := by
  native_decide

private lemma divisors_card_67507 : (67507).divisors.card = 12 := by
  native_decide

private lemma divisors_card_664411 : (664411).divisors.card = 18 := by
  native_decide

private lemma divisors_card_742577 : (742577).divisors.card = 18 := by
  native_decide

private lemma divisors_card_1147619 : (1147619).divisors.card = 18 := by
  native_decide

private lemma no_solution_3553_11_pow11 (N s : ℕ) :
    2520 * N ≠ 11 + 3553 * 11 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((11 + 3553 * 11 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  have h121 : (121 : ZMod 8) = 1 := by native_decide
  simp [h121] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((11 + 3553 * 11 ^ (s % 2) : ℕ) : ZMod 8)) = 0 := by
    calc
      (((11 + 3553 * 11 ^ (s % 2) : ℕ) : ZMod 8)) = (((2520 * N : ℕ) : ZMod 8)) := by
        simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((11 + 3553 * 11 ^ (s % 2) : ℕ) : ZMod 8)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

private lemma no_solution_3553_11_pow17 (N s : ℕ) :
    2520 * N ≠ 11 + 3553 * 17 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((11 + 3553 * 17 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  have h289 : (289 : ZMod 8) = 1 := by native_decide
  simp [h289] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((11 + 3553 * 17 ^ (s % 2) : ℕ) : ZMod 8)) = 0 := by
    calc
      (((11 + 3553 * 17 ^ (s % 2) : ℕ) : ZMod 8)) = (((2520 * N : ℕ) : ZMod 8)) := by
        simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((11 + 3553 * 17 ^ (s % 2) : ℕ) : ZMod 8)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

private lemma no_solution_3553_11_pow19 (N s : ℕ) :
    2520 * N ≠ 11 + 3553 * 19 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((11 + 3553 * 19 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  have h361 : (361 : ZMod 8) = 1 := by native_decide
  simp [h361] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((11 + 3553 * 19 ^ (s % 2) : ℕ) : ZMod 8)) = 0 := by
    calc
      (((11 + 3553 * 19 ^ (s % 2) : ℕ) : ZMod 8)) = (((2520 * N : ℕ) : ZMod 8)) := by
        simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((11 + 3553 * 19 ^ (s % 2) : ℕ) : ZMod 8)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

/-- The 2-residue `ble1` family `(g_exact, k) = (3553, 11)` closes directly
at the full-value level. -/
theorem family_3553_11_closes (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues355311) :
    ¬ IsErdos647 (2520 * N) := by
  intro hE
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 11) / 3553
  let eval := 32760 * q + b
  let m := 2520 * N - 11

  have hr_div : 3553 ∣ 2520 * r - 11 := residue355311_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue355311_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 11 = 3553 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 3553 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 3553 * 32760 := by native_decide
    calc
      m = 2520 * N - 11 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 11 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 11) := by
        rw [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (3553 * 32760) * q + 3553 * b := by rw [hmul, hb_eq]
      _ = 3553 * eval := by
        dsimp [eval]
        ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 9493 ≤ N := by
      have hr_ge : 9493 ≤ r := residue355311_ge9493 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  have h_tau : m.divisors.card ≤ 13 := by
    dsimp [m]
    have h11lt : 11 < 2520 * N := by
      have hN_ge : 9493 ≤ N := by
        have hr_ge : 9493 ≤ r := residue355311_ge9493 r (by simpa [r] using hr)
        have : r ≤ N := by
          dsimp [r]
          exact Nat.mod_le _ _
        omega
      omega
    simpa using tau_bound_at_k N 11 hE (by decide) h11lt

  by_cases h11 : 11 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · have h664411 : 664411 ∣ m := by
        have h187 : 187 ∣ eval := by
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 11 17) h11 h17
        rcases h187 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]
        ring
      have hmono := Bridge2.Nat.divisors_card_le_of_dvd h664411 hm_ne
      rw [divisors_card_664411] at hmono
      omega
    · by_cases h19 : 19 ∣ eval
      · have h742577 : 742577 ∣ m := by
          have h209 : 209 ∣ eval := by
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 11 19) h11 h19
          rcases h209 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]
          ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h742577 hm_ne
        rw [divisors_card_742577] at hmono
        omega
      · have hnotpow11 : ∀ s : ℕ, eval ≠ 11 ^ s := by
          intro s hs
          have hpow : 2520 * N = 11 + 3553 * 11 ^ s := by
            omega
          exact no_solution_3553_11_pow11 N s hpow
        obtain ⟨p, hp, hpdvd_eval, hp_ne_11⟩ :=
          exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 11) h11 hnotpow11
        have hp_notin_39083 : p ∉ (39083).primeFactors := by
          rw [primeFactors_39083]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact hp_ne_11 rfl
          · exact h17 hpdvd_eval
          · exact h19 hpdvd_eval
        have hcop : Nat.Coprime p 39083 := coprime_of_prime_notin_primeFactors (by decide : (39083 : ℕ) ≠ 0) hp hp_notin_39083
        have h39083 : 39083 ∣ m := by
          rcases h11 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]
          ring
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 3553
        have hge := Bridge2.Nat.divisors_card_ge_two_mul h39083 hp hpdvd_m hcop hm_ne
        rw [divisors_card_39083] at hge
        omega
  · by_cases h17 : 17 ∣ eval
    · by_cases h19 : 19 ∣ eval
      · have h1147619 : 1147619 ∣ m := by
          have h323 : 323 ∣ eval := by
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 17 19) h17 h19
          rcases h323 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]
          ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1147619 hm_ne
        rw [divisors_card_1147619] at hmono
        omega
      · have hnotpow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
          intro s hs
          have hpow : 2520 * N = 11 + 3553 * 17 ^ s := by
            omega
          exact no_solution_3553_11_pow17 N s hpow
        obtain ⟨p, hp, hpdvd_eval, hp_ne_17⟩ :=
          exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 17) h17 hnotpow17
        have hp_notin_60401 : p ∉ (60401).primeFactors := by
          rw [primeFactors_60401]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h11 hpdvd_eval
          · exact hp_ne_17 rfl
          · exact h19 hpdvd_eval
        have hcop : Nat.Coprime p 60401 := coprime_of_prime_notin_primeFactors (by decide : (60401 : ℕ) ≠ 0) hp hp_notin_60401
        have h60401 : 60401 ∣ m := by
          rcases h17 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]
          ring
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 3553
        have hge := Bridge2.Nat.divisors_card_ge_two_mul h60401 hp hpdvd_m hcop hm_ne
        rw [divisors_card_60401] at hge
        omega
    · by_cases h19 : 19 ∣ eval
      · have hnotpow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
          intro s hs
          have hpow : 2520 * N = 11 + 3553 * 19 ^ s := by
            omega
          exact no_solution_3553_11_pow19 N s hpow
        obtain ⟨p, hp, hpdvd_eval, hp_ne_19⟩ :=
          exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 19) h19 hnotpow19
        have hp_notin_67507 : p ∉ (67507).primeFactors := by
          rw [primeFactors_67507]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h11 hpdvd_eval
          · exact h17 hpdvd_eval
          · exact hp_ne_19 rfl
        have hcop : Nat.Coprime p 67507 := coprime_of_prime_notin_primeFactors (by decide : (67507 : ℕ) ≠ 0) hp hp_notin_67507
        have h67507 : 67507 ∣ m := by
          rcases h19 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]
          ring
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 3553
        have hge := Bridge2.Nat.divisors_card_ge_two_mul h67507 hp hpdvd_m hcop hm_ne
        rw [divisors_card_67507] at hge
        omega
      · obtain ⟨p, hp, hpdvd_eval⟩ := Nat.exists_prime_and_dvd (by omega : eval ≠ 1)
        have hp_notin_3553 : p ∉ (3553).primeFactors := by
          rw [primeFactors_3553]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h11 hpdvd_eval
          · exact h17 hpdvd_eval
          · exact h19 hpdvd_eval
        have hcop : Nat.Coprime p 3553 := coprime_of_prime_notin_primeFactors (by decide : (3553 : ℕ) ≠ 0) hp hp_notin_3553
        have h3553 : 3553 ∣ m := by
          exact ⟨eval, hm_eq⟩
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 3553
        have hge := Bridge2.Nat.divisors_card_ge_two_mul h3553 hp hpdvd_m hcop hm_ne
        rw [divisors_card_3553] at hge
        omega

theorem no_erdos647_of_mem_residues26020 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ residues26020) :
    ¬ IsErdos647 (2520 * N) :=
  family_260_20_closes N hN

theorem no_erdos647_of_mem_residues3553_11 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ residues355311) :
    ¬ IsErdos647 (2520 * N) :=
  family_3553_11_closes N hN

def residues4199_13 : Finset ℕ :=
  Erdos647SingleOverlap_4199_13_draft.residues419913

def residues14535_45 : Finset ℕ :=
  Erdos647SingleOverlap_14535_45_draft.residues1453545

theorem no_erdos647_of_mem_residues4199_13 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ residues4199_13) :
    ¬ IsErdos647 (2520 * N) :=
  Erdos647SingleOverlap_4199_13_draft.family_4199_13_closes N hN

theorem no_erdos647_of_mem_residues14535_45 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ residues14535_45) :
    ¬ IsErdos647 (2520 * N) :=
  Erdos647SingleOverlap_14535_45_draft.family_14535_45_closes N hN

def singleOverlapResidues40 : Finset ℕ :=
  residues26020 ∪ residues355311

def singleOverlapResidues42 : Finset ℕ :=
  singleOverlapResidues40 ∪ residues4199_13 ∪ residues14535_45

theorem no_erdos647_of_mem_singleOverlapResidues40 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ singleOverlapResidues40) :
    ¬ IsErdos647 (2520 * N) := by
  simp only [singleOverlapResidues40, Finset.mem_union] at hN
  rcases hN with hN | hN
  · exact no_erdos647_of_mem_residues26020 N hN
  · exact no_erdos647_of_mem_residues3553_11 N hN

theorem no_erdos647_of_mem_singleOverlapResidues42 (N : ℕ)
    (hN : N % Erdos647SieveCertificate.M ∈ singleOverlapResidues42) :
    ¬ IsErdos647 (2520 * N) := by
  have hN' :
      N % Erdos647SieveCertificate.M ∈ singleOverlapResidues40 ∨
      N % Erdos647SieveCertificate.M ∈ residues4199_13 ∨
      N % Erdos647SieveCertificate.M ∈ residues14535_45 := by
    simpa [singleOverlapResidues42, Finset.mem_union, or_assoc] using hN
  rcases hN' with hN40 | hNrest
  · exact no_erdos647_of_mem_singleOverlapResidues40 N hN40
  · rcases hNrest with hN4199 | hN14535
    · exact no_erdos647_of_mem_residues4199_13 N hN4199
    · exact no_erdos647_of_mem_residues14535_45 N hN14535

theorem singleOverlapResidues40_card : singleOverlapResidues40.card = 40 := by
  native_decide

theorem singleOverlapResidues42_card : singleOverlapResidues42.card = 42 := by
  native_decide

end Erdos647SingleOverlapClosure
