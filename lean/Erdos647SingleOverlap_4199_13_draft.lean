import Mathlib
import Bridge2
import Erdos647BridgeV1
import Erdos647SieveCertificate
import Erdos647ValuationCore
import ShapeDecomposition

/-!
# Single-overlap closure: family `(g_exact, k) = (4199, 13)`

DRAFT — not yet wired into the main partition. This file proves the
1-residue family `(4199, 13)`, completing one of the two unformalized
single-overlap families from the Stage-1A rollback state.

Structure: mirrors `family_3553_11_closes` in
`Erdos647SingleOverlapClosure.lean`. The novelty is the **Case B
sub-branch at p = 13**: the equation `2520*N = 13 + 4199 * 13^s` has
solutions for some `s` (smallest is `s = 9`), but every solution forces
`s ≥ 2`, which makes `τ(m) ≥ 16 > 15 = k+2`, contradicting the divisor
budget.
-/

namespace Erdos647SingleOverlap_4199_13_draft

open Erdos647BridgeV1
open Erdos647ValuationCore

private lemma natCard_div_eq_card (m : ℕ) :
    Nat.card (Nat.divisors m) = (Nat.divisors m).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

-- Local copy of a helper also present in `Erdos647SingleOverlapClosure`. Keep
-- the copy here for standalone compilation; delete at merge time.
private lemma exists_prime_ne_of_not_primepow
    {n p : ℕ} (hn0 : n ≠ 0) (hp : Nat.Prime p) (hpdvd : p ∣ n)
    (hnotpow : ∀ s : ℕ, n ≠ p ^ s) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ q ≠ p := by
  have hp_mem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn0⟩
  by_contra hnone
  have hall : ∀ q : ℕ, q ∈ n.primeFactors → q = p := by
    intro q hq
    by_cases hqp : q = p
    · exact hqp
    · exfalso
      exact hnone ⟨q, Nat.prime_of_mem_primeFactors hq,
        Nat.dvd_of_mem_primeFactors hq, hqp⟩
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

/-- The 1-residue `ble1` family with `g_exact = 4199`, `k = 13`. -/
def residues419913 : Finset ℕ := {40612}

private lemma residue419913_div (r : ℕ) (hr : r ∈ residues419913) :
    4199 ∣ 2520 * r - 13 := by
  native_decide +revert

private lemma residue419913_b_ge_two (r : ℕ) (hr : r ∈ residues419913) :
    2 ≤ (2520 * r - 13) / 4199 := by
  native_decide +revert

private lemma residue419913_ge40612 (r : ℕ) (hr : r ∈ residues419913) :
    40612 ≤ r := by
  native_decide +revert

-- prime-factorisation helpers
private lemma primeFactors_4199 : (4199).primeFactors = {13, 17, 19} := by
  native_decide

private lemma primeFactors_54587 : (54587).primeFactors = {13, 17, 19} := by
  native_decide

private lemma primeFactors_71383 : (71383).primeFactors = {13, 17, 19} := by
  native_decide

private lemma primeFactors_79781 : (79781).primeFactors = {13, 17, 19} := by
  native_decide

-- divisor-count helpers (k+2 = 15 budget)
private lemma divisors_card_4199 : (4199).divisors.card = 8 := by
  native_decide

private lemma divisors_card_54587 : (54587).divisors.card = 12 := by
  native_decide

private lemma divisors_card_71383 : (71383).divisors.card = 12 := by
  native_decide

private lemma divisors_card_79781 : (79781).divisors.card = 12 := by
  native_decide

private lemma divisors_card_927979 : (927979).divisors.card = 18 := by
  native_decide

private lemma divisors_card_1037153 : (1037153).divisors.card = 18 := by
  native_decide

private lemma divisors_card_1356277 : (1356277).divisors.card = 18 := by
  native_decide

/-- Case B helper: τ-value at `s = 2` for the pure 13-power branch. -/
private lemma divisors_card_709631 : (709631).divisors.card = 16 := by
  native_decide
  -- 709631 = 4199 · 169 = 13^3 · 17 · 19, so τ = 4·2·2 = 16

-- Case A pow-contradictions
-- p = 17 (mod 8, ord 1, residues {4})
private lemma no_solution_4199_13_pow17 (N s : ℕ) :
    2520 * N ≠ 13 + 4199 * 17 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((13 + 4199 * 17 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  -- 17 ≡ 1 (mod 8), so 17^s ≡ 1 (mod 8) for all s
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  -- (13 + 4199 · 17^s) mod 8 = (5 + 7 · 1) mod 8 = 12 mod 8 = 4
  -- So we need 0 = 4 in ZMod 8, contradiction
  have h17 : (17 : ZMod 8) = 1 := by native_decide
  have hcast : ((17 ^ s : ℕ) : ZMod 8) = 1 := by
    induction s with
    | zero => simp
    | succ n _ => simp [pow_succ, Nat.cast_mul, h17]
  have hzR : (((13 + 4199 * 17 ^ s : ℕ) : ZMod 8)) = 4 := by
    calc
      (((13 + 4199 * 17 ^ s : ℕ) : ZMod 8))
          = ((13 : ZMod 8) + (4199 : ZMod 8) * (((17 ^ s : ℕ) : ZMod 8))) := by
              simp
      _ = 4 := by rw [hcast]; native_decide
  have : (0 : ZMod 8) = 4 := by rw [← hzL, hz, hzR]
  exact absurd this (by native_decide)

-- p = 19 (mod 5, ord 2, residues {2, 4})
private lemma no_solution_4199_13_pow19 (N s : ℕ) :
    2520 * N ≠ 13 + 4199 * 19 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 5)) = (((13 + 4199 * 19 ^ s : ℕ) : ZMod 5)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 5)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  -- 19^2 = 361 ≡ 1 (mod 5)
  have h361 : (361 : ZMod 5) = 1 := by native_decide
  simp [h361] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 5) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 5)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((13 + 4199 * 19 ^ (s % 2) : ℕ) : ZMod 5)) = 0 := by
    calc
      (((13 + 4199 * 19 ^ (s % 2) : ℕ) : ZMod 5))
          = (((2520 * N : ℕ) : ZMod 5)) := by simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((13 + 4199 * 19 ^ (s % 2) : ℕ) : ZMod 5)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

-- Case B at p = 13: small-s exclusion (s ≤ 1)
private lemma no_solution_4199_13_pow13_zero (N : ℕ) :
    2520 * N ≠ 13 + 4199 * 13 ^ 0 := by
  intro h
  -- 13 + 4199*1 = 4212; 4212 mod 2520 = 1692 ≠ 0
  have : (((2520 * N : ℕ) : ZMod 2520)) = ((4212 : ℕ) : ZMod 2520) := by
    have : 13 + 4199 * 13 ^ 0 = 4212 := by norm_num
    rw [this] at h
    simpa using congrArg (fun n : ℕ => (n : ZMod 2520)) h
  have h2520 : ((2520 : ℕ) : ZMod 2520) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 2520)) = 0 := by
    rw [Nat.cast_mul, h2520, zero_mul]
  have hzR : ((4212 : ℕ) : ZMod 2520) ≠ 0 := by native_decide
  exact hzR (by rw [← this, hzL])

private lemma no_solution_4199_13_pow13_one (N : ℕ) :
    2520 * N ≠ 13 + 4199 * 13 ^ 1 := by
  intro h
  -- 13 + 4199*13 = 54600; 54600 mod 2520 = 1680 ≠ 0
  have : (((2520 * N : ℕ) : ZMod 2520)) = ((54600 : ℕ) : ZMod 2520) := by
    have : 13 + 4199 * 13 ^ 1 = 54600 := by norm_num
    rw [this] at h
    simpa using congrArg (fun n : ℕ => (n : ZMod 2520)) h
  have h2520 : ((2520 : ℕ) : ZMod 2520) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 2520)) = 0 := by
    rw [Nat.cast_mul, h2520, zero_mul]
  have hzR : ((54600 : ℕ) : ZMod 2520) ≠ 0 := by native_decide
  exact hzR (by rw [← this, hzL])

/-- The single residue family `(g_exact, k) = (4199, 13)` closes directly
at the full-value level. -/
theorem family_4199_13_closes (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues419913) :
    ¬ IsErdos647 (2520 * N) := by
  intro hE
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 13) / 4199
  let eval := 27720 * q + b
  let m := 2520 * N - 13

  have hr_div : 4199 ∣ 2520 * r - 13 := residue419913_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue419913_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 13 = 4199 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 4199 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 4199 * 27720 := by native_decide
    calc
      m = 2520 * N - 13 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 13 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 13) := by
        rw [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (4199 * 27720) * q + 4199 * b := by rw [hmul, hb_eq]
      _ = 4199 * eval := by
        dsimp [eval]
        ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 40612 ≤ N := by
      have hr_ge : 40612 ≤ r := residue419913_ge40612 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]; exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]; omega

  have h_tau : m.divisors.card ≤ 15 := by
    dsimp [m]
    have h13lt : 13 < 2520 * N := by
      have hN_ge : 40612 ≤ N := by
        have hr_ge : 40612 ≤ r := residue419913_ge40612 r (by simpa [r] using hr)
        have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
        omega
      omega
    simpa using tau_bound_at_k N 13 hE (by decide) h13lt

  by_cases h13 : 13 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · -- pair (13, 17): use 927979 = 4199 · 221
      have h927979 : 927979 ∣ m := by
        have h221 : 221 ∣ eval :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 13 17) h13 h17
        rcases h221 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]; ring
      have hmono := Bridge2.Nat.divisors_card_le_of_dvd h927979 hm_ne
      rw [divisors_card_927979] at hmono
      omega
    · by_cases h19 : 19 ∣ eval
      · -- pair (13, 19): use 1037153 = 4199 · 247
        have h1037153 : 1037153 ∣ m := by
          have h247 : 247 ∣ eval :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 13 19) h13 h19
          rcases h247 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1037153 hm_ne
        rw [divisors_card_1037153] at hmono
        omega
      · -- only 13 divides eval — Case B at p = 13
        -- Either eval is a pure power of 13 (handled by τ-forcing), or eval has
        -- a prime factor outside {13, 17, 19} (handled by coprime partner).
        by_cases hpow : ∀ s : ℕ, eval ≠ 13 ^ s
        · -- eval has a prime outside {13, 17, 19}; coprime partner gives τ ≥ 24 > 15
          obtain ⟨p, hp, hpdvd_eval, hp_ne_13⟩ :=
            exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 13) h13 hpow
          have hp_notin_54587 : p ∉ (54587).primeFactors := by
            rw [primeFactors_54587]
            intro hpin
            simp at hpin
            rcases hpin with rfl | rfl | rfl
            · exact hp_ne_13 rfl
            · exact h17 hpdvd_eval
            · exact h19 hpdvd_eval
          have hcop : Nat.Coprime p 54587 :=
            coprime_of_prime_notin_primeFactors (by decide : (54587 : ℕ) ≠ 0) hp hp_notin_54587
          have h54587 : 54587 ∣ m := by
            rcases h13 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hpdvd_m : p ∣ m := by
            rw [hm_eq]
            exact dvd_mul_of_dvd_right hpdvd_eval 4199
          have hge :=
            Bridge2.Nat.divisors_card_ge_two_mul h54587 hp hpdvd_m hcop hm_ne
          rw [divisors_card_54587] at hge
          omega
        · -- eval = 13^s for some s; CASE B
          push_neg at hpow
          obtain ⟨s, hs⟩ := hpow
          -- exclude s = 0 (eval = 1 contradicts h_eval_gt_one)
          -- exclude s = 1 (modular impossibility)
          -- for s ≥ 2: 13^3 · 17 · 19 = 709631 divides m, τ = 16 > 15
          rcases Nat.lt_or_ge s 2 with hs_lt | hs_ge
          · interval_cases s
            · -- s = 0: eval = 1, contradicts h_eval_gt_one
              simp at hs; omega
            · -- s = 1: eval = 13, so m = 4199*13 = 54587, hence 2520*N = 54600
              have heq : 2520 * N = 13 + 4199 * 13 ^ 1 := by
                have : m = 4199 * 13 := by rw [hm_eq, hs]; ring
                dsimp [m] at this
                have hN_ge : 40612 ≤ N := by
                  have hr_ge : 40612 ≤ r := residue419913_ge40612 r (by simpa [r] using hr)
                  have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
                  omega
                omega
              exact no_solution_4199_13_pow13_one N heq
          · -- s ≥ 2: 709631 | m, τ ≥ 16, contradicts h_tau ≤ 15
            have h169 : 169 ∣ eval := by
              rw [hs]
              have hs2 : 2 ≤ s := by omega
              have hs_eq : s = 2 + (s - 2) := by omega
              rw [hs_eq, pow_add, pow_two]
              exact dvd_mul_right _ _
            have h709631 : 709631 ∣ m := by
              -- 709631 = 4199 · 169
              rcases h169 with ⟨t, ht⟩
              refine ⟨t, ?_⟩
              rw [hm_eq, ht]; ring
            have hmono := Bridge2.Nat.divisors_card_le_of_dvd h709631 hm_ne
            rw [divisors_card_709631] at hmono
            omega
  · by_cases h17 : 17 ∣ eval
    · by_cases h19 : 19 ∣ eval
      · -- pair (17, 19): use 1356277 = 4199 · 323
        have h1356277 : 1356277 ∣ m := by
          have h323 : 323 ∣ eval :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 17 19) h17 h19
          rcases h323 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1356277 hm_ne
        rw [divisors_card_1356277] at hmono
        omega
      · -- only 17 divides eval — Case A at p = 17
        have hnotpow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
          intro s hs
          have hpow : 2520 * N = 13 + 4199 * 17 ^ s := by
            have : m = 4199 * 17 ^ s := by rw [hm_eq, hs]
            dsimp [m] at this
            have hN_ge : 40612 ≤ N := by
              have hr_ge : 40612 ≤ r := residue419913_ge40612 r (by simpa [r] using hr)
              have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
              omega
            omega
          exact no_solution_4199_13_pow17 N s hpow
        obtain ⟨p, hp, hpdvd_eval, hp_ne_17⟩ :=
          exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 17) h17 hnotpow17
        have hp_notin_71383 : p ∉ (71383).primeFactors := by
          rw [primeFactors_71383]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h13 hpdvd_eval
          · exact hp_ne_17 rfl
          · exact h19 hpdvd_eval
        have hcop : Nat.Coprime p 71383 :=
          coprime_of_prime_notin_primeFactors (by decide : (71383 : ℕ) ≠ 0) hp hp_notin_71383
        have h71383 : 71383 ∣ m := by
          rcases h17 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 4199
        have hge :=
          Bridge2.Nat.divisors_card_ge_two_mul h71383 hp hpdvd_m hcop hm_ne
        rw [divisors_card_71383] at hge
        omega
    · by_cases h19 : 19 ∣ eval
      · -- only 19 divides eval — Case A at p = 19
        have hnotpow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
          intro s hs
          have hpow : 2520 * N = 13 + 4199 * 19 ^ s := by
            have : m = 4199 * 19 ^ s := by rw [hm_eq, hs]
            dsimp [m] at this
            have hN_ge : 40612 ≤ N := by
              have hr_ge : 40612 ≤ r := residue419913_ge40612 r (by simpa [r] using hr)
              have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
              omega
            omega
          exact no_solution_4199_13_pow19 N s hpow
        obtain ⟨p, hp, hpdvd_eval, hp_ne_19⟩ :=
          exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 19) h19 hnotpow19
        have hp_notin_79781 : p ∉ (79781).primeFactors := by
          rw [primeFactors_79781]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h13 hpdvd_eval
          · exact h17 hpdvd_eval
          · exact hp_ne_19 rfl
        have hcop : Nat.Coprime p 79781 :=
          coprime_of_prime_notin_primeFactors (by decide : (79781 : ℕ) ≠ 0) hp hp_notin_79781
        have h79781 : 79781 ∣ m := by
          rcases h19 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 4199
        have hge :=
          Bridge2.Nat.divisors_card_ge_two_mul h79781 hp hpdvd_m hcop hm_ne
        rw [divisors_card_79781] at hge
        omega
      · -- no prime of g divides eval — coprime partner against 4199
        obtain ⟨p, hp, hpdvd_eval⟩ := Nat.exists_prime_and_dvd (by omega : eval ≠ 1)
        have hp_notin_4199 : p ∉ (4199).primeFactors := by
          rw [primeFactors_4199]
          intro hpin
          simp at hpin
          rcases hpin with rfl | rfl | rfl
          · exact h13 hpdvd_eval
          · exact h17 hpdvd_eval
          · exact h19 hpdvd_eval
        have hcop : Nat.Coprime p 4199 :=
          coprime_of_prime_notin_primeFactors (by decide : (4199 : ℕ) ≠ 0) hp hp_notin_4199
        have h4199 : 4199 ∣ m := ⟨eval, hm_eq⟩
        have hpdvd_m : p ∣ m := by
          rw [hm_eq]
          exact dvd_mul_of_dvd_right hpdvd_eval 4199
        have hge :=
          Bridge2.Nat.divisors_card_ge_two_mul h4199 hp hpdvd_m hcop hm_ne
        rw [divisors_card_4199] at hge
        omega

-- Note: the Case B "exists_prime_ne_of_not_primepow" helper used above is
-- the same one already in Erdos647SingleOverlapClosure. When merging,
-- delete the local copy and import it.
-- The same applies to `coprime_of_prime_notin_primeFactors` and
-- `tau_bound_at_k`, which exist in Erdos647ValuationCore.

end Erdos647SingleOverlap_4199_13_draft
