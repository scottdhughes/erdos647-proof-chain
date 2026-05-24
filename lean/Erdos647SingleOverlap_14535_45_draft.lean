import Mathlib
import Bridge2
import Erdos647BridgeV1
import Erdos647SieveCertificate
import Erdos647ValuationCore
import ShapeDecomposition

/-!
# Single-overlap closure: family `(g_exact, k) = (14535, 45)`

DRAFT — not yet wired into the main partition. This file proves the
1-residue family `(14535, 45)`, completing the second of the two
unformalized single-overlap families from the Stage-1A rollback state.

Structure: mirrors `family_3553_11_closes` in
`Erdos647SingleOverlapClosure.lean`, extended to four `g`-primes
`{3, 5, 17, 19}`. The case split has 11 leaves:

  * 6 pair leaves:  `(3,5), (3,17), (3,19), (5,17), (5,19), (17,19)`
  * 3 Case-A leaves (pure p-power, ruled out mod 8):  p = 3, 17, 19
  * 1 Case-B leaf (pure p-power, ruled out by τ-forcing):  p = 5
  * 1 empty leaf (no g-prime divides eval)

Case B at `p = 5` uses divisor monotonicity to
  `363375 = 3^2 · 5^3 · 17 · 19`,
which has `τ = 48 > 47 = k + 2 = budget`, contradicting the full-value
divisor bound at shift `k = 45`.
-/

namespace Erdos647SingleOverlap_14535_45_draft

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

/-- The 1-residue `ble1` family with `g_exact = 14535`, `k = 45`. -/
def residues1453545 : Finset ℕ := {26884}

private lemma residue1453545_div (r : ℕ) (hr : r ∈ residues1453545) :
    14535 ∣ 2520 * r - 45 := by
  native_decide +revert

private lemma residue1453545_b_ge_two (r : ℕ) (hr : r ∈ residues1453545) :
    2 ≤ (2520 * r - 45) / 14535 := by
  native_decide +revert

private lemma residue1453545_ge26884 (r : ℕ) (hr : r ∈ residues1453545) :
    26884 ≤ r := by
  native_decide +revert

-- prime-factorisation helpers
private lemma primeFactors_14535 : (14535).primeFactors = {3, 5, 17, 19} := by
  native_decide

private lemma primeFactors_43605 : (43605).primeFactors = {3, 5, 17, 19} := by
  native_decide

private lemma primeFactors_72675 : (72675).primeFactors = {3, 5, 17, 19} := by
  native_decide

private lemma primeFactors_247095 : (247095).primeFactors = {3, 5, 17, 19} := by
  native_decide

private lemma primeFactors_276165 : (276165).primeFactors = {3, 5, 17, 19} := by
  native_decide

-- divisor-count helpers (k + 2 = 47 budget)

-- g alone (no g-prime in eval)
private lemma divisors_card_14535 : (14535).divisors.card = 24 := by
  native_decide

-- g · p : used by Case-A and Case-B "single prime divides" branches via coprime partner
private lemma divisors_card_43605 : (43605).divisors.card = 32 := by
  native_decide

private lemma divisors_card_72675 : (72675).divisors.card = 36 := by
  native_decide

private lemma divisors_card_247095 : (247095).divisors.card = 36 := by
  native_decide

private lemma divisors_card_276165 : (276165).divisors.card = 36 := by
  native_decide

-- g · (pair) : used by pair leaves
private lemma divisors_card_218025 : (218025).divisors.card = 48 := by
  native_decide  -- g · 15 = 3^3 · 5^2 · 17 · 19

private lemma divisors_card_741285 : (741285).divisors.card = 48 := by
  native_decide  -- g · 51 = 3^3 · 5 · 17^2 · 19

private lemma divisors_card_828495 : (828495).divisors.card = 48 := by
  native_decide  -- g · 57 = 3^3 · 5 · 17 · 19^2

private lemma divisors_card_1235475 : (1235475).divisors.card = 54 := by
  native_decide  -- g · 85 = 3^2 · 5^2 · 17^2 · 19

private lemma divisors_card_1380825 : (1380825).divisors.card = 54 := by
  native_decide  -- g · 95 = 3^2 · 5^2 · 17 · 19^2

private lemma divisors_card_4694805 : (4694805).divisors.card = 54 := by
  native_decide  -- g · 323 = 3^2 · 5 · 17^2 · 19^2

-- Case B helper: τ-value at `s = 2` for the pure 5-power branch.
private lemma divisors_card_363375 : (363375).divisors.card = 48 := by
  native_decide
  -- 363375 = 14535 · 25 = 3^2 · 5^3 · 17 · 19, so τ = 3·4·2·2 = 48 > 47

-- Case A pow-contradictions (all mod 8, since 14535 ≡ 7 (mod 8) and 45 ≡ 5 (mod 8))

-- p = 3, mod 8, ord 2, residues {2, 4}, never 0
private lemma no_solution_14535_45_pow3 (N s : ℕ) :
    2520 * N ≠ 45 + 14535 * 3 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((45 + 14535 * 3 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  -- 3^2 = 9 ≡ 1 (mod 8)
  have h9 : (9 : ZMod 8) = 1 := by native_decide
  simp [h9] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((45 + 14535 * 3 ^ (s % 2) : ℕ) : ZMod 8)) = 0 := by
    calc
      (((45 + 14535 * 3 ^ (s % 2) : ℕ) : ZMod 8))
          = (((2520 * N : ℕ) : ZMod 8)) := by simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((45 + 14535 * 3 ^ (s % 2) : ℕ) : ZMod 8)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

-- p = 17, mod 8, ord 1, residues {4}, never 0
private lemma no_solution_14535_45_pow17 (N s : ℕ) :
    2520 * N ≠ 45 + 14535 * 17 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((45 + 14535 * 17 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  -- 17 ≡ 1 (mod 8), so 17^s ≡ 1
  have h17 : (17 : ZMod 8) = 1 := by native_decide
  have hcast : ((17 ^ s : ℕ) : ZMod 8) = 1 := by
    induction s with
    | zero => simp
    | succ n _ => simp [pow_succ, Nat.cast_mul, h17]
  have hzR : (((45 + 14535 * 17 ^ s : ℕ) : ZMod 8)) = 4 := by
    calc
      (((45 + 14535 * 17 ^ s : ℕ) : ZMod 8))
          = ((45 : ZMod 8) + (14535 : ZMod 8) * (((17 ^ s : ℕ) : ZMod 8))) := by
              simp
      _ = 4 := by rw [hcast]; native_decide
  have : (0 : ZMod 8) = 4 := by rw [← hzL, hz, hzR]
  exact absurd this (by native_decide)

-- p = 19, mod 8, ord 2, residues {2, 4}, never 0
private lemma no_solution_14535_45_pow19 (N s : ℕ) :
    2520 * N ≠ 45 + 14535 * 19 ^ s := by
  intro h
  have hz : (((2520 * N : ℕ) : ZMod 8)) = (((45 + 14535 * 19 ^ s : ℕ) : ZMod 8)) := by
    simpa using congrArg (fun n : ℕ => (n : ZMod 8)) h
  have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
  rw [hsdecomp, pow_add, pow_mul] at hz
  -- 19^2 = 361 ≡ 1 (mod 8)
  have h361 : (361 : ZMod 8) = 1 := by native_decide
  simp [h361] at hz
  have h2520zero : ((2520 : ℕ) : ZMod 8) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 8)) = 0 := by
    rw [Nat.cast_mul, h2520zero, zero_mul]
  have hzR : (((45 + 14535 * 19 ^ (s % 2) : ℕ) : ZMod 8)) = 0 := by
    calc
      (((45 + 14535 * 19 ^ (s % 2) : ℕ) : ZMod 8))
          = (((2520 * N : ℕ) : ZMod 8)) := by simpa using hz.symm
      _ = 0 := hzL
  have hbad : (((45 + 14535 * 19 ^ (s % 2) : ℕ) : ZMod 8)) ≠ 0 := by
    have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases hsmod : s % 2 <;> native_decide
  exact hbad hzR

-- Case B at p = 5: small-s exclusion (s ≤ 1) via ZMod 2520

private lemma no_solution_14535_45_pow5_zero (N : ℕ) :
    2520 * N ≠ 45 + 14535 * 5 ^ 0 := by
  intro h
  -- 45 + 14535*1 = 14580; 14580 mod 2520 = 1980 ≠ 0
  have : (((2520 * N : ℕ) : ZMod 2520)) = ((14580 : ℕ) : ZMod 2520) := by
    have : 45 + 14535 * 5 ^ 0 = 14580 := by norm_num
    rw [this] at h
    simpa using congrArg (fun n : ℕ => (n : ZMod 2520)) h
  have h2520 : ((2520 : ℕ) : ZMod 2520) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 2520)) = 0 := by
    rw [Nat.cast_mul, h2520, zero_mul]
  have hzR : ((14580 : ℕ) : ZMod 2520) ≠ 0 := by native_decide
  exact hzR (by rw [← this, hzL])

private lemma no_solution_14535_45_pow5_one (N : ℕ) :
    2520 * N ≠ 45 + 14535 * 5 ^ 1 := by
  intro h
  -- 45 + 14535*5 = 72720; 72720 mod 2520 = 2160 ≠ 0
  have : (((2520 * N : ℕ) : ZMod 2520)) = ((72720 : ℕ) : ZMod 2520) := by
    have : 45 + 14535 * 5 ^ 1 = 72720 := by norm_num
    rw [this] at h
    simpa using congrArg (fun n : ℕ => (n : ZMod 2520)) h
  have h2520 : ((2520 : ℕ) : ZMod 2520) = 0 := by native_decide
  have hzL : (((2520 * N : ℕ) : ZMod 2520)) = 0 := by
    rw [Nat.cast_mul, h2520, zero_mul]
  have hzR : ((72720 : ℕ) : ZMod 2520) ≠ 0 := by native_decide
  exact hzR (by rw [← this, hzL])

/-- The single residue family `(g_exact, k) = (14535, 45)` closes directly
at the full-value level. -/
theorem family_14535_45_closes (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues1453545) :
    ¬ IsErdos647 (2520 * N) := by
  intro hE
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 45) / 14535
  let eval := 8008 * q + b
  let m := 2520 * N - 45

  have hr_div : 14535 ∣ 2520 * r - 45 := residue1453545_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue1453545_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 45 = 14535 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 14535 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 14535 * 8008 := by native_decide
    calc
      m = 2520 * N - 45 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 45 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 45) := by
        rw [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (14535 * 8008) * q + 14535 * b := by rw [hmul, hb_eq]
      _ = 14535 * eval := by
        dsimp [eval]
        ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 26884 ≤ N := by
      have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]; exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]; omega

  have h_tau : m.divisors.card ≤ 47 := by
    dsimp [m]
    have h45lt : 45 < 2520 * N := by
      have hN_ge : 26884 ≤ N := by
        have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
        have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
        omega
      omega
    simpa using tau_bound_at_k N 45 hE (by decide) h45lt

  -- 11-way case split on which of {3, 5, 17, 19} divides eval
  by_cases h3 : 3 ∣ eval
  · -- 3 ∣ eval
    by_cases h5 : 5 ∣ eval
    · -- pair (3, 5): 218025 = 14535 · 15, τ = 48
      have h218025 : 218025 ∣ m := by
        have h15 : 15 ∣ eval :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 5) h3 h5
        rcases h15 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hm_eq, ht]; ring
      have hmono := Bridge2.Nat.divisors_card_le_of_dvd h218025 hm_ne
      rw [divisors_card_218025] at hmono
      omega
    · by_cases h17 : 17 ∣ eval
      · -- pair (3, 17): 741285 = 14535 · 51, τ = 48
        have h741285 : 741285 ∣ m := by
          have h51 : 51 ∣ eval :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 17) h3 h17
          rcases h51 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h741285 hm_ne
        rw [divisors_card_741285] at hmono
        omega
      · by_cases h19 : 19 ∣ eval
        · -- pair (3, 19): 828495 = 14535 · 57, τ = 48
          have h828495 : 828495 ∣ m := by
            have h57 : 57 ∣ eval :=
              Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 19) h3 h19
            rcases h57 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hmono := Bridge2.Nat.divisors_card_le_of_dvd h828495 hm_ne
          rw [divisors_card_828495] at hmono
          omega
        · -- only 3 divides eval — Case A at p = 3
          have hnotpow3 : ∀ s : ℕ, eval ≠ 3 ^ s := by
            intro s hs
            have hpow : 2520 * N = 45 + 14535 * 3 ^ s := by
              have : m = 14535 * 3 ^ s := by rw [hm_eq, hs]
              dsimp [m] at this
              have hN_ge : 26884 ≤ N := by
                have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
                have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
                omega
              omega
            exact no_solution_14535_45_pow3 N s hpow
          obtain ⟨p, hp, hpdvd_eval, hp_ne_3⟩ :=
            exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 3) h3 hnotpow3
          have hp_notin_43605 : p ∉ (43605).primeFactors := by
            rw [primeFactors_43605]
            intro hpin
            simp at hpin
            rcases hpin with rfl | rfl | rfl | rfl
            · exact hp_ne_3 rfl
            · exact h5 hpdvd_eval
            · exact h17 hpdvd_eval
            · exact h19 hpdvd_eval
          have hcop : Nat.Coprime p 43605 :=
            coprime_of_prime_notin_primeFactors (by decide : (43605 : ℕ) ≠ 0) hp hp_notin_43605
          have h43605 : 43605 ∣ m := by
            rcases h3 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hpdvd_m : p ∣ m := by
            rw [hm_eq]
            exact dvd_mul_of_dvd_right hpdvd_eval 14535
          have hge :=
            Bridge2.Nat.divisors_card_ge_two_mul h43605 hp hpdvd_m hcop hm_ne
          rw [divisors_card_43605] at hge
          omega
  · -- 3 ∤ eval
    by_cases h5 : 5 ∣ eval
    · by_cases h17 : 17 ∣ eval
      · -- pair (5, 17): 1235475 = 14535 · 85, τ = 54
        have h1235475 : 1235475 ∣ m := by
          have h85 : 85 ∣ eval :=
            Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 5 17) h5 h17
          rcases h85 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [hm_eq, ht]; ring
        have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1235475 hm_ne
        rw [divisors_card_1235475] at hmono
        omega
      · by_cases h19 : 19 ∣ eval
        · -- pair (5, 19): 1380825 = 14535 · 95, τ = 54
          have h1380825 : 1380825 ∣ m := by
            have h95 : 95 ∣ eval :=
              Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 5 19) h5 h19
            rcases h95 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1380825 hm_ne
          rw [divisors_card_1380825] at hmono
          omega
        · -- only 5 divides eval — CASE B at p = 5
          by_cases hpow : ∀ s : ℕ, eval ≠ 5 ^ s
          · -- eval has a prime outside {3, 5, 17, 19}; coprime partner gives τ ≥ 72 > 47
            obtain ⟨p, hp, hpdvd_eval, hp_ne_5⟩ :=
              exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 5) h5 hpow
            have hp_notin_72675 : p ∉ (72675).primeFactors := by
              rw [primeFactors_72675]
              intro hpin
              simp at hpin
              rcases hpin with rfl | rfl | rfl | rfl
              · exact h3 hpdvd_eval
              · exact hp_ne_5 rfl
              · exact h17 hpdvd_eval
              · exact h19 hpdvd_eval
            have hcop : Nat.Coprime p 72675 :=
              coprime_of_prime_notin_primeFactors (by decide : (72675 : ℕ) ≠ 0) hp hp_notin_72675
            have h72675 : 72675 ∣ m := by
              rcases h5 with ⟨t, ht⟩
              refine ⟨t, ?_⟩
              rw [hm_eq, ht]; ring
            have hpdvd_m : p ∣ m := by
              rw [hm_eq]
              exact dvd_mul_of_dvd_right hpdvd_eval 14535
            have hge :=
              Bridge2.Nat.divisors_card_ge_two_mul h72675 hp hpdvd_m hcop hm_ne
            rw [divisors_card_72675] at hge
            omega
          · -- eval = 5^s for some s; Case B τ-forcing
            push_neg at hpow
            obtain ⟨s, hs⟩ := hpow
            rcases Nat.lt_or_ge s 2 with hs_lt | hs_ge
            · interval_cases s
              · -- s = 0: eval = 1, contradicts h_eval_gt_one
                simp at hs; omega
              · -- s = 1: eval = 5, so m = 14535 · 5 = 72675, hence 2520·N = 72720
                have heq : 2520 * N = 45 + 14535 * 5 ^ 1 := by
                  have : m = 14535 * 5 := by rw [hm_eq, hs]; ring
                  dsimp [m] at this
                  have hN_ge : 26884 ≤ N := by
                    have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
                    have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
                    omega
                  omega
                exact no_solution_14535_45_pow5_one N heq
            · -- s ≥ 2: 363375 = 3^2 · 5^3 · 17 · 19 divides m, τ ≥ 48 > 47
              have h25 : 25 ∣ eval := by
                rw [hs]
                have hs2 : 2 ≤ s := by omega
                have hs_eq : s = 2 + (s - 2) := by omega
                rw [hs_eq, pow_add, pow_two]
                exact dvd_mul_right _ _
              have h363375 : 363375 ∣ m := by
                -- 363375 = 14535 · 25
                rcases h25 with ⟨t, ht⟩
                refine ⟨t, ?_⟩
                rw [hm_eq, ht]; ring
              have hmono := Bridge2.Nat.divisors_card_le_of_dvd h363375 hm_ne
              rw [divisors_card_363375] at hmono
              omega
    · by_cases h17 : 17 ∣ eval
      · by_cases h19 : 19 ∣ eval
        · -- pair (17, 19): 4694805 = 14535 · 323, τ = 54
          have h4694805 : 4694805 ∣ m := by
            have h323 : 323 ∣ eval :=
              Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 17 19) h17 h19
            rcases h323 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hmono := Bridge2.Nat.divisors_card_le_of_dvd h4694805 hm_ne
          rw [divisors_card_4694805] at hmono
          omega
        · -- only 17 divides eval — Case A at p = 17
          have hnotpow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
            intro s hs
            have hpow : 2520 * N = 45 + 14535 * 17 ^ s := by
              have : m = 14535 * 17 ^ s := by rw [hm_eq, hs]
              dsimp [m] at this
              have hN_ge : 26884 ≤ N := by
                have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
                have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
                omega
              omega
            exact no_solution_14535_45_pow17 N s hpow
          obtain ⟨p, hp, hpdvd_eval, hp_ne_17⟩ :=
            exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 17) h17 hnotpow17
          have hp_notin_247095 : p ∉ (247095).primeFactors := by
            rw [primeFactors_247095]
            intro hpin
            simp at hpin
            rcases hpin with rfl | rfl | rfl | rfl
            · exact h3 hpdvd_eval
            · exact h5 hpdvd_eval
            · exact hp_ne_17 rfl
            · exact h19 hpdvd_eval
          have hcop : Nat.Coprime p 247095 :=
            coprime_of_prime_notin_primeFactors (by decide : (247095 : ℕ) ≠ 0) hp hp_notin_247095
          have h247095 : 247095 ∣ m := by
            rcases h17 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hpdvd_m : p ∣ m := by
            rw [hm_eq]
            exact dvd_mul_of_dvd_right hpdvd_eval 14535
          have hge :=
            Bridge2.Nat.divisors_card_ge_two_mul h247095 hp hpdvd_m hcop hm_ne
          rw [divisors_card_247095] at hge
          omega
      · by_cases h19 : 19 ∣ eval
        · -- only 19 divides eval — Case A at p = 19
          have hnotpow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
            intro s hs
            have hpow : 2520 * N = 45 + 14535 * 19 ^ s := by
              have : m = 14535 * 19 ^ s := by rw [hm_eq, hs]
              dsimp [m] at this
              have hN_ge : 26884 ≤ N := by
                have hr_ge : 26884 ≤ r := residue1453545_ge26884 r (by simpa [r] using hr)
                have : r ≤ N := by dsimp [r]; exact Nat.mod_le _ _
                omega
              omega
            exact no_solution_14535_45_pow19 N s hpow
          obtain ⟨p, hp, hpdvd_eval, hp_ne_19⟩ :=
            exists_prime_ne_of_not_primepow (by omega) (by decide : Nat.Prime 19) h19 hnotpow19
          have hp_notin_276165 : p ∉ (276165).primeFactors := by
            rw [primeFactors_276165]
            intro hpin
            simp at hpin
            rcases hpin with rfl | rfl | rfl | rfl
            · exact h3 hpdvd_eval
            · exact h5 hpdvd_eval
            · exact h17 hpdvd_eval
            · exact hp_ne_19 rfl
          have hcop : Nat.Coprime p 276165 :=
            coprime_of_prime_notin_primeFactors (by decide : (276165 : ℕ) ≠ 0) hp hp_notin_276165
          have h276165 : 276165 ∣ m := by
            rcases h19 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [hm_eq, ht]; ring
          have hpdvd_m : p ∣ m := by
            rw [hm_eq]
            exact dvd_mul_of_dvd_right hpdvd_eval 14535
          have hge :=
            Bridge2.Nat.divisors_card_ge_two_mul h276165 hp hpdvd_m hcop hm_ne
          rw [divisors_card_276165] at hge
          omega
        · -- no g-prime divides eval — coprime partner against g = 14535
          obtain ⟨p, hp, hpdvd_eval⟩ := Nat.exists_prime_and_dvd (by omega : eval ≠ 1)
          have hp_notin_14535 : p ∉ (14535).primeFactors := by
            rw [primeFactors_14535]
            intro hpin
            simp at hpin
            rcases hpin with rfl | rfl | rfl | rfl
            · exact h3 hpdvd_eval
            · exact h5 hpdvd_eval
            · exact h17 hpdvd_eval
            · exact h19 hpdvd_eval
          have hcop : Nat.Coprime p 14535 :=
            coprime_of_prime_notin_primeFactors (by decide : (14535 : ℕ) ≠ 0) hp hp_notin_14535
          have h14535 : 14535 ∣ m := ⟨eval, hm_eq⟩
          have hpdvd_m : p ∣ m := by
            rw [hm_eq]
            exact dvd_mul_of_dvd_right hpdvd_eval 14535
          have hge :=
            Bridge2.Nat.divisors_card_ge_two_mul h14535 hp hpdvd_m hcop hm_ne
          rw [divisors_card_14535] at hge
          omega

-- Notes for merging into Erdos647SingleOverlapClosure.lean:
--  * `exists_prime_ne_of_not_primepow` is already present there; drop the
--    implicit reference here and use the public name at merge time.
--  * `coprime_of_prime_notin_primeFactors` and `tau_bound_at_k` live in
--    `Erdos647ValuationCore`; no dedup needed.
--  * Fold `residues1453545` into the existing `singleOverlapResidues40` to
--    produce `singleOverlapResidues42` (together with `{40612}` from the
--    (4199, 13) draft).
--  * Update cardinality theorems in `Erdos647ResiduePartitionStage1.lean`:
--      `singleOverlapResidues42.card = 42`,
--      `closedResidues53.card` → `closedResidues55.card = 55`,
--      `openResiduesStage1.card = 43` → `41`,
--      `openResiduesUnformalizedBle1` deleted.

end Erdos647SingleOverlap_14535_45_draft
