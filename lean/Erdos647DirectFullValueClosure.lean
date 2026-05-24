import Mathlib
import Bridge2
import Erdos647BridgeV1
import Erdos647SieveCertificate
import Erdos647ValuationCore

/-!
# Direct full-value closures for the 13 easy Stage-1 residues
-/

namespace Erdos647DirectFullValueClosure

open Erdos647BridgeV1
open Erdos647ValuationCore

/-- The 6-residue family `(g_exact, k) = (1729, 7)`. -/
def residues1729_7 : Finset ℕ :=
  {5775, 16643, 24794, 32945, 41096, 43813}

/-- The 2-residue family `(g_exact, k) = (2584, 16)`. -/
def residues2584_16 : Finset ℕ := {7348, 39325}

/-- The 2-residue family `(g_exact, k) = (4522, 14)`. -/
def residues4522_14 : Finset ℕ := {8206, 40183}

/-- The 2-residue family `(g_exact, k) = (4845, 15)`. -/
def residues4845_15 : Finset ℕ := {7777, 39754}

/-- The 1-residue family `(g_exact, k) = (9690, 30)`. -/
def residues9690_30 : Finset ℕ := {33319}

def directFullValueResidues13 : Finset ℕ :=
  residues1729_7 ∪ residues2584_16 ∪ residues4522_14 ∪ residues4845_15 ∪ residues9690_30

private lemma residue1729_7_div (r : ℕ) (hr : r ∈ residues1729_7) :
    1729 ∣ 2520 * r - 7 := by
  native_decide +revert

private lemma residue1729_7_b_ge_two (r : ℕ) (hr : r ∈ residues1729_7) :
    2 ≤ (2520 * r - 7) / 1729 := by
  native_decide +revert

private lemma residue1729_7_ge5775 (r : ℕ) (hr : r ∈ residues1729_7) :
    5775 ≤ r := by
  native_decide +revert

private lemma primeFactors_1729 : (1729).primeFactors = {7, 13, 19} := by
  native_decide

private lemma divisors_card_1729 : (1729).divisors.card = 8 := by
  native_decide

private lemma divisors_card_1729_mul_factor {p : ℕ} (hp : p ∈ (1729).primeFactors) :
    (1729 * p).divisors.card = 12 := by
  rw [primeFactors_1729] at hp
  simp at hp
  rcases hp with rfl | rfl | rfl <;> native_decide

theorem no_erdos647_of_mem_residues1729_7 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues1729_7) :
    ¬ IsErdos647 (2520 * N) := by
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 7) / 1729
  let eval := 67320 * q + b
  let m := 2520 * N - 7

  have hr_div : 1729 ∣ 2520 * r - 7 := residue1729_7_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue1729_7_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 7 = 1729 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 1729 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 1729 * 67320 := by native_decide
    calc
      m = 2520 * N - 7 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 7 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 7) := by
            rw [Nat.mul_add, Nat.mul_assoc]
            omega
      _ = (1729 * 67320) * q + 1729 * b := by rw [hmul, hb_eq]
      _ = 1729 * eval := by
            dsimp [eval]
            ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 5775 ≤ N := by
      have hr_ge : 5775 ≤ r := residue1729_7_ge5775 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  obtain ⟨p, hp, hpdvd_eval⟩ := exists_prime_dvd_of_gt_one h_eval_gt_one

  by_cases hp_in : p ∈ (1729).primeFactors
  · have h1729p : 1729 * p ∣ m := by
      rcases hpdvd_eval with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hm_eq, ht]
      ring
    have hmono := Bridge2.Nat.divisors_card_le_of_dvd h1729p hm_ne
    have hlt : 9 < (1729 * p).divisors.card := by
      have hcard := divisors_card_1729_mul_factor hp_in
      omega
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 7) (by decide)
      (by
        have hN_ge : 5775 ≤ N := by
          have hr_ge : 5775 ≤ r := residue1729_7_ge5775 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        have hcard := divisors_card_1729_mul_factor hp_in
        exact lt_of_lt_of_le (by omega) hmono)
  · have hcop : Nat.Coprime p 1729 :=
      coprime_of_prime_notin_primeFactors (by decide : (1729 : ℕ) ≠ 0) hp hp_in
    have h1729 : 1729 ∣ m := by exact ⟨eval, hm_eq⟩
    have hpdvd_m : p ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_right hpdvd_eval 1729
    have hge := Bridge2.Nat.divisors_card_ge_two_mul h1729 hp hpdvd_m hcop hm_ne
    have hlt : 9 < 2 * (1729).divisors.card := by
      rw [divisors_card_1729]
      omega
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 7) (by decide)
      (by
        have hN_ge : 5775 ≤ N := by
          have hr_ge : 5775 ≤ r := residue1729_7_ge5775 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        rw [divisors_card_1729] at hge
        exact lt_of_lt_of_le (by decide : 9 < 16) hge)

private lemma residue2584_16_div (r : ℕ) (hr : r ∈ residues2584_16) :
    2584 ∣ 2520 * r - 16 := by
  native_decide +revert

private lemma residue2584_16_b_ge_two (r : ℕ) (hr : r ∈ residues2584_16) :
    2 ≤ (2520 * r - 16) / 2584 := by
  native_decide +revert

private lemma residue2584_16_ge7348 (r : ℕ) (hr : r ∈ residues2584_16) :
    7348 ≤ r := by
  native_decide +revert

private lemma primeFactors_2584 : (2584).primeFactors = {2, 17, 19} := by
  native_decide

private lemma divisors_card_2584 : (2584).divisors.card = 16 := by
  native_decide

private lemma divisors_card_2584_mul_factor {p : ℕ} (hp : p ∈ (2584).primeFactors) :
    20 ≤ (2584 * p).divisors.card := by
  rw [primeFactors_2584] at hp
  simp at hp
  rcases hp with rfl | rfl | rfl <;> native_decide

theorem no_erdos647_of_mem_residues2584_16 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues2584_16) :
    ¬ IsErdos647 (2520 * N) := by
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 16) / 2584
  let eval := 45045 * q + b
  let m := 2520 * N - 16

  have hr_div : 2584 ∣ 2520 * r - 16 := residue2584_16_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue2584_16_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 16 = 2584 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 2584 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 2584 * 45045 := by native_decide
    calc
      m = 2520 * N - 16 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 16 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 16) := by
            rw [Nat.mul_add, Nat.mul_assoc]
            omega
      _ = (2584 * 45045) * q + 2584 * b := by rw [hmul, hb_eq]
      _ = 2584 * eval := by
            dsimp [eval]
            ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 7348 ≤ N := by
      have hr_ge : 7348 ≤ r := residue2584_16_ge7348 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  obtain ⟨p, hp, hpdvd_eval⟩ := exists_prime_dvd_of_gt_one h_eval_gt_one

  by_cases hp_in : p ∈ (2584).primeFactors
  · have h2584p : 2584 * p ∣ m := by
      rcases hpdvd_eval with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hm_eq, ht]
      ring
    have hmono := Bridge2.Nat.divisors_card_le_of_dvd h2584p hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 16) (by decide)
      (by
        have hN_ge : 7348 ≤ N := by
          have hr_ge : 7348 ≤ r := residue2584_16_ge7348 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        have hcard := divisors_card_2584_mul_factor hp_in
        exact lt_of_lt_of_le (by omega) hmono)
  · have hcop : Nat.Coprime p 2584 :=
      coprime_of_prime_notin_primeFactors (by decide : (2584 : ℕ) ≠ 0) hp hp_in
    have h2584 : 2584 ∣ m := by exact ⟨eval, hm_eq⟩
    have hpdvd_m : p ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_right hpdvd_eval 2584
    have hge := Bridge2.Nat.divisors_card_ge_two_mul h2584 hp hpdvd_m hcop hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 16) (by decide)
      (by
        have hN_ge : 7348 ≤ N := by
          have hr_ge : 7348 ≤ r := residue2584_16_ge7348 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        rw [divisors_card_2584] at hge
        exact lt_of_lt_of_le (by decide : 18 < 32) hge)

private lemma residue4522_14_div (r : ℕ) (hr : r ∈ residues4522_14) :
    4522 ∣ 2520 * r - 14 := by
  native_decide +revert

private lemma residue4522_14_b_ge_two (r : ℕ) (hr : r ∈ residues4522_14) :
    2 ≤ (2520 * r - 14) / 4522 := by
  native_decide +revert

private lemma residue4522_14_ge8206 (r : ℕ) (hr : r ∈ residues4522_14) :
    8206 ≤ r := by
  native_decide +revert

private lemma primeFactors_4522 : (4522).primeFactors = {2, 7, 17, 19} := by
  native_decide

private lemma divisors_card_4522 : (4522).divisors.card = 16 := by
  native_decide

private lemma divisors_card_4522_mul_factor {p : ℕ} (hp : p ∈ (4522).primeFactors) :
    24 ≤ (4522 * p).divisors.card := by
  rw [primeFactors_4522] at hp
  simp at hp
  rcases hp with rfl | rfl | rfl | rfl <;> native_decide

theorem no_erdos647_of_mem_residues4522_14 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues4522_14) :
    ¬ IsErdos647 (2520 * N) := by
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 14) / 4522
  let eval := 25740 * q + b
  let m := 2520 * N - 14

  have hr_div : 4522 ∣ 2520 * r - 14 := residue4522_14_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue4522_14_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 14 = 4522 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 4522 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 4522 * 25740 := by native_decide
    calc
      m = 2520 * N - 14 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 14 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 14) := by
            rw [Nat.mul_add, Nat.mul_assoc]
            omega
      _ = (4522 * 25740) * q + 4522 * b := by rw [hmul, hb_eq]
      _ = 4522 * eval := by
            dsimp [eval]
            ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 8206 ≤ N := by
      have hr_ge : 8206 ≤ r := residue4522_14_ge8206 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  obtain ⟨p, hp, hpdvd_eval⟩ := exists_prime_dvd_of_gt_one h_eval_gt_one

  by_cases hp_in : p ∈ (4522).primeFactors
  · have h4522p : 4522 * p ∣ m := by
      rcases hpdvd_eval with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hm_eq, ht]
      ring
    have hmono := Bridge2.Nat.divisors_card_le_of_dvd h4522p hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 14) (by decide)
      (by
        have hN_ge : 8206 ≤ N := by
          have hr_ge : 8206 ≤ r := residue4522_14_ge8206 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        have hcard := divisors_card_4522_mul_factor hp_in
        exact lt_of_lt_of_le (by omega) hmono)
  · have hcop : Nat.Coprime p 4522 :=
      coprime_of_prime_notin_primeFactors (by decide : (4522 : ℕ) ≠ 0) hp hp_in
    have h4522 : 4522 ∣ m := by exact ⟨eval, hm_eq⟩
    have hpdvd_m : p ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_right hpdvd_eval 4522
    have hge := Bridge2.Nat.divisors_card_ge_two_mul h4522 hp hpdvd_m hcop hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 14) (by decide)
      (by
        have hN_ge : 8206 ≤ N := by
          have hr_ge : 8206 ≤ r := residue4522_14_ge8206 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        rw [divisors_card_4522] at hge
        exact lt_of_lt_of_le (by decide : 16 < 32) hge)

private lemma residue4845_15_div (r : ℕ) (hr : r ∈ residues4845_15) :
    4845 ∣ 2520 * r - 15 := by
  native_decide +revert

private lemma residue4845_15_b_ge_two (r : ℕ) (hr : r ∈ residues4845_15) :
    2 ≤ (2520 * r - 15) / 4845 := by
  native_decide +revert

private lemma residue4845_15_ge7777 (r : ℕ) (hr : r ∈ residues4845_15) :
    7777 ≤ r := by
  native_decide +revert

private lemma primeFactors_4845 : (4845).primeFactors = {3, 5, 17, 19} := by
  native_decide

private lemma divisors_card_4845 : (4845).divisors.card = 16 := by
  native_decide

private lemma divisors_card_4845_mul_factor {p : ℕ} (hp : p ∈ (4845).primeFactors) :
    24 ≤ (4845 * p).divisors.card := by
  rw [primeFactors_4845] at hp
  simp at hp
  rcases hp with rfl | rfl | rfl | rfl <;> native_decide

theorem no_erdos647_of_mem_residues4845_15 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues4845_15) :
    ¬ IsErdos647 (2520 * N) := by
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 15) / 4845
  let eval := 24024 * q + b
  let m := 2520 * N - 15

  have hr_div : 4845 ∣ 2520 * r - 15 := residue4845_15_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue4845_15_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 15 = 4845 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 4845 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 4845 * 24024 := by native_decide
    calc
      m = 2520 * N - 15 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 15 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 15) := by
            rw [Nat.mul_add, Nat.mul_assoc]
            omega
      _ = (4845 * 24024) * q + 4845 * b := by rw [hmul, hb_eq]
      _ = 4845 * eval := by
            dsimp [eval]
            ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 7777 ≤ N := by
      have hr_ge : 7777 ≤ r := residue4845_15_ge7777 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  obtain ⟨p, hp, hpdvd_eval⟩ := exists_prime_dvd_of_gt_one h_eval_gt_one

  by_cases hp_in : p ∈ (4845).primeFactors
  · have h4845p : 4845 * p ∣ m := by
      rcases hpdvd_eval with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hm_eq, ht]
      ring
    have hmono := Bridge2.Nat.divisors_card_le_of_dvd h4845p hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 15) (by decide)
      (by
        have hN_ge : 7777 ≤ N := by
          have hr_ge : 7777 ≤ r := residue4845_15_ge7777 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        have hcard := divisors_card_4845_mul_factor hp_in
        exact lt_of_lt_of_le (by omega) hmono)
  · have hcop : Nat.Coprime p 4845 :=
      coprime_of_prime_notin_primeFactors (by decide : (4845 : ℕ) ≠ 0) hp hp_in
    have h4845 : 4845 ∣ m := by exact ⟨eval, hm_eq⟩
    have hpdvd_m : p ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_right hpdvd_eval 4845
    have hge := Bridge2.Nat.divisors_card_ge_two_mul h4845 hp hpdvd_m hcop hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 15) (by decide)
      (by
        have hN_ge : 7777 ≤ N := by
          have hr_ge : 7777 ≤ r := residue4845_15_ge7777 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        rw [divisors_card_4845] at hge
        exact lt_of_lt_of_le (by decide : 17 < 32) hge)

private lemma residue9690_30_div (r : ℕ) (hr : r ∈ residues9690_30) :
    9690 ∣ 2520 * r - 30 := by
  native_decide +revert

private lemma residue9690_30_b_ge_two (r : ℕ) (hr : r ∈ residues9690_30) :
    2 ≤ (2520 * r - 30) / 9690 := by
  native_decide +revert

private lemma residue9690_30_ge33319 (r : ℕ) (hr : r ∈ residues9690_30) :
    33319 ≤ r := by
  native_decide +revert

private lemma primeFactors_9690 : (9690).primeFactors = {2, 3, 5, 17, 19} := by
  native_decide

private lemma divisors_card_9690 : (9690).divisors.card = 32 := by
  native_decide

private lemma divisors_card_9690_mul_factor {p : ℕ} (hp : p ∈ (9690).primeFactors) :
    48 ≤ (9690 * p).divisors.card := by
  rw [primeFactors_9690] at hp
  simp at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem no_erdos647_of_mem_residues9690_30 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ residues9690_30) :
    ¬ IsErdos647 (2520 * N) := by
  let r := N % Erdos647SieveCertificate.M
  let q := N / Erdos647SieveCertificate.M
  let b := (2520 * r - 30) / 9690
  let eval := 12012 * q + b
  let m := 2520 * N - 30

  have hr_div : 9690 ∣ 2520 * r - 30 := residue9690_30_div r (by simpa [r] using hr)
  have hb_ge_two : 2 ≤ b := residue9690_30_b_ge_two r (by simpa [r] using hr)

  have hb_eq : 2520 * r - 30 = 9690 * b := by
    dsimp [b]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hr_div).symm

  have hN_decomp : N = Erdos647SieveCertificate.M * q + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm, Erdos647SieveCertificate.M] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm

  have hm_eq : m = 9690 * eval := by
    have hmul : 2520 * Erdos647SieveCertificate.M = 9690 * 12012 := by native_decide
    calc
      m = 2520 * N - 30 := by rfl
      _ = 2520 * (Erdos647SieveCertificate.M * q + r) - 30 := by rw [hN_decomp]
      _ = (2520 * Erdos647SieveCertificate.M) * q + (2520 * r - 30) := by
            rw [Nat.mul_add, Nat.mul_assoc]
            omega
      _ = (9690 * 12012) * q + 9690 * b := by rw [hmul, hb_eq]
      _ = 9690 * eval := by
            dsimp [eval]
            ring

  have hm_ne : m ≠ 0 := by
    dsimp [m]
    have hN_ge : 33319 ≤ N := by
      have hr_ge : 33319 ≤ r := residue9690_30_ge33319 r (by simpa [r] using hr)
      have : r ≤ N := by
        dsimp [r]
        exact Nat.mod_le _ _
      omega
    omega

  have h_eval_gt_one : 1 < eval := by
    dsimp [eval]
    omega

  obtain ⟨p, hp, hpdvd_eval⟩ := exists_prime_dvd_of_gt_one h_eval_gt_one

  by_cases hp_in : p ∈ (9690).primeFactors
  · have h9690p : 9690 * p ∣ m := by
      rcases hpdvd_eval with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hm_eq, ht]
      ring
    have hmono := Bridge2.Nat.divisors_card_le_of_dvd h9690p hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 30) (by decide)
      (by
        have hN_ge : 33319 ≤ N := by
          have hr_ge : 33319 ≤ r := residue9690_30_ge33319 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        have hcard := divisors_card_9690_mul_factor hp_in
        exact lt_of_lt_of_le (by omega) hmono)
  · have hcop : Nat.Coprime p 9690 :=
      coprime_of_prime_notin_primeFactors (by decide : (9690 : ℕ) ≠ 0) hp hp_in
    have h9690 : 9690 ∣ m := by exact ⟨eval, hm_eq⟩
    have hpdvd_m : p ∣ m := by
      rw [hm_eq]
      exact dvd_mul_of_dvd_right hpdvd_eval 9690
    have hge := Bridge2.Nat.divisors_card_ge_two_mul h9690 hp hpdvd_m hcop hm_ne
    exact not_isErdos647_of_tau_gt_at (N := N) (k := 30) (by decide)
      (by
        have hN_ge : 33319 ≤ N := by
          have hr_ge : 33319 ≤ r := residue9690_30_ge33319 r (by simpa [r] using hr)
          have : r ≤ N := by
            dsimp [r]
            exact Nat.mod_le _ _
          omega
        omega)
      (by
        rw [divisors_card_9690] at hge
        exact lt_of_lt_of_le (by decide : 32 < 64) hge)

theorem no_erdos647_of_mem_directFullValueResidues13 (N : ℕ)
    (hr : N % Erdos647SieveCertificate.M ∈ directFullValueResidues13) :
    ¬ IsErdos647 (2520 * N) := by
  have hr' :
      N % Erdos647SieveCertificate.M ∈ residues1729_7 ∨
      N % Erdos647SieveCertificate.M ∈ residues2584_16 ∨
      N % Erdos647SieveCertificate.M ∈ residues4522_14 ∨
      N % Erdos647SieveCertificate.M ∈ residues4845_15 ∨
      N % Erdos647SieveCertificate.M ∈ residues9690_30 := by
    simpa [directFullValueResidues13, Finset.mem_union, or_assoc]
      using hr
  rcases hr' with hr1729 | hr2584 | hr4522 | hr4845 | hr9690
  · exact no_erdos647_of_mem_residues1729_7 N hr1729
  · exact no_erdos647_of_mem_residues2584_16 N hr2584
  · exact no_erdos647_of_mem_residues4522_14 N hr4522
  · exact no_erdos647_of_mem_residues4845_15 N hr4845
  · exact no_erdos647_of_mem_residues9690_30 N hr9690

theorem directFullValueResidues13_card : directFullValueResidues13.card = 13 := by
  native_decide

end Erdos647DirectFullValueClosure
