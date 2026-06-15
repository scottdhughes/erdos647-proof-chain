import Mathlib
import Erdos647V23HenselCore

open Nat Finset Erdos647V23Hensel Erdos647QuotientCover

-- Auto-generated. Mod-23 rootline partial certificates for the 41 canonical frontier residues mod 46189.
-- Each theorem closes a sub-AP of relative density 1/23 inside its base AP via hensel_rootline_closure.
-- Total candidates: 269
-- Source: scripts/codegen_mod23_rootline.py

set_option maxHeartbeats 16000000

lemma tau_46_mul_prime_gt4 :
    ∀ p : ℕ, p.Prime → (46 * p).divisors.card > 4 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 46 := by
      intro hdvd
      have hmem : p ∈ (46 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (46 : ℕ).primeFactors = {2, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 46 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_69_mul_prime_gt5 :
    ∀ p : ℕ, p.Prime → (69 * p).divisors.card > 5 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 69 := by
      intro hdvd
      have hmem : p ∈ (69 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (69 : ℕ).primeFactors = {3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 69 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_92_mul_prime_gt6 :
    ∀ p : ℕ, p.Prime → (92 * p).divisors.card > 6 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 92 := by
      intro hdvd
      have hmem : p ∈ (92 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (92 : ℕ).primeFactors = {2, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 92 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_138_mul_prime_gt8 :
    ∀ p : ℕ, p.Prime → (138 * p).divisors.card > 8 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 138 := by
      intro hdvd
      have hmem : p ∈ (138 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (138 : ℕ).primeFactors = {2, 3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 138 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_3059_mul_prime_gt9 :
    ∀ p : ℕ, p.Prime → (3059 * p).divisors.card > 9 := by
  intro p hp
  by_cases h7 : p = 7
  · subst h7; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 3059 := by
      intro hdvd
      have hmem : p ∈ (3059 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (3059 : ℕ).primeFactors = {7, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 3059 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_276_mul_prime_gt14 :
    ∀ p : ℕ, p.Prime → (276 * p).divisors.card > 14 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 276 := by
      intro hdvd
      have hmem : p ∈ (276 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (276 : ℕ).primeFactors = {2, 3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 276 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_5474_mul_prime_gt16 :
    ∀ p : ℕ, p.Prime → (5474 * p).divisors.card > 16 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h7 : p = 7
  · subst h7; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 5474 := by
      intro hdvd
      have hmem : p ∈ (5474 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (5474 : ℕ).primeFactors = {2, 7, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 5474 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_6118_mul_prime_gt16 :
    ∀ p : ℕ, p.Prime → (6118 * p).divisors.card > 16 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h7 : p = 7
  · subst h7; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 6118 := by
      intro hdvd
      have hmem : p ∈ (6118 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (6118 : ℕ).primeFactors = {2, 7, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 6118 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_5865_mul_prime_gt17 :
    ∀ p : ℕ, p.Prime → (5865 * p).divisors.card > 17 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 5865 := by
      intro hdvd
      have hmem : p ∈ (5865 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (5865 : ℕ).primeFactors = {3, 5, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 5865 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_6555_mul_prime_gt17 :
    ∀ p : ℕ, p.Prime → (6555 * p).divisors.card > 17 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 6555 := by
      intro hdvd
      have hmem : p ∈ (6555 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (6555 : ℕ).primeFactors = {3, 5, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 6555 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_3128_mul_prime_gt18 :
    ∀ p : ℕ, p.Prime → (3128 * p).divisors.card > 18 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 3128 := by
      intro hdvd
      have hmem : p ∈ (3128 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (3128 : ℕ).primeFactors = {2, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 3128 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_3496_mul_prime_gt18 :
    ∀ p : ℕ, p.Prime → (3496 * p).divisors.card > 18 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 3496 := by
      intro hdvd
      have hmem : p ∈ (3496 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (3496 : ℕ).primeFactors = {2, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 3496 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_10948_mul_prime_gt30 :
    ∀ p : ℕ, p.Prime → (10948 * p).divisors.card > 30 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h7 : p = 7
  · subst h7; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 10948 := by
      intro hdvd
      have hmem : p ∈ (10948 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (10948 : ℕ).primeFactors = {2, 7, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 10948 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_11730_mul_prime_gt32 :
    ∀ p : ℕ, p.Prime → (11730 * p).divisors.card > 32 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 11730 := by
      intro hdvd
      have hmem : p ∈ (11730 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (11730 : ℕ).primeFactors = {2, 3, 5, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 11730 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_13110_mul_prime_gt32 :
    ∀ p : ℕ, p.Prime → (13110 * p).divisors.card > 32 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 13110 := by
      intro hdvd
      have hmem : p ∈ (13110 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (13110 : ℕ).primeFactors = {2, 3, 5, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 13110 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_59432_mul_prime_gt34 :
    ∀ p : ℕ, p.Prime → (59432 * p).divisors.card > 34 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 59432 := by
      intro hdvd
      have hmem : p ∈ (59432 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (59432 : ℕ).primeFactors = {2, 17, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 59432 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_245157_mul_prime_gt35 :
    ∀ p : ℕ, p.Prime → (245157 * p).divisors.card > 35 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h11 : p = 11
  · subst h11; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 245157 := by
      intro hdvd
      have hmem : p ∈ (245157 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (245157 : ℕ).primeFactors = {3, 11, 17, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 245157 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_15732_mul_prime_gt38 :
    ∀ p : ℕ, p.Prime → (15732 * p).divisors.card > 38 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 15732 := by
      intro hdvd
      have hmem : p ∈ (15732 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (15732 : ℕ).primeFactors = {2, 3, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 15732 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


/-- Mod-23 rootline partial certificate at residue r = 0, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 0 (mod 46189)}. -/
theorem mod23_rootline_partial_r0_c5 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 230945) := by
  apply hensel_rootline_closure 3 69 1062347 230945 38798760 8434513
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 0, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 0 (mod 46189)}. -/
theorem mod23_rootline_partial_r0_c10 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 461890) := by
  apply hensel_rootline_closure 6 138 1062347 461890 19399380 8434513
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 0, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 0 (mod 46189)}. -/
theorem mod23_rootline_partial_r0_c11 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 508079) := by
  apply hensel_rootline_closure 2 46 1062347 508079 58198140 27833893
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 0, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 0 (mod 46189)}. -/
theorem mod23_rootline_partial_r0_c20 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 923780) := by
  apply hensel_rootline_closure 12 276 1062347 923780 9699690 8434513
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 0, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 0 (mod 46189)}. -/
theorem mod23_rootline_partial_r0_c22 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 1016158) := by
  apply hensel_rootline_closure 4 92 1062347 1016158 29099070 27833893
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c4 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 185614) := by
  apply hensel_rootline_closure 6 138 1062347 185614 19399380 3389473
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c5 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 231803) := by
  apply hensel_rootline_closure 2 46 1062347 231803 58198140 12698773
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c8 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 370370) := by
  apply hensel_rootline_closure 36 15732 1062347 370370 170170 59327
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c14 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 647504) := by
  apply hensel_rootline_closure 12 276 1062347 647504 9699690 5911993
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c16 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 739882) := by
  apply hensel_rootline_closure 4 92 1062347 739882 29099070 20266333
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c19 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 878449) := by
  apply hensel_rootline_closure 15 5865 1062347 878449 456456 377441
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 858, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 858 (mod 46189)}. -/
theorem mod23_rootline_partial_r858_c22 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 1017016) := by
  apply hensel_rootline_closure 3 69 1062347 1017016 38798760 37143193
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c1 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 47476) := by
  apply hensel_rootline_closure 6 138 1062347 47476 19399380 866953
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c2 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 93665) := by
  apply hensel_rootline_closure 2 46 1062347 93665 58198140 5131213
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c10 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 463177) := by
  apply hensel_rootline_closure 16 3496 1062347 463177 765765 333869
  · intro s; omega
  · omega
  · omega
  · exact tau_3496_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c11 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 509366) := by
  apply hensel_rootline_closure 12 276 1062347 509366 9699690 4650733
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c13 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 601744) := by
  apply hensel_rootline_closure 4 92 1062347 601744 29099070 16482553
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c19 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 878878) := by
  apply hensel_rootline_closure 3 69 1062347 878878 38798760 32098153
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 1287, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1287 (mod 46189)}. -/
theorem mod23_rootline_partial_r1287_c22 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 1017445) := by
  apply hensel_rootline_closure 14 5474 1062347 1017445 489060 468389
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c8 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 371228) := by
  apply hensel_rootline_closure 12 276 1062347 371228 9699690 3389473
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c10 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 463606) := by
  apply hensel_rootline_closure 4 92 1062347 463606 29099070 12698773
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c13 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 602173) := by
  apply hensel_rootline_closure 15 6555 1062347 602173 408408 231499
  · intro s; omega
  · omega
  · omega
  · exact tau_6555_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c15 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 694551) := by
  apply hensel_rootline_closure 30 11730 1062347 694551 228228 149213
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c16 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 740740) := by
  apply hensel_rootline_closure 3 69 1062347 740740 38798760 27053113
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c21 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 971685) := by
  apply hensel_rootline_closure 6 138 1062347 971685 19399380 17743813
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 1716, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 1716 (mod 46189)}. -/
theorem mod23_rootline_partial_r1716_c22 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 1017874) := by
  apply hensel_rootline_closure 2 46 1062347 1017874 58198140 55761793
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c3 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 140998) := by
  apply hensel_rootline_closure 12 276 1062347 140998 9699690 1287373
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c5 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 233376) := by
  apply hensel_rootline_closure 4 92 1062347 233376 29099070 6392473
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c10 :
    ∀ s : ℕ, ¬ goodOn {7} (1062347 * s + 464321) := by
  apply hensel_rootline_closure 7 3059 1062347 464321 875160 382507
  · intro s; omega
  · omega
  · omega
  · exact tau_3059_mul_prime_gt9


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c11 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 510510) := by
  apply hensel_rootline_closure 3 69 1062347 510510 38798760 18644713
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c16 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 741455) := by
  apply hensel_rootline_closure 6 138 1062347 741455 19399380 13539613
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 2431, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2431 (mod 46189)}. -/
theorem mod23_rootline_partial_r2431_c17 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 787644) := by
  apply hensel_rootline_closure 2 46 1062347 787644 58198140 43149193
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c2 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 94952) := by
  apply hensel_rootline_closure 12 276 1062347 94952 9699690 866953
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c4 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 187330) := by
  apply hensel_rootline_closure 4 92 1062347 187330 29099070 5131213
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c10 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 464464) := by
  apply hensel_rootline_closure 3 69 1062347 464464 38798760 16963033
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c15 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 695409) := by
  apply hensel_rootline_closure 6 138 1062347 695409 19399380 12698773
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c16 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 741598) := by
  apply hensel_rootline_closure 2 46 1062347 741598 58198140 40626673
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 2574, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 2574 (mod 46189)}. -/
theorem mod23_rootline_partial_r2574_c21 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 972543) := by
  apply hensel_rootline_closure 28 10948 1062347 972543 244530 223859
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c0 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 4862) := by
  apply hensel_rootline_closure 2 46 1062347 4862 58198140 266353
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c9 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 420563) := by
  apply hensel_rootline_closure 12 276 1062347 420563 9699690 3839923
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c11 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 512941) := by
  apply hensel_rootline_closure 4 92 1062347 512941 29099070 14050123
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c17 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 790075) := by
  apply hensel_rootline_closure 3 69 1062347 790075 38798760 28854913
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c20 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 928642) := by
  apply hensel_rootline_closure 14 6118 1062347 928642 437580 382507
  · intro s; omega
  · omega
  · omega
  · exact tau_6118_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 4862, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 4862 (mod 46189)}. -/
theorem mod23_rootline_partial_r4862_c22 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 1021020) := by
  apply hensel_rootline_closure 6 138 1062347 1021020 19399380 18644713
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c5 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 236236) := by
  apply hensel_rootline_closure 16 3128 1062347 236236 855855 190318
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c6 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 282425) := by
  apply hensel_rootline_closure 12 276 1062347 282425 9699690 2578663
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c8 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 374803) := by
  apply hensel_rootline_closure 4 92 1062347 374803 29099070 10266343
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c14 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 651937) := by
  apply hensel_rootline_closure 3 69 1062347 651937 38798760 23809873
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c19 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 882882) := by
  apply hensel_rootline_closure 6 138 1062347 882882 19399380 16122193
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 5291, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 5291 (mod 46189)}. -/
theorem mod23_rootline_partial_r5291_c20 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 929071) := by
  apply hensel_rootline_closure 2 46 1062347 929071 58198140 50896933
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c0 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 6149) := by
  apply hensel_rootline_closure 12 276 1062347 6149 9699690 56143
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c2 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 98527) := by
  apply hensel_rootline_closure 4 92 1062347 98527 29099070 2698783
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c7 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 329472) := by
  apply hensel_rootline_closure 30 13110 1062347 329472 204204 63331
  · intro s; omega
  · omega
  · omega
  · exact tau_13110_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c8 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 375661) := by
  apply hensel_rootline_closure 3 69 1062347 375661 38798760 13719793
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c11 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 514228) := by
  apply hensel_rootline_closure 14 5474 1062347 514228 489060 236729
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c13 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 606606) := by
  apply hensel_rootline_closure 6 138 1062347 606606 19399380 11077153
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 6149, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 6149 (mod 46189)}. -/
theorem mod23_rootline_partial_r6149_c14 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 652795) := by
  apply hensel_rootline_closure 2 46 1062347 652795 58198140 35761813
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c0 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 8151) := by
  apply hensel_rootline_closure 2 46 1062347 8151 58198140 446533
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c9 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 423852) := by
  apply hensel_rootline_closure 12 276 1062347 423852 9699690 3869953
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c11 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 516230) := by
  apply hensel_rootline_closure 4 92 1062347 516230 29099070 14140213
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c14 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 654797) := by
  apply hensel_rootline_closure 15 5865 1062347 654797 456456 281345
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c17 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 793364) := by
  apply hensel_rootline_closure 3 69 1062347 793364 38798760 28975033
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 8151, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 8151 (mod 46189)}. -/
theorem mod23_rootline_partial_r8151_c22 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 1024309) := by
  apply hensel_rootline_closure 6 138 1062347 1024309 19399380 18704773
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c3 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 147576) := by
  apply hensel_rootline_closure 12 276 1062347 147576 9699690 1347433
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c5 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 239954) := by
  apply hensel_rootline_closure 4 92 1062347 239954 29099070 6572653
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c10 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 470899) := by
  apply hensel_rootline_closure 30 11730 1062347 470899 228228 101165
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c11 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 517088) := by
  apply hensel_rootline_closure 3 69 1062347 517088 38798760 18884953
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c16 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 748033) := by
  apply hensel_rootline_closure 6 138 1062347 748033 19399380 13659733
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c17 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 794222) := by
  apply hensel_rootline_closure 2 46 1062347 794222 58198140 43509553
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 9009, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9009 (mod 46189)}. -/
theorem mod23_rootline_partial_r9009_c20 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 932789) := by
  apply hensel_rootline_closure 36 15732 1062347 932789 170170 149417
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c2 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 102245) := by
  apply hensel_rootline_closure 15 6555 1062347 102245 408408 39307
  · intro s; omega
  · omega
  · omega
  · exact tau_6555_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c5 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 240812) := by
  apply hensel_rootline_closure 3 69 1062347 240812 38798760 8794873
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c10 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 471757) := by
  apply hensel_rootline_closure 6 138 1062347 471757 19399380 8614693
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c11 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 517946) := by
  apply hensel_rootline_closure 2 46 1062347 517946 58198140 28374433
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c16 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 748891) := by
  apply hensel_rootline_closure 28 10948 1062347 748891 244530 172379
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c20 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 933647) := by
  apply hensel_rootline_closure 12 276 1062347 933647 9699690 8524603
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 9867, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 9867 (mod 46189)}. -/
theorem mod23_rootline_partial_r9867_c22 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 1026025) := by
  apply hensel_rootline_closure 4 92 1062347 1026025 29099070 28104163
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c0 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 10582) := by
  apply hensel_rootline_closure 3 69 1062347 10582 38798760 386473
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c5 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 241527) := by
  apply hensel_rootline_closure 6 138 1062347 241527 19399380 4410493
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c6 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 287716) := by
  apply hensel_rootline_closure 2 46 1062347 287716 58198140 15761833
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c15 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 703417) := by
  apply hensel_rootline_closure 12 276 1062347 703417 9699690 6422503
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c17 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 795795) := by
  apply hensel_rootline_closure 4 92 1062347 795795 29099070 21797863
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c20 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 934362) := by
  apply hensel_rootline_closure 15 5865 1062347 934362 456456 401465
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 10582, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 10582 (mod 46189)}. -/
theorem mod23_rootline_partial_r10582_c22 :
    ∀ s : ℕ, ¬ goodOn {7} (1062347 * s + 1026740) := by
  apply hensel_rootline_closure 7 3059 1062347 1026740 875160 845827
  · intro s; omega
  · omega
  · omega
  · exact tau_3059_mul_prime_gt9


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c3 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 150722) := by
  apply hensel_rootline_closure 16 3496 1062347 150722 765765 108644
  · intro s; omega
  · omega
  · omega
  · exact tau_3496_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c4 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 196911) := by
  apply hensel_rootline_closure 12 276 1062347 196911 9699690 1797883
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c6 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 289289) := by
  apply hensel_rootline_closure 4 92 1062347 289289 29099070 7924003
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c12 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 566423) := by
  apply hensel_rootline_closure 3 69 1062347 566423 38798760 20686753
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c17 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 797368) := by
  apply hensel_rootline_closure 6 138 1062347 797368 19399380 14560633
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 12155, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12155 (mod 46189)}. -/
theorem mod23_rootline_partial_r12155_c18 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 843557) := by
  apply hensel_rootline_closure 2 46 1062347 843557 58198140 46212253
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c0 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 12584) := by
  apply hensel_rootline_closure 16 3128 1062347 12584 855855 10138
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c1 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 58773) := by
  apply hensel_rootline_closure 12 276 1062347 58773 9699690 536623
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c3 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 151151) := by
  apply hensel_rootline_closure 4 92 1062347 151151 29099070 4140223
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c6 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 289718) := by
  apply hensel_rootline_closure 15 6555 1062347 289718 408408 111379
  · intro s; omega
  · omega
  · omega
  · exact tau_6555_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c9 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 428285) := by
  apply hensel_rootline_closure 3 69 1062347 428285 38798760 15641713
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c14 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 659230) := by
  apply hensel_rootline_closure 6 138 1062347 659230 19399380 12038113
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 12584, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 12584 (mod 46189)}. -/
theorem mod23_rootline_partial_r12584_c15 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 705419) := by
  apply hensel_rootline_closure 2 46 1062347 705419 58198140 38644693
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c0 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 13013) := by
  apply hensel_rootline_closure 4 92 1062347 13013 29099070 356443
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c3 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 151580) := by
  apply hensel_rootline_closure 15 5865 1062347 151580 456456 65129
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c6 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 290147) := by
  apply hensel_rootline_closure 3 69 1062347 290147 38798760 10596673
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c9 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 428714) := by
  apply hensel_rootline_closure 14 6118 1062347 428714 437580 176587
  · intro s; omega
  · omega
  · omega
  · exact tau_6118_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c11 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 521092) := by
  apply hensel_rootline_closure 6 138 1062347 521092 19399380 9515593
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c12 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 567281) := by
  apply hensel_rootline_closure 2 46 1062347 567281 58198140 31077133
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 13013, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13013 (mod 46189)}. -/
theorem mod23_rootline_partial_r13013_c21 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 982982) := by
  apply hensel_rootline_closure 12 276 1062347 982982 9699690 8975053
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c3 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 152009) := by
  apply hensel_rootline_closure 3 69 1062347 152009 38798760 5551633
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c6 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 290576) := by
  apply hensel_rootline_closure 14 5474 1062347 290576 489060 133769
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c8 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 382954) := by
  apply hensel_rootline_closure 6 138 1062347 382954 19399380 6993073
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c9 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 429143) := by
  apply hensel_rootline_closure 2 46 1062347 429143 58198140 23509573
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c18 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 844844) := by
  apply hensel_rootline_closure 12 276 1062347 844844 9699690 7713793
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 13442, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 13442 (mod 46189)}. -/
theorem mod23_rootline_partial_r13442_c20 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 937222) := by
  apply hensel_rootline_closure 4 92 1062347 937222 29099070 25671733
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c0 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 16302) := by
  apply hensel_rootline_closure 4 92 1062347 16302 29099070 446533
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c5 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 247247) := by
  apply hensel_rootline_closure 30 11730 1062347 247247 228228 53117
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c6 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 293436) := by
  apply hensel_rootline_closure 3 69 1062347 293436 38798760 10716793
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c11 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 524381) := by
  apply hensel_rootline_closure 6 138 1062347 524381 19399380 9575653
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c12 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 570570) := by
  apply hensel_rootline_closure 2 46 1062347 570570 58198140 31257313
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 16302, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 16302 (mod 46189)}. -/
theorem mod23_rootline_partial_r16302_c21 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 986271) := by
  apply hensel_rootline_closure 12 276 1062347 986271 9699690 9005083
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c0 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 17017) := by
  apply hensel_rootline_closure 30 13110 1062347 17017 204204 3271
  · intro s; omega
  · omega
  · omega
  · exact tau_13110_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c1 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 63206) := by
  apply hensel_rootline_closure 3 69 1062347 63206 38798760 2308393
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c6 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 294151) := by
  apply hensel_rootline_closure 6 138 1062347 294151 19399380 5371453
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c7 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 340340) := by
  apply hensel_rootline_closure 2 46 1062347 340340 58198140 18644713
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c16 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 756041) := by
  apply hensel_rootline_closure 12 276 1062347 756041 9699690 6902983
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 17017, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17017 (mod 46189)}. -/
theorem mod23_rootline_partial_r17017_c18 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 848419) := by
  apply hensel_rootline_closure 4 92 1062347 848419 29099070 23239303
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c0 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 17160) := by
  apply hensel_rootline_closure 3 69 1062347 17160 38798760 626713
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c5 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 248105) := by
  apply hensel_rootline_closure 6 138 1062347 248105 19399380 4530613
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c6 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 294294) := by
  apply hensel_rootline_closure 2 46 1062347 294294 58198140 16122193
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c9 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 432861) := by
  apply hensel_rootline_closure 36 15732 1062347 432861 170170 69337
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c11 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 525239) := by
  apply hensel_rootline_closure 28 10948 1062347 525239 244530 120899
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c15 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 709995) := by
  apply hensel_rootline_closure 12 276 1062347 709995 9699690 6482563
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 17160, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 17160 (mod 46189)}. -/
theorem mod23_rootline_partial_r17160_c17 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 802373) := by
  apply hensel_rootline_closure 4 92 1062347 802373 29099070 21978043
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c4 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 203489) := by
  apply hensel_rootline_closure 12 276 1062347 203489 9699690 1857943
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c6 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 295867) := by
  apply hensel_rootline_closure 4 92 1062347 295867 29099070 8104183
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c11 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 526812) := by
  apply hensel_rootline_closure 30 11730 1062347 526812 228228 113177
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c12 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 573001) := by
  apply hensel_rootline_closure 3 69 1062347 573001 38798760 20926993
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c17 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 803946) := by
  apply hensel_rootline_closure 6 138 1062347 803946 19399380 14680753
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 18733, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 18733 (mod 46189)}. -/
theorem mod23_rootline_partial_r18733_c18 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 850135) := by
  apply hensel_rootline_closure 2 46 1062347 850135 58198140 46572613
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c4 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 204633) := by
  apply hensel_rootline_closure 3 69 1062347 204633 38798760 7473553
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c9 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 435578) := by
  apply hensel_rootline_closure 6 138 1062347 435578 19399380 7954033
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c10 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 481767) := by
  apply hensel_rootline_closure 2 46 1062347 481767 58198140 26392453
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c13 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 620334) := by
  apply hensel_rootline_closure 36 15732 1062347 620334 170170 99367
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c18 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 851279) := by
  apply hensel_rootline_closure 16 3128 1062347 851279 855855 685813
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c19 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 897468) := by
  apply hensel_rootline_closure 12 276 1062347 897468 9699690 8194273
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 19877, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 19877 (mod 46189)}. -/
theorem mod23_rootline_partial_r19877_c21 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 989846) := by
  apply hensel_rootline_closure 4 92 1062347 989846 29099070 27113173
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c1 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 66495) := by
  apply hensel_rootline_closure 3 69 1062347 66495 38798760 2428513
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c6 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 297440) := by
  apply hensel_rootline_closure 6 138 1062347 297440 19399380 5431513
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c7 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 343629) := by
  apply hensel_rootline_closure 2 46 1062347 343629 58198140 18824893
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c15 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 713141) := by
  apply hensel_rootline_closure 16 3496 1062347 713141 765765 514049
  · intro s; omega
  · omega
  · omega
  · exact tau_3496_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c16 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 759330) := by
  apply hensel_rootline_closure 12 276 1062347 759330 9699690 6933013
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c18 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 851708) := by
  apply hensel_rootline_closure 4 92 1062347 851708 29099070 23329393
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 20306, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20306 (mod 46189)}. -/
theorem mod23_rootline_partial_r20306_c21 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 990275) := by
  apply hensel_rootline_closure 15 5865 1062347 990275 456456 425489
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c1 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 66924) := by
  apply hensel_rootline_closure 14 5474 1062347 66924 489060 30809
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c3 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 159302) := by
  apply hensel_rootline_closure 6 138 1062347 159302 19399380 2908993
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c4 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 205491) := by
  apply hensel_rootline_closure 2 46 1062347 205491 58198140 11257333
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c13 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 621192) := by
  apply hensel_rootline_closure 12 276 1062347 621192 9699690 5671753
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c15 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 713570) := by
  apply hensel_rootline_closure 4 92 1062347 713570 29099070 19545613
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c18 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 852137) := by
  apply hensel_rootline_closure 15 6555 1062347 852137 408408 327595
  · intro s; omega
  · omega
  · omega
  · exact tau_6555_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 20735, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 20735 (mod 46189)}. -/
theorem mod23_rootline_partial_r20735_c21 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 990704) := by
  apply hensel_rootline_closure 3 69 1062347 990704 38798760 36182233
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c0 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 21164) := by
  apply hensel_rootline_closure 6 138 1062347 21164 19399380 386473
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c1 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 67353) := by
  apply hensel_rootline_closure 2 46 1062347 67353 58198140 3689773
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c10 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 483054) := by
  apply hensel_rootline_closure 12 276 1062347 483054 9699690 4410493
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c12 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 575432) := by
  apply hensel_rootline_closure 4 92 1062347 575432 29099070 15761833
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c17 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 806377) := by
  apply hensel_rootline_closure 30 11730 1062347 806377 228228 173237
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c18 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 852566) := by
  apply hensel_rootline_closure 3 69 1062347 852566 38798760 31137193
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 21164, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 21164 (mod 46189)}. -/
theorem mod23_rootline_partial_r21164_c21 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 991133) := by
  apply hensel_rootline_closure 14 6118 1062347 991133 437580 408247
  · intro s; omega
  · omega
  · omega
  · exact tau_6118_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 24310, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24310 (mod 46189)}. -/
theorem mod23_rootline_partial_r24310_c1 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 70499) := by
  apply hensel_rootline_closure 6 138 1062347 70499 19399380 1287373
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 24310, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24310 (mod 46189)}. -/
theorem mod23_rootline_partial_r24310_c2 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 116688) := by
  apply hensel_rootline_closure 2 46 1062347 116688 58198140 6392473
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 24310, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24310 (mod 46189)}. -/
theorem mod23_rootline_partial_r24310_c11 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 532389) := by
  apply hensel_rootline_closure 12 276 1062347 532389 9699690 4860943
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 24310, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24310 (mod 46189)}. -/
theorem mod23_rootline_partial_r24310_c13 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 624767) := by
  apply hensel_rootline_closure 4 92 1062347 624767 29099070 17113183
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 24310, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24310 (mod 46189)}. -/
theorem mod23_rootline_partial_r24310_c19 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 901901) := by
  apply hensel_rootline_closure 3 69 1062347 901901 38798760 32938993
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c0 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 24453) := by
  apply hensel_rootline_closure 6 138 1062347 24453 19399380 446533
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c1 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 70642) := by
  apply hensel_rootline_closure 2 46 1062347 70642 58198140 3869953
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c6 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 301587) := by
  apply hensel_rootline_closure 28 10948 1062347 301587 244530 69419
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c10 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 486343) := by
  apply hensel_rootline_closure 12 276 1062347 486343 9699690 4440523
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c12 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 578721) := by
  apply hensel_rootline_closure 4 92 1062347 578721 29099070 15851923
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 24453, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 24453 (mod 46189)}. -/
theorem mod23_rootline_partial_r24453_c18 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 855855) := by
  apply hensel_rootline_closure 3 69 1062347 855855 38798760 31257313
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c5 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 256113) := by
  apply hensel_rootline_closure 12 276 1062347 256113 9699690 2338423
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c7 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 348491) := by
  apply hensel_rootline_closure 4 92 1062347 348491 29099070 9545623
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c10 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 487058) := by
  apply hensel_rootline_closure 15 5865 1062347 487058 456456 209273
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c12 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 579436) := by
  apply hensel_rootline_closure 30 13110 1062347 579436 204204 111379
  · intro s; omega
  · omega
  · omega
  · exact tau_13110_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c13 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 625625) := by
  apply hensel_rootline_closure 3 69 1062347 625625 38798760 22848913
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c18 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 856570) := by
  apply hensel_rootline_closure 6 138 1062347 856570 19399380 15641713
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 25168, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 25168 (mod 46189)}. -/
theorem mod23_rootline_partial_r25168_c19 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 902759) := by
  apply hensel_rootline_closure 2 46 1062347 902759 58198140 49455493
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c4 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 211926) := by
  apply hensel_rootline_closure 6 138 1062347 211926 19399380 3869953
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c5 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 258115) := by
  apply hensel_rootline_closure 2 46 1062347 258115 58198140 14140213
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c13 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 627627) := by
  apply hensel_rootline_closure 16 3128 1062347 627627 855855 505633
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c14 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 673816) := by
  apply hensel_rootline_closure 12 276 1062347 673816 9699690 6152233
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c16 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 766194) := by
  apply hensel_rootline_closure 4 92 1062347 766194 29099070 20987053
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 27170, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 27170 (mod 46189)}. -/
theorem mod23_rootline_partial_r27170_c22 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 1043328) := by
  apply hensel_rootline_closure 3 69 1062347 1043328 38798760 38104153
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c2 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 120406) := by
  apply hensel_rootline_closure 36 15732 1062347 120406 170170 19287
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c8 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 397540) := by
  apply hensel_rootline_closure 12 276 1062347 397540 9699690 3629713
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c10 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 489918) := by
  apply hensel_rootline_closure 4 92 1062347 489918 29099070 13419493
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c16 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 767052) := by
  apply hensel_rootline_closure 3 69 1062347 767052 38798760 28014073
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c19 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 905619) := by
  apply hensel_rootline_closure 14 5474 1062347 905619 489060 416909
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 21 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c21 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 997997) := by
  apply hensel_rootline_closure 6 138 1062347 997997 19399380 18224293
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 28028, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28028 (mod 46189)}. -/
theorem mod23_rootline_partial_r28028_c22 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 1044186) := by
  apply hensel_rootline_closure 2 46 1062347 1044186 58198140 57203233
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c4 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 213213) := by
  apply hensel_rootline_closure 16 3496 1062347 213213 765765 153689
  · intro s; omega
  · omega
  · omega
  · exact tau_3496_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c5 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 259402) := by
  apply hensel_rootline_closure 12 276 1062347 259402 9699690 2368453
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c7 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 351780) := by
  apply hensel_rootline_closure 4 92 1062347 351780 29099070 9635713
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c12 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 582725) := by
  apply hensel_rootline_closure 30 11730 1062347 582725 228228 125189
  · intro s; omega
  · omega
  · omega
  · exact tau_11730_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c13 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 628914) := by
  apply hensel_rootline_closure 3 69 1062347 628914 38798760 22969033
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c18 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 859859) := by
  apply hensel_rootline_closure 6 138 1062347 859859 19399380 15701773
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 28457, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 28457 (mod 46189)}. -/
theorem mod23_rootline_partial_r28457_c19 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 906048) := by
  apply hensel_rootline_closure 2 46 1062347 906048 58198140 49635673
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c1 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 75504) := by
  apply hensel_rootline_closure 4 92 1062347 75504 29099070 2068153
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c7 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 352638) := by
  apply hensel_rootline_closure 3 69 1062347 352638 38798760 12878953
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c10 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 491205) := by
  apply hensel_rootline_closure 14 6118 1062347 491205 437580 202327
  · intro s; omega
  · omega
  · omega
  · exact tau_6118_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c12 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 583583) := by
  apply hensel_rootline_closure 6 138 1062347 583583 19399380 10656733
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c13 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 629772) := by
  apply hensel_rootline_closure 2 46 1062347 629772 58198140 34500553
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c18 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 860717) := by
  apply hensel_rootline_closure 28 10948 1062347 860717 244530 198119
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 29315, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29315 (mod 46189)}. -/
theorem mod23_rootline_partial_r29315_c22 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 1045473) := by
  apply hensel_rootline_closure 12 276 1062347 1045473 9699690 9545623
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 4 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c4 :
    ∀ s : ℕ, ¬ goodOn {7} (1062347 * s + 214357) := by
  apply hensel_rootline_closure 7 3059 1062347 214357 875160 176587
  · intro s; omega
  · omega
  · omega
  · exact tau_3059_mul_prime_gt9


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c5 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 260546) := by
  apply hensel_rootline_closure 3 69 1062347 260546 38798760 9515593
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c10 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 491491) := by
  apply hensel_rootline_closure 6 138 1062347 491491 19399380 8975053
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c11 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 537680) := by
  apply hensel_rootline_closure 2 46 1062347 537680 58198140 29455513
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c19 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 907192) := by
  apply hensel_rootline_closure 16 3128 1062347 907192 855855 730858
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c20 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 953381) := by
  apply hensel_rootline_closure 12 276 1062347 953381 9699690 8704783
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 29601, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 29601 (mod 46189)}. -/
theorem mod23_rootline_partial_r29601_c22 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 1045759) := by
  apply hensel_rootline_closure 4 92 1062347 1045759 29099070 28644703
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 6 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c6 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 308737) := by
  apply hensel_rootline_closure 12 276 1062347 308737 9699690 2818903
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c8 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 401115) := by
  apply hensel_rootline_closure 4 92 1062347 401115 29099070 10987063
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c11 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 539682) := by
  apply hensel_rootline_closure 15 6555 1062347 539682 408408 207475
  · intro s; omega
  · omega
  · omega
  · exact tau_6555_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c14 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 678249) := by
  apply hensel_rootline_closure 3 69 1062347 678249 38798760 24770833
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c19 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 909194) := by
  apply hensel_rootline_closure 6 138 1062347 909194 19399380 16602673
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 31603, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 31603 (mod 46189)}. -/
theorem mod23_rootline_partial_r31603_c20 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 955383) := by
  apply hensel_rootline_closure 2 46 1062347 955383 58198140 52338373
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c2 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 124410) := by
  apply hensel_rootline_closure 16 3128 1062347 124410 855855 100228
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c3 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 170599) := by
  apply hensel_rootline_closure 12 276 1062347 170599 9699690 1557643
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c5 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 262977) := by
  apply hensel_rootline_closure 4 92 1062347 262977 29099070 7203283
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c11 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 540111) := by
  apply hensel_rootline_closure 3 69 1062347 540111 38798760 19725793
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c14 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 678678) := by
  apply hensel_rootline_closure 14 6118 1062347 678678 437580 279547
  · intro s; omega
  · omega
  · omega
  · exact tau_6118_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c15 :
    ∀ s : ℕ, ¬ goodOn {33} (1062347 * s + 724867) := by
  apply hensel_rootline_closure 33 245157 1062347 724867 10920 7451
  · intro s; omega
  · omega
  · omega
  · exact tau_245157_mul_prime_gt35


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c16 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 771056) := by
  apply hensel_rootline_closure 6 138 1062347 771056 19399380 14080153
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 32032, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32032 (mod 46189)}. -/
theorem mod23_rootline_partial_r32032_c17 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 817245) := by
  apply hensel_rootline_closure 2 46 1062347 817245 58198140 44770813
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c0 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 32461) := by
  apply hensel_rootline_closure 12 276 1062347 32461 9699690 296383
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c2 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 124839) := by
  apply hensel_rootline_closure 4 92 1062347 124839 29099070 3419503
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c5 :
    ∀ s : ℕ, ¬ goodOn {15} (1062347 * s + 263406) := by
  apply hensel_rootline_closure 15 5865 1062347 263406 456456 113177
  · intro s; omega
  · omega
  · omega
  · exact tau_5865_mul_prime_gt17


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c8 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 401973) := by
  apply hensel_rootline_closure 3 69 1062347 401973 38798760 14680753
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c13 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 632918) := by
  apply hensel_rootline_closure 6 138 1062347 632918 19399380 11557633
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c14 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 679107) := by
  apply hensel_rootline_closure 2 46 1062347 679107 58198140 37203253
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 32461, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 32461 (mod 46189)}. -/
theorem mod23_rootline_partial_r32461_c18 :
    ∀ s : ℕ, ¬ goodOn {32} (1062347 * s + 863863) := by
  apply hensel_rootline_closure 32 59432 1062347 863863 45045 36629
  · intro s; omega
  · omega
  · omega
  · exact tau_59432_mul_prime_gt34


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c3 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 173888) := by
  apply hensel_rootline_closure 12 276 1062347 173888 9699690 1587673
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 5 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c5 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 266266) := by
  apply hensel_rootline_closure 4 92 1062347 266266 29099070 7293373
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c11 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 543400) := by
  apply hensel_rootline_closure 3 69 1062347 543400 38798760 19845913
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c14 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 681967) := by
  apply hensel_rootline_closure 14 5474 1062347 681967 489060 313949
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c16 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 774345) := by
  apply hensel_rootline_closure 6 138 1062347 774345 19399380 14140213
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 35321, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 35321 (mod 46189)}. -/
theorem mod23_rootline_partial_r35321_c17 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 820534) := by
  apply hensel_rootline_closure 2 46 1062347 820534 58198140 44950993
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 2 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c2 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 128986) := by
  apply hensel_rootline_closure 3 69 1062347 128986 38798760 4710793
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 7 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c7 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 359931) := by
  apply hensel_rootline_closure 6 138 1062347 359931 19399380 6572653
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 8 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c8 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 406120) := by
  apply hensel_rootline_closure 2 46 1062347 406120 58198140 22248313
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 13 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c13 :
    ∀ s : ℕ, ¬ goodOn {28} (1062347 * s + 637065) := by
  apply hensel_rootline_closure 28 10948 1062347 637065 244530 146639
  · intro s; omega
  · omega
  · omega
  · exact tau_10948_mul_prime_gt30


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c16 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 775632) := by
  apply hensel_rootline_closure 16 3496 1062347 775632 765765 559094
  · intro s; omega
  · omega
  · omega
  · exact tau_3496_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c17 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 821821) := by
  apply hensel_rootline_closure 12 276 1062347 821821 9699690 7503583
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 36608, s ≡ 19 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 36608 (mod 46189)}. -/
theorem mod23_rootline_partial_r36608_c19 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 914199) := by
  apply hensel_rootline_closure 4 92 1062347 914199 29099070 25041103
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c0 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 37752) := by
  apply hensel_rootline_closure 2 46 1062347 37752 58198140 2068153
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c9 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 453453) := by
  apply hensel_rootline_closure 12 276 1062347 453453 9699690 4140223
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 11 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c11 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 545831) := by
  apply hensel_rootline_closure 4 92 1062347 545831 29099070 14951023
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 16 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c16 :
    ∀ s : ℕ, ¬ goodOn {7} (1062347 * s + 776776) := by
  apply hensel_rootline_closure 7 3059 1062347 776776 875160 639907
  · intro s; omega
  · omega
  · omega
  · exact tau_3059_mul_prime_gt9


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c17 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 822965) := by
  apply hensel_rootline_closure 3 69 1062347 822965 38798760 30056113
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 20 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c20 :
    ∀ s : ℕ, ¬ goodOn {14} (1062347 * s + 961532) := by
  apply hensel_rootline_closure 14 5474 1062347 961532 489060 442649
  · intro s; omega
  · omega
  · omega
  · exact tau_5474_mul_prime_gt16


/-- Mod-23 rootline partial certificate at residue r = 37752, s ≡ 22 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 37752 (mod 46189)}. -/
theorem mod23_rootline_partial_r37752_c22 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 1053910) := by
  apply hensel_rootline_closure 6 138 1062347 1053910 19399380 19245313
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c1 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 85085) := by
  apply hensel_rootline_closure 12 276 1062347 85085 9699690 776863
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 3 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c3 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 177463) := by
  apply hensel_rootline_closure 4 92 1062347 177463 29099070 4860943
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c9 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 454597) := by
  apply hensel_rootline_closure 3 69 1062347 454597 38798760 16602673
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 14 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c14 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 685542) := by
  apply hensel_rootline_closure 6 138 1062347 685542 19399380 12518593
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 15 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c15 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 731731) := by
  apply hensel_rootline_closure 2 46 1062347 731731 58198140 40086133
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 38896, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 38896 (mod 46189)}. -/
theorem mod23_rootline_partial_r38896_c18 :
    ∀ s : ℕ, ¬ goodOn {36} (1062347 * s + 870298) := by
  apply hensel_rootline_closure 36 15732 1062347 870298 170170 139407
  · intro s; omega
  · omega
  · omega
  · exact tau_15732_mul_prime_gt38


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 0 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c0 :
    ∀ s : ℕ, ¬ goodOn {6} (1062347 * s + 44187) := by
  apply hensel_rootline_closure 6 138 1062347 44187 19399380 806893
  · intro s; omega
  · omega
  · omega
  · exact tau_138_mul_prime_gt8


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 1 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c1 :
    ∀ s : ℕ, ¬ goodOn {2} (1062347 * s + 90376) := by
  apply hensel_rootline_closure 2 46 1062347 90376 58198140 4951033
  · intro s; omega
  · omega
  · omega
  · exact tau_46_mul_prime_gt4


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 9 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c9 :
    ∀ s : ℕ, ¬ goodOn {16} (1062347 * s + 459888) := by
  apply hensel_rootline_closure 16 3128 1062347 459888 855855 370498
  · intro s; omega
  · omega
  · omega
  · exact tau_3128_mul_prime_gt18


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 10 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c10 :
    ∀ s : ℕ, ¬ goodOn {12} (1062347 * s + 506077) := by
  apply hensel_rootline_closure 12 276 1062347 506077 9699690 4620703
  · intro s; omega
  · omega
  · omega
  · exact tau_276_mul_prime_gt14


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 12 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c12 :
    ∀ s : ℕ, ¬ goodOn {4} (1062347 * s + 598455) := by
  apply hensel_rootline_closure 4 92 1062347 598455 29099070 16392463
  · intro s; omega
  · omega
  · omega
  · exact tau_92_mul_prime_gt6


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 17 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c17 :
    ∀ s : ℕ, ¬ goodOn {30} (1062347 * s + 829400) := by
  apply hensel_rootline_closure 30 13110 1062347 829400 204204 159427
  · intro s; omega
  · omega
  · omega
  · exact tau_13110_mul_prime_gt32


/-- Mod-23 rootline partial certificate at residue r = 44187, s ≡ 18 (mod 23). Closes a sub-AP of relative density 1/23 inside the base AP {N ≡ 44187 (mod 46189)}. -/
theorem mod23_rootline_partial_r44187_c18 :
    ∀ s : ℕ, ¬ goodOn {3} (1062347 * s + 875589) := by
  apply hensel_rootline_closure 3 69 1062347 875589 38798760 31978033
  · intro s; omega
  · omega
  · omega
  · exact tau_69_mul_prime_gt5

