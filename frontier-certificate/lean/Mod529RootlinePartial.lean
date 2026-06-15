import Mathlib
import Erdos647V23HenselCore

open Nat Finset Erdos647V23Hensel Erdos647QuotientCover

-- Auto-generated. Mod-529 rootline partial certificates inside the OPEN mod-23 classes at the 41 frontier residues mod 46189.
-- Each theorem closes a sub-AP of relative density 1/529 inside its base AP via hensel_rootline_closure.
-- Coverage NOT covered by Mod23RootlinePartial (which closes entire mod-23 classes — these are inside the remaining open ones).
-- Total candidates: 362
-- Source: scripts/codegen_mod529_rootline.py

set_option maxHeartbeats 16000000

lemma tau_529_mul_prime_gt3 :
    ∀ p : ℕ, p.Prime → (529 * p).divisors.card > 3 := by
  intro p hp
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 529 := by
      intro hdvd
      have hmem : p ∈ (529 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (529 : ℕ).primeFactors = {23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl <;> contradiction
    have hcop : Nat.Coprime 529 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_2645_mul_prime_gt7 :
    ∀ p : ℕ, p.Prime → (2645 * p).divisors.card > 7 := by
  intro p hp
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 2645 := by
      intro hdvd
      have hmem : p ∈ (2645 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (2645 : ℕ).primeFactors = {5, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 2645 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_4232_mul_prime_gt10 :
    ∀ p : ℕ, p.Prime → (4232 * p).divisors.card > 10 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 4232 := by
      intro hdvd
      have hmem : p ∈ (4232 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (4232 : ℕ).primeFactors = {2, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 4232 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_4761_mul_prime_gt11 :
    ∀ p : ℕ, p.Prime → (4761 * p).divisors.card > 11 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 4761 := by
      intro hdvd
      have hmem : p ∈ (4761 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (4761 : ℕ).primeFactors = {3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 4761 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_5290_mul_prime_gt12 :
    ∀ p : ℕ, p.Prime → (5290 * p).divisors.card > 12 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 5290 := by
      intro hdvd
      have hmem : p ∈ (5290 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (5290 : ℕ).primeFactors = {2, 5, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 5290 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_98923_mul_prime_gt13 :
    ∀ p : ℕ, p.Prime → (98923 * p).divisors.card > 13 := by
  intro p hp
  by_cases h11 : p = 11
  · subst h11; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 98923 := by
      intro hdvd
      have hmem : p ∈ (98923 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (98923 : ℕ).primeFactors = {11, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 98923 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_110561_mul_prime_gt13 :
    ∀ p : ℕ, p.Prime → (110561 * p).divisors.card > 13 := by
  intro p hp
  by_cases h11 : p = 11
  · subst h11; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 110561 := by
      intro hdvd
      have hmem : p ∈ (110561 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (110561 : ℕ).primeFactors = {11, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 110561 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_116909_mul_prime_gt15 :
    ∀ p : ℕ, p.Prime → (116909 * p).divisors.card > 15 := by
  intro p hp
  by_cases h13 : p = 13
  · subst h13; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 116909 := by
      intro hdvd
      have hmem : p ∈ (116909 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (116909 : ℕ).primeFactors = {13, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 116909 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_130663_mul_prime_gt15 :
    ∀ p : ℕ, p.Prime → (130663 * p).divisors.card > 15 := by
  intro p hp
  by_cases h13 : p = 13
  · subst h13; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 130663 := by
      intro hdvd
      have hmem : p ∈ (130663 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (130663 : ℕ).primeFactors = {13, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 130663 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_9522_mul_prime_gt20 :
    ∀ p : ℕ, p.Prime → (9522 * p).divisors.card > 20 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 9522 := by
      intro hdvd
      have hmem : p ∈ (9522 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (9522 : ℕ).primeFactors = {2, 3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 9522 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_10580_mul_prime_gt22 :
    ∀ p : ℕ, p.Prime → (10580 * p).divisors.card > 22 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 10580 := by
      intro hdvd
      have hmem : p ∈ (10580 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (10580 : ℕ).primeFactors = {2, 5, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 10580 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_12696_mul_prime_gt26 :
    ∀ p : ℕ, p.Prime → (12696 * p).divisors.card > 26 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 12696 := by
      intro hdvd
      have hmem : p ∈ (12696 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (12696 : ℕ).primeFactors = {2, 3, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 12696 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_404685_mul_prime_gt47 :
    ∀ p : ℕ, p.Prime → (404685 * p).divisors.card > 47 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 404685 := by
      intro hdvd
      have hmem : p ∈ (404685 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (404685 : ℕ).primeFactors = {3, 5, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 404685 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_452295_mul_prime_gt47 :
    ∀ p : ℕ, p.Prime → (452295 * p).divisors.card > 47 := by
  intro p hp
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h5 : p = 5
  · subst h5; native_decide
  by_cases h19 : p = 19
  · subst h19; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 452295 := by
      intro hdvd
      have hmem : p ∈ (452295 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (452295 : ℕ).primeFactors = {3, 5, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 452295 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_755412_mul_prime_gt86 :
    ∀ p : ℕ, p.Prime → (755412 * p).divisors.card > 86 := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; native_decide
  by_cases h3 : p = 3
  · subst h3; native_decide
  by_cases h7 : p = 7
  · subst h7; native_decide
  by_cases h17 : p = 17
  · subst h17; native_decide
  by_cases h23 : p = 23
  · subst h23; native_decide
  · have hndvd : ¬ p ∣ 755412 := by
      intro hdvd
      have hmem : p ∈ (755412 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (755412 : ℕ).primeFactors = {2, 3, 7, 17, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 755412 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


lemma tau_904590_mul_prime_gt92 :
    ∀ p : ℕ, p.Prime → (904590 * p).divisors.card > 92 := by
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
  · have hndvd : ¬ p ∣ 904590 := by
      intro hdvd
      have hmem : p ∈ (904590 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, by norm_num⟩
      have hpf : (904590 : ℕ).primeFactors = {2, 3, 5, 19, 23} := by native_decide
      rw [hpf] at hmem
      simp at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;> contradiction
    have hcop : Nat.Coprime 904590 p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
    rw [hcop.card_divisors_mul, hp.divisors, Finset.card_pair hp.one_lt.ne]
    native_decide


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 191 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s191 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 8822099) := by
  apply hensel_rootline_closure 18 9522 24433981 8822099 6466460 2334771
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 400 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s400 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 18475600) := by
  apply hensel_rootline_closure 10 5290 24433981 18475600 11639628 8801231
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 360 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s360 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 16628040) := by
  apply hensel_rootline_closure 9 4761 24433981 16628040 12932920 8801231
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 200 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s200 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 9237800) := by
  apply hensel_rootline_closure 5 2645 24433981 9237800 23279256 8801231
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 40 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s40 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 1847560) := by
  apply hensel_rootline_closure 1 529 24433981 1847560 116396280 8801231
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 431 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s431 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 19907459) := by
  apply hensel_rootline_closure 24 12696 24433981 19907459 4849845 3951386
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 271 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s271 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 12517219) := by
  apply hensel_rootline_closure 20 10580 24433981 12517219 5819814 2981417
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 0, s ≡ 320 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r0_s320 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 14780480) := by
  apply hensel_rootline_closure 8 4232 24433981 14780480 14549535 8801231
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 1 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s1 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 47047) := by
  apply hensel_rootline_closure 18 9522 24433981 47047 6466460 12451
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 210 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s210 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 9700548) := by
  apply hensel_rootline_closure 10 5290 24433981 9700548 11639628 4621055
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 170 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s170 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 7852988) := by
  apply hensel_rootline_closure 9 4761 24433981 7852988 12932920 4156591
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 10 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s10 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 462748) := by
  apply hensel_rootline_closure 5 2645 24433981 462748 23279256 440879
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 241 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s241 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 11132407) := by
  apply hensel_rootline_closure 24 12696 24433981 11132407 4849845 2209646
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 379 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s379 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 17506489) := by
  apply hensel_rootline_closure 1 529 24433981 17506489 116396280 83395751
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 81 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s81 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 3742167) := by
  apply hensel_rootline_closure 20 10580 24433981 3742167 5819814 891329
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 858, s ≡ 130 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r858_s130 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 6005428) := by
  apply hensel_rootline_closure 8 4232 24433981 6005428 14549535 3576011
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 115 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s115 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 5313022) := by
  apply hensel_rootline_closure 10 5290 24433981 5313022 11639628 2530967
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 75 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s75 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 3465462) := by
  apply hensel_rootline_closure 9 4761 24433981 3465462 12932920 1834271
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 444 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s444 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 20509203) := by
  apply hensel_rootline_closure 5 2645 24433981 20509203 23279256 19539959
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 146 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s146 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 6744881) := by
  apply hensel_rootline_closure 24 12696 24433981 6744881 4849845 1338776
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 284 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s284 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 13118963) := by
  apply hensel_rootline_closure 1 529 24433981 13118963 116396280 62494871
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 515 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s515 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 23788622) := by
  apply hensel_rootline_closure 20 10580 24433981 23788622 5819814 5666099
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 35 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s35 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 1617902) := by
  apply hensel_rootline_closure 8 4232 24433981 1617902 14549535 963401
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 1287, s ≡ 435 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1287_s435 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 20093502) := by
  apply hensel_rootline_closure 18 9522 24433981 20093502 6466460 5317751
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 140 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s140 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 6468176) := by
  apply hensel_rootline_closure 13 116909 24433981 6468176 526680 139423
  · intro s; omega
  · omega
  · omega
  · exact tau_116909_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 509 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s509 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 23511917) := by
  apply hensel_rootline_closure 9 4761 24433981 23511917 12932920 12444871
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 349 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s349 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 16121677) := by
  apply hensel_rootline_closure 5 2645 24433981 16121677 23279256 15359783
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 51 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s51 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 2357355) := by
  apply hensel_rootline_closure 24 12696 24433981 2357355 4849845 467906
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 189 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s189 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 8731437) := by
  apply hensel_rootline_closure 1 529 24433981 8731437 116396280 41593991
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 420 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s420 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 19401096) := by
  apply hensel_rootline_closure 20 10580 24433981 19401096 5819814 4621055
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 469 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s469 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 21664357) := by
  apply hensel_rootline_closure 8 4232 24433981 21664357 14549535 12900326
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 340 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s340 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 15705976) := by
  apply hensel_rootline_closure 18 9522 24433981 15705976 6466460 4156591
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 1716, s ≡ 20 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r1716_s20 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 925496) := by
  apply hensel_rootline_closure 10 5290 24433981 925496 11639628 440879
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 69 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s69 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 3189472) := by
  apply hensel_rootline_closure 24 12696 24433981 3189472 4849845 633071
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 207 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s207 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 9563554) := by
  apply hensel_rootline_closure 1 529 24433981 9563554 116396280 45557951
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 438 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s438 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 20233213) := by
  apply hensel_rootline_closure 20 10580 24433981 20233213 5819814 4819253
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 487 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s487 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 22496474) := by
  apply hensel_rootline_closure 8 4232 24433981 22496474 14549535 13395821
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 380 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s380 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 17554251) := by
  apply hensel_rootline_closure 45 452295 24433981 17554251 136136 97805
  · intro s; omega
  · omega
  · omega
  · exact tau_452295_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 358 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s358 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 16538093) := by
  apply hensel_rootline_closure 18 9522 24433981 16538093 6466460 4376811
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 38 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s38 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 1757613) := by
  apply hensel_rootline_closure 10 5290 24433981 1757613 11639628 837275
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 527 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s527 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 24344034) := by
  apply hensel_rootline_closure 9 4761 24433981 24344034 12932920 12885311
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 2431, s ≡ 367 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2431_s367 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 16953794) := by
  apply hensel_rootline_closure 5 2645 24433981 16953794 23279256 16152575
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 230 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s230 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 10626044) := by
  apply hensel_rootline_closure 20 10580 24433981 10626044 5819814 2530967
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 279 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s279 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 12889305) := by
  apply hensel_rootline_closure 8 4232 24433981 12889305 14549535 7675106
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 399 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s399 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 18431985) := by
  apply hensel_rootline_closure 11 98923 24433981 18431985 622440 469543
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 172 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s172 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 7947082) := by
  apply hensel_rootline_closure 45 404685 24433981 7947082 152152 49487
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 150 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s150 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 6930924) := by
  apply hensel_rootline_closure 18 9522 24433981 6930924 6466460 1834271
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 359 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s359 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 16584425) := by
  apply hensel_rootline_closure 10 5290 24433981 16584425 11639628 7900331
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 479 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s479 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 22127105) := by
  apply hensel_rootline_closure 13 130663 24433981 22127105 471240 426749
  · intro s; omega
  · omega
  · omega
  · exact tau_130663_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 319 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s319 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 14736865) := by
  apply hensel_rootline_closure 9 4761 24433981 14736865 12932920 7800231
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 390 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s390 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 18016284) := by
  apply hensel_rootline_closure 24 12696 24433981 18016284 4849845 3576011
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 2574, s ≡ 528 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r2574_s528 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 24390366) := by
  apply hensel_rootline_closure 1 529 24433981 24390366 116396280 116188511
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 231 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s231 :
    ∀ s : ℕ, ¬ goodOn {90} (24433981 * s + 10674521) := by
  apply hensel_rootline_closure 90 904590 24433981 10674521 68068 29737
  · intro s; omega
  · omega
  · omega
  · exact tau_904590_mul_prime_gt92


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 165 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s165 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 7626047) := by
  apply hensel_rootline_closure 9 4761 24433981 7626047 12932920 4036471
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 5 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s5 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 235807) := by
  apply hensel_rootline_closure 5 2645 24433981 235807 23279256 224663
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 236 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s236 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 10905466) := by
  apply hensel_rootline_closure 24 12696 24433981 10905466 4849845 2164601
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 374 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s374 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 17279548) := by
  apply hensel_rootline_closure 1 529 24433981 17279548 116396280 82314671
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 76 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s76 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 3515226) := by
  apply hensel_rootline_closure 20 10580 24433981 3515226 5819814 837275
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 125 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s125 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 5778487) := by
  apply hensel_rootline_closure 8 4232 24433981 5778487 14549535 3440876
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 525 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s525 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 24254087) := by
  apply hensel_rootline_closure 18 9522 24433981 24254087 6466460 6418851
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 4862, s ≡ 205 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r4862_s205 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 9473607) := by
  apply hensel_rootline_closure 10 5290 24433981 9473607 11639628 4512947
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 230 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s230 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 10628761) := by
  apply hensel_rootline_closure 13 130663 24433981 10628761 471240 204989
  · intro s; omega
  · omega
  · omega
  · exact tau_130663_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 70 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s70 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 3238521) := by
  apply hensel_rootline_closure 9 4761 24433981 3238521 12932920 1714151
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 439 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s439 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 20282262) := by
  apply hensel_rootline_closure 5 2645 24433981 20282262 23279256 19323743
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 141 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s141 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 6517940) := by
  apply hensel_rootline_closure 24 12696 24433981 6517940 4849845 1293731
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 279 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s279 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 12892022) := by
  apply hensel_rootline_closure 1 529 24433981 12892022 116396280 61413791
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 510 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s510 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 23561681) := by
  apply hensel_rootline_closure 20 10580 24433981 23561681 5819814 5612045
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 30 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s30 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 1390961) := by
  apply hensel_rootline_closure 8 4232 24433981 1390961 14549535 828266
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 425 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s425 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 19635616) := by
  apply hensel_rootline_closure 84 755412 24433981 19635616 81510 65503
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 430 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s430 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 19866561) := by
  apply hensel_rootline_closure 18 9522 24433981 19866561 6466460 5257691
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 5291, s ≡ 110 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r5291_s110 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 5086081) := by
  apply hensel_rootline_closure 10 5290 24433981 5086081 11639628 2422859
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 369 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s369 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 17049890) := by
  apply hensel_rootline_closure 8 4232 24433981 17049890 14549535 10152581
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 489 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s489 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 22592570) := by
  apply hensel_rootline_closure 11 110561 24433981 22592570 556920 514949
  · intro s; omega
  · omega
  · omega
  · exact tau_110561_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 240 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s240 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 11091509) := by
  apply hensel_rootline_closure 18 9522 24433981 11091509 6466460 2935371
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 449 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s449 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 20745010) := by
  apply hensel_rootline_closure 10 5290 24433981 20745010 11639628 9882311
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 409 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s409 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 18897450) := by
  apply hensel_rootline_closure 9 4761 24433981 18897450 12932920 10002431
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 249 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s249 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 11507210) := by
  apply hensel_rootline_closure 5 2645 24433981 11507210 23279256 10963391
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 89 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s89 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 4116970) := by
  apply hensel_rootline_closure 1 529 24433981 4116970 116396280 19612031
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 480 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s480 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 22176869) := by
  apply hensel_rootline_closure 24 12696 24433981 22176869 4849845 4401836
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 6149, s ≡ 320 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r6149_s320 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 14786629) := by
  apply hensel_rootline_closure 20 10580 24433981 14786629 5819814 3521957
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 142 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s142 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 6566989) := by
  apply hensel_rootline_closure 9 4761 24433981 6566989 12932920 3475911
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 511 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s511 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 23610730) := by
  apply hensel_rootline_closure 5 2645 24433981 23610730 23279256 22494911
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 213 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s213 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 9846408) := by
  apply hensel_rootline_closure 24 12696 24433981 9846408 4849845 1954391
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 351 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s351 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 16220490) := by
  apply hensel_rootline_closure 1 529 24433981 16220490 116396280 77269631
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 53 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s53 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 2456168) := by
  apply hensel_rootline_closure 20 10580 24433981 2456168 5819814 585023
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 102 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s102 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 4719429) := by
  apply hensel_rootline_closure 8 4232 24433981 4719429 14549535 2810246
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 502 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s502 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 23195029) := by
  apply hensel_rootline_closure 18 9522 24433981 23195029 6466460 6138571
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 8151, s ≡ 182 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r8151_s182 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 8414549) := by
  apply hensel_rootline_closure 10 5290 24433981 8414549 11639628 4008443
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 23 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s23 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 1071356) := by
  apply hensel_rootline_closure 24 12696 24433981 1071356 4849845 212651
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 161 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s161 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 7445438) := by
  apply hensel_rootline_closure 1 529 24433981 7445438 116396280 35467871
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 392 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s392 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 18115097) := by
  apply hensel_rootline_closure 20 10580 24433981 18115097 5819814 4314749
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 441 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s441 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 20378358) := by
  apply hensel_rootline_closure 8 4232 24433981 20378358 14549535 12134561
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 312 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s312 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 14419977) := by
  apply hensel_rootline_closure 18 9522 24433981 14419977 6466460 3816251
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 521 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s521 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 24073478) := by
  apply hensel_rootline_closure 10 5290 24433981 24073478 11639628 11467895
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 481 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s481 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 22225918) := by
  apply hensel_rootline_closure 9 4761 24433981 22225918 12932920 11764191
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 9009, s ≡ 321 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9009_s321 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 14835678) := by
  apply hensel_rootline_closure 5 2645 24433981 14835678 23279256 14134559
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 371 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s371 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 17145986) := by
  apply hensel_rootline_closure 11 98923 24433981 17145986 622440 436783
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 144 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s144 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 6661083) := by
  apply hensel_rootline_closure 45 404685 24433981 6661083 152152 41479
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 122 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s122 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 5644925) := by
  apply hensel_rootline_closure 18 9522 24433981 5644925 6466460 1493931
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 331 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s331 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 15298426) := by
  apply hensel_rootline_closure 10 5290 24433981 15298426 11639628 7287719
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 291 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s291 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 13450866) := by
  apply hensel_rootline_closure 9 4761 24433981 13450866 12932920 7119551
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 362 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s362 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 16730285) := by
  apply hensel_rootline_closure 24 12696 24433981 16730285 4849845 3320756
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 500 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s500 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 23104367) := by
  apply hensel_rootline_closure 1 529 24433981 23104367 116396280 110062391
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 202 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s202 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 9340045) := by
  apply hensel_rootline_closure 20 10580 24433981 9340045 5819814 2224661
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 9867, s ≡ 251 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r9867_s251 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 11603306) := by
  apply hensel_rootline_closure 8 4232 24433981 11603306 14549535 6909341
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 162 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s162 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 7493200) := by
  apply hensel_rootline_closure 45 452295 24433981 7493200 136136 41749
  · intro s; omega
  · omega
  · omega
  · exact tau_452295_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 140 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s140 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 6477042) := by
  apply hensel_rootline_closure 18 9522 24433981 6477042 6466460 1714151
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 349 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s349 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 16130543) := by
  apply hensel_rootline_closure 10 5290 24433981 16130543 11639628 7684115
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 309 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s309 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 14282983) := by
  apply hensel_rootline_closure 9 4761 24433981 14282983 12932920 7559991
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 149 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s149 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 6892743) := by
  apply hensel_rootline_closure 5 2645 24433981 6892743 23279256 6566999
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 380 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s380 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 17562402) := by
  apply hensel_rootline_closure 24 12696 24433981 17562402 4849845 3485921
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 518 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s518 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 23936484) := by
  apply hensel_rootline_closure 1 529 24433981 23936484 116396280 114026351
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 220 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s220 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 10172162) := by
  apply hensel_rootline_closure 20 10580 24433981 10172162 5819814 2422859
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 10582, s ≡ 269 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r10582_s269 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 12435423) := by
  apply hensel_rootline_closure 8 4232 24433981 12435423 14549535 7404836
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 506 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s506 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 23383789) := by
  apply hensel_rootline_closure 5 2645 24433981 23383789 23279256 22278695
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 208 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s208 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 9619467) := by
  apply hensel_rootline_closure 24 12696 24433981 9619467 4849845 1909346
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 346 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s346 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 15993549) := by
  apply hensel_rootline_closure 1 529 24433981 15993549 116396280 76188551
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 48 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s48 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 2229227) := by
  apply hensel_rootline_closure 20 10580 24433981 2229227 5819814 530969
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 97 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s97 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 4492488) := by
  apply hensel_rootline_closure 8 4232 24433981 4492488 14549535 2675111
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 497 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s497 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 22968088) := by
  apply hensel_rootline_closure 18 9522 24433981 22968088 6466460 6078511
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 177 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s177 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 8187608) := by
  apply hensel_rootline_closure 10 5290 24433981 8187608 11639628 3900335
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 12155, s ≡ 137 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12155_s137 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 6340048) := by
  apply hensel_rootline_closure 9 4761 24433981 6340048 12932920 3355791
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 2 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s2 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 104962) := by
  apply hensel_rootline_closure 8 4232 24433981 104962 14549535 62501
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 402 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s402 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 18580562) := by
  apply hensel_rootline_closure 18 9522 24433981 18580562 6466460 4917351
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 82 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s82 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 3800082) := by
  apply hensel_rootline_closure 10 5290 24433981 3800082 11639628 1810247
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 42 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s42 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 1952522) := by
  apply hensel_rootline_closure 9 4761 24433981 1952522 12932920 1033471
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 411 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s411 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 18996263) := by
  apply hensel_rootline_closure 5 2645 24433981 18996263 23279256 18098519
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 113 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s113 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 5231941) := by
  apply hensel_rootline_closure 24 12696 24433981 5231941 4849845 1038476
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 251 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s251 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 11606023) := by
  apply hensel_rootline_closure 1 529 24433981 11606023 116396280 55287671
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 12584, s ≡ 482 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r12584_s482 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 22275682) := by
  apply hensel_rootline_closure 20 10580 24433981 22275682 5819814 5305739
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 307 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s307 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 14193036) := by
  apply hensel_rootline_closure 18 9522 24433981 14193036 6466460 3756191
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 516 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s516 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 23846537) := by
  apply hensel_rootline_closure 10 5290 24433981 23846537 11639628 11359787
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 13 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s13 :
    ∀ s : ℕ, ¬ goodOn {90} (24433981 * s + 613470) := by
  apply hensel_rootline_closure 90 904590 24433981 613470 68068 1709
  · intro s; omega
  · omega
  · omega
  · exact tau_904590_mul_prime_gt92


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 476 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s476 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 21998977) := by
  apply hensel_rootline_closure 9 4761 24433981 21998977 12932920 11644071
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 316 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s316 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 14608737) := by
  apply hensel_rootline_closure 5 2645 24433981 14608737 23279256 13918343
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 18 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s18 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 844415) := by
  apply hensel_rootline_closure 24 12696 24433981 844415 4849845 167606
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 156 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s156 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 7218497) := by
  apply hensel_rootline_closure 1 529 24433981 7218497 116396280 34386791
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 387 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s387 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 17888156) := by
  apply hensel_rootline_closure 20 10580 24433981 17888156 5819814 4260695
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 13013, s ≡ 436 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13013_s436 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 20151417) := by
  apply hensel_rootline_closure 8 4232 24433981 20151417 14549535 11999426
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 212 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s212 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 9805510) := by
  apply hensel_rootline_closure 18 9522 24433981 9805510 6466460 2595031
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 421 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s421 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 19459011) := by
  apply hensel_rootline_closure 10 5290 24433981 19459011 11639628 9269699
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 12 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s12 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 567710) := by
  apply hensel_rootline_closure 13 130663 24433981 567710 471240 10949
  · intro s; omega
  · omega
  · omega
  · exact tau_130663_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 381 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s381 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 17611451) := by
  apply hensel_rootline_closure 9 4761 24433981 17611451 12932920 9321751
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 221 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s221 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 10221211) := by
  apply hensel_rootline_closure 5 2645 24433981 10221211 23279256 9738167
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 61 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s61 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 2830971) := by
  apply hensel_rootline_closure 1 529 24433981 2830971 116396280 13485911
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 452 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s452 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 20890870) := by
  apply hensel_rootline_closure 24 12696 24433981 20890870 4849845 4146581
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 292 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s292 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 13500630) := by
  apply hensel_rootline_closure 20 10580 24433981 13500630 5819814 3215651
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 13442, s ≡ 341 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r13442_s341 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 15763891) := by
  apply hensel_rootline_closure 8 4232 24433981 15763891 14549535 9386816
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 284 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s284 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 13133978) := by
  apply hensel_rootline_closure 18 9522 24433981 13133978 6466460 3475911
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 493 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s493 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 22787479) := by
  apply hensel_rootline_closure 10 5290 24433981 22787479 11639628 10855283
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 84 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s84 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 3896178) := by
  apply hensel_rootline_closure 13 116909 24433981 3896178 526680 83983
  · intro s; omega
  · omega
  · omega
  · exact tau_116909_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 453 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s453 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 20939919) := by
  apply hensel_rootline_closure 9 4761 24433981 20939919 12932920 11083511
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 293 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s293 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 13549679) := by
  apply hensel_rootline_closure 5 2645 24433981 13549679 23279256 12909335
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 133 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s133 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 6159439) := by
  apply hensel_rootline_closure 1 529 24433981 6159439 116396280 29341751
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 524 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s524 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 24219338) := by
  apply hensel_rootline_closure 24 12696 24433981 24219338 4849845 4807241
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 364 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s364 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 16829098) := by
  apply hensel_rootline_closure 20 10580 24433981 16829098 5819814 4008443
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 16302, s ≡ 413 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r16302_s413 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 19092359) := by
  apply hensel_rootline_closure 8 4232 24433981 19092359 14549535 11368796
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 302 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s302 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 13966095) := by
  apply hensel_rootline_closure 18 9522 24433981 13966095 6466460 3696131
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 511 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s511 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 23619596) := by
  apply hensel_rootline_closure 10 5290 24433981 23619596 11639628 11251679
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 471 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s471 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 21772036) := by
  apply hensel_rootline_closure 9 4761 24433981 21772036 12932920 11523951
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 311 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s311 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 14381796) := by
  apply hensel_rootline_closure 5 2645 24433981 14381796 23279256 13702127
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 13 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s13 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 617474) := by
  apply hensel_rootline_closure 24 12696 24433981 617474 4849845 122561
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 151 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s151 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 6991556) := by
  apply hensel_rootline_closure 1 529 24433981 6991556 116396280 33305711
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 382 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s382 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 17661215) := by
  apply hensel_rootline_closure 20 10580 24433981 17661215 5819814 4206641
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 431 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s431 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 19924476) := by
  apply hensel_rootline_closure 8 4232 24433981 19924476 14549535 11864291
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 17017, s ≡ 22 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17017_s22 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 1033175) := by
  apply hensel_rootline_closure 11 110561 24433981 1033175 556920 23549
  · intro s; omega
  · omega
  · omega
  · exact tau_110561_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 116 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s116 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 5375084) := by
  apply hensel_rootline_closure 45 404685 24433981 5375084 152152 33471
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 94 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s94 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 4358926) := by
  apply hensel_rootline_closure 18 9522 24433981 4358926 6466460 1153591
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 303 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s303 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 14012427) := by
  apply hensel_rootline_closure 10 5290 24433981 14012427 11639628 6675107
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 263 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s263 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 12164867) := by
  apply hensel_rootline_closure 9 4761 24433981 12164867 12932920 6438871
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 334 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s334 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 15444286) := by
  apply hensel_rootline_closure 24 12696 24433981 15444286 4849845 3065501
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 472 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s472 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 21818368) := by
  apply hensel_rootline_closure 1 529 24433981 21818368 116396280 103936271
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 174 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s174 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 8054046) := by
  apply hensel_rootline_closure 20 10580 24433981 8054046 5819814 1918355
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 223 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s223 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 10317307) := by
  apply hensel_rootline_closure 8 4232 24433981 10317307 14549535 6143576
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 17160, s ≡ 343 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r17160_s343 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 15859987) := by
  apply hensel_rootline_closure 11 98923 24433981 15859987 622440 404023
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 460 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s460 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 21265673) := by
  apply hensel_rootline_closure 5 2645 24433981 21265673 23279256 20260679
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 162 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s162 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 7501351) := by
  apply hensel_rootline_closure 24 12696 24433981 7501351 4849845 1488926
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 300 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s300 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 13875433) := by
  apply hensel_rootline_closure 1 529 24433981 13875433 116396280 66098471
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 2 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s2 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 111111) := by
  apply hensel_rootline_closure 20 10580 24433981 111111 5819814 26465
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 51 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s51 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 2374372) := by
  apply hensel_rootline_closure 8 4232 24433981 2374372 14549535 1413851
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 473 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s473 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 21866130) := by
  apply hensel_rootline_closure 45 452295 24433981 21866130 136136 121829
  · intro s; omega
  · omega
  · omega
  · exact tau_452295_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 451 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s451 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 20849972) := by
  apply hensel_rootline_closure 18 9522 24433981 20849972 6466460 5517951
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 131 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s131 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 6069492) := by
  apply hensel_rootline_closure 10 5290 24433981 6069492 11639628 2891327
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 251 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s251 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 11612172) := by
  apply hensel_rootline_closure 13 116909 24433981 11612172 526680 250303
  · intro s; omega
  · omega
  · omega
  · exact tau_116909_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 18733, s ≡ 91 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r18733_s91 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 4221932) := by
  apply hensel_rootline_closure 9 4761 24433981 4221932 12932920 2234671
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 369 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s369 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 17063618) := by
  apply hensel_rootline_closure 84 755412 24433981 17063618 81510 56923
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 374 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s374 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 17294563) := by
  apply hensel_rootline_closure 18 9522 24433981 17294563 6466460 4577011
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 54 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s54 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 2514083) := by
  apply hensel_rootline_closure 10 5290 24433981 2514083 11639628 1197635
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 14 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s14 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 666523) := by
  apply hensel_rootline_closure 9 4761 24433981 666523 12932920 352791
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 383 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s383 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 17710264) := by
  apply hensel_rootline_closure 5 2645 24433981 17710264 23279256 16873295
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 85 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s85 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 3945942) := by
  apply hensel_rootline_closure 24 12696 24433981 3945942 4849845 783221
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 223 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s223 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 10320024) := by
  apply hensel_rootline_closure 1 529 24433981 10320024 116396280 49161551
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 454 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s454 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 20989683) := by
  apply hensel_rootline_closure 20 10580 24433981 20989683 5819814 4999433
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 19877, s ≡ 503 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r19877_s503 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 23252944) := by
  apply hensel_rootline_closure 8 4232 24433981 23252944 14549535 13846271
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 279 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s279 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 12907037) := by
  apply hensel_rootline_closure 18 9522 24433981 12907037 6466460 3415851
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 488 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s488 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 22560538) := by
  apply hensel_rootline_closure 10 5290 24433981 22560538 11639628 10747175
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 448 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s448 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 20712978) := by
  apply hensel_rootline_closure 9 4761 24433981 20712978 12932920 10963391
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 288 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s288 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 13322738) := by
  apply hensel_rootline_closure 5 2645 24433981 13322738 23279256 12693119
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 128 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s128 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 5932498) := by
  apply hensel_rootline_closure 1 529 24433981 5932498 116396280 28260671
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 519 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s519 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 23992397) := by
  apply hensel_rootline_closure 24 12696 24433981 23992397 4849845 4762196
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 359 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s359 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 16602157) := by
  apply hensel_rootline_closure 20 10580 24433981 16602157 5819814 3954389
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 20306, s ≡ 408 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20306_s408 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 18865418) := by
  apply hensel_rootline_closure 8 4232 24433981 18865418 14549535 11233661
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 184 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s184 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 8519511) := by
  apply hensel_rootline_closure 18 9522 24433981 8519511 6466460 2254691
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 393 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s393 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 18173012) := by
  apply hensel_rootline_closure 10 5290 24433981 18173012 11639628 8657087
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 353 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s353 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 16325452) := by
  apply hensel_rootline_closure 9 4761 24433981 16325452 12932920 8641071
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 193 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s193 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 8935212) := by
  apply hensel_rootline_closure 5 2645 24433981 8935212 23279256 8512943
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 33 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s33 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 1544972) := by
  apply hensel_rootline_closure 1 529 24433981 1544972 116396280 7359791
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 424 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s424 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 19604871) := by
  apply hensel_rootline_closure 24 12696 24433981 19604871 4849845 3891326
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 264 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s264 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 12214631) := by
  apply hensel_rootline_closure 20 10580 24433981 12214631 5819814 2909345
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 20735, s ≡ 313 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r20735_s313 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 14477892) := by
  apply hensel_rootline_closure 8 4232 24433981 14477892 14549535 8621051
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 324 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s324 :
    ∀ s : ℕ, ¬ goodOn {90} (24433981 * s + 14986400) := by
  apply hensel_rootline_closure 90 904590 24433981 14986400 68068 41749
  · intro s; omega
  · omega
  · omega
  · exact tau_904590_mul_prime_gt92


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 418 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s418 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 19328166) := by
  apply hensel_rootline_closure 13 116909 24433981 19328166 526680 416623
  · intro s; omega
  · omega
  · omega
  · exact tau_116909_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 258 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s258 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 11937926) := by
  apply hensel_rootline_closure 9 4761 24433981 11937926 12932920 6318751
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 98 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s98 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 4547686) := by
  apply hensel_rootline_closure 5 2645 24433981 4547686 23279256 4332767
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 329 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s329 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 15217345) := by
  apply hensel_rootline_closure 24 12696 24433981 15217345 4849845 3020456
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 467 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s467 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 21591427) := by
  apply hensel_rootline_closure 1 529 24433981 21591427 116396280 102855191
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 169 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s169 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 7827105) := by
  apply hensel_rootline_closure 20 10580 24433981 7827105 5819814 1864301
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 218 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s218 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 10090366) := by
  apply hensel_rootline_closure 8 4232 24433981 10090366 14549535 6008441
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 89 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s89 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 4131985) := by
  apply hensel_rootline_closure 18 9522 24433981 4131985 6466460 1093531
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 21164, s ≡ 298 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r21164_s298 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 13785486) := by
  apply hensel_rootline_closure 10 5290 24433981 13785486 11639628 6566999
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 483 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s483 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 22333597) := by
  apply hensel_rootline_closure 10 5290 24433981 22333597 11639628 10639067
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 74 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s74 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 3442296) := by
  apply hensel_rootline_closure 13 130663 24433981 3442296 471240 66389
  · intro s; omega
  · omega
  · omega
  · exact tau_130663_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 443 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s443 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 20486037) := by
  apply hensel_rootline_closure 9 4761 24433981 20486037 12932920 10843271
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 283 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s283 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 13095797) := by
  apply hensel_rootline_closure 5 2645 24433981 13095797 23279256 12476903
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 123 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s123 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 5705557) := by
  apply hensel_rootline_closure 1 529 24433981 5705557 116396280 27179591
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 514 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s514 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 23765456) := by
  apply hensel_rootline_closure 24 12696 24433981 23765456 4849845 4717151
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 354 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s354 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 16375216) := by
  apply hensel_rootline_closure 20 10580 24433981 16375216 5819814 3900335
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 403 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s403 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 18638477) := by
  apply hensel_rootline_closure 8 4232 24433981 18638477 14549535 11098526
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 24310, s ≡ 274 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24310_s274 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 12680096) := by
  apply hensel_rootline_closure 18 9522 24433981 12680096 6466460 3355791
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 235 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s235 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 10878868) := by
  apply hensel_rootline_closure 9 4761 24433981 10878868 12932920 5758191
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 306 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s306 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 14158287) := by
  apply hensel_rootline_closure 24 12696 24433981 14158287 4849845 2810246
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 444 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s444 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 20532369) := by
  apply hensel_rootline_closure 1 529 24433981 20532369 116396280 97810151
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 146 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s146 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 6768047) := by
  apply hensel_rootline_closure 20 10580 24433981 6768047 5819814 1612049
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 195 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s195 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 9031308) := by
  apply hensel_rootline_closure 8 4232 24433981 9031308 14549535 5377811
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 315 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s315 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 14573988) := by
  apply hensel_rootline_closure 11 98923 24433981 14573988 622440 371263
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 88 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s88 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 4089085) := by
  apply hensel_rootline_closure 45 404685 24433981 4089085 152152 25463
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 66 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s66 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 3072927) := by
  apply hensel_rootline_closure 18 9522 24433981 3072927 6466460 813251
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 24453, s ≡ 275 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r24453_s275 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 12726428) := by
  apply hensel_rootline_closure 10 5290 24433981 12726428 11639628 6062495
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 253 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s253 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 11710985) := by
  apply hensel_rootline_closure 9 4761 24433981 11710985 12932920 6198631
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 93 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s93 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 4320745) := by
  apply hensel_rootline_closure 5 2645 24433981 4320745 23279256 4116551
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 324 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s324 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 14990404) := by
  apply hensel_rootline_closure 24 12696 24433981 14990404 4849845 2975411
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 462 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s462 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 21364486) := by
  apply hensel_rootline_closure 1 529 24433981 21364486 116396280 101774111
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 164 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s164 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 7600164) := by
  apply hensel_rootline_closure 20 10580 24433981 7600164 5819814 1810247
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 213 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s213 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 9863425) := by
  apply hensel_rootline_closure 8 4232 24433981 9863425 14549535 5873306
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 333 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s333 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 15406105) := by
  apply hensel_rootline_closure 11 110561 24433981 15406105 556920 351149
  · intro s; omega
  · omega
  · omega
  · exact tau_110561_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 84 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s84 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 3905044) := by
  apply hensel_rootline_closure 18 9522 24433981 3905044 6466460 1033471
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 25168, s ≡ 293 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r25168_s293 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 13558545) := by
  apply hensel_rootline_closure 10 5290 24433981 13558545 11639628 6458891
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 346 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s346 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 16008564) := by
  apply hensel_rootline_closure 18 9522 24433981 16008564 6466460 4236671
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 26 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s26 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 1228084) := by
  apply hensel_rootline_closure 10 5290 24433981 1228084 11639628 585023
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 515 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s515 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 23814505) := by
  apply hensel_rootline_closure 9 4761 24433981 23814505 12932920 12605031
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 355 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s355 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 16424265) := by
  apply hensel_rootline_closure 5 2645 24433981 16424265 23279256 15648071
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 57 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s57 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 2659943) := by
  apply hensel_rootline_closure 24 12696 24433981 2659943 4849845 527966
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 195 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s195 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 9034025) := by
  apply hensel_rootline_closure 1 529 24433981 9034025 116396280 43035431
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 426 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s426 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 19703684) := by
  apply hensel_rootline_closure 20 10580 24433981 19703684 5819814 4693127
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 475 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s475 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 21966945) := by
  apply hensel_rootline_closure 8 4232 24433981 21966945 14549535 13080506
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 27170, s ≡ 341 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r27170_s341 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 15777619) := by
  apply hensel_rootline_closure 84 755412 24433981 15777619 81510 52633
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 325 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s325 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 15039453) := by
  apply hensel_rootline_closure 9 4761 24433981 15039453 12932920 7960391
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 165 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s165 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 7649213) := by
  apply hensel_rootline_closure 5 2645 24433981 7649213 23279256 7287719
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 5 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s5 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 258973) := by
  apply hensel_rootline_closure 1 529 24433981 258973 116396280 1233671
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 396 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s396 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 18318872) := by
  apply hensel_rootline_closure 24 12696 24433981 18318872 4849845 3636071
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 236 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s236 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 10928632) := by
  apply hensel_rootline_closure 20 10580 24433981 10928632 5819814 2603039
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 285 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s285 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 13191893) := by
  apply hensel_rootline_closure 8 4232 24433981 13191893 14549535 7855286
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 156 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s156 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 7233512) := by
  apply hensel_rootline_closure 18 9522 24433981 7233512 6466460 1914351
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 28028, s ≡ 365 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28028_s365 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 16887013) := by
  apply hensel_rootline_closure 10 5290 24433981 16887013 11639628 8044475
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 230 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s230 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 10651927) := by
  apply hensel_rootline_closure 9 4761 24433981 10651927 12932920 5638071
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 70 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s70 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 3261687) := by
  apply hensel_rootline_closure 5 2645 24433981 3261687 23279256 3107543
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 301 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s301 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 13931346) := by
  apply hensel_rootline_closure 24 12696 24433981 13931346 4849845 2765201
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 439 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s439 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 20305428) := by
  apply hensel_rootline_closure 1 529 24433981 20305428 116396280 96729071
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 141 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s141 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 6541106) := by
  apply hensel_rootline_closure 20 10580 24433981 6541106 5819814 1557995
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 190 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s190 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 8804367) := by
  apply hensel_rootline_closure 8 4232 24433981 8804367 14549535 5242676
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 61 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s61 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 2845986) := by
  apply hensel_rootline_closure 18 9522 24433981 2845986 6466460 753191
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 270 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s270 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 12499487) := by
  apply hensel_rootline_closure 10 5290 24433981 12499487 11639628 5954387
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 28457, s ≡ 390 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r28457_s390 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 18042167) := by
  apply hensel_rootline_closure 13 116909 24433981 18042167 526680 388903
  · intro s; omega
  · omega
  · omega
  · exact tau_116909_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 0 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s0 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 29315) := by
  apply hensel_rootline_closure 8 4232 24433981 29315 14549535 17456
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 120 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s120 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 5571995) := by
  apply hensel_rootline_closure 11 98923 24433981 5571995 622440 141943
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 422 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s422 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 19521073) := by
  apply hensel_rootline_closure 45 404685 24433981 19521073 152152 121559
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 400 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s400 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 18504915) := by
  apply hensel_rootline_closure 18 9522 24433981 18504915 6466460 4897331
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 80 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s80 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 3724435) := by
  apply hensel_rootline_closure 10 5290 24433981 3724435 11639628 1774211
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 106 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s106 :
    ∀ s : ℕ, ¬ goodOn {90} (24433981 * s + 4925349) := by
  apply hensel_rootline_closure 90 904590 24433981 4925349 68068 13721
  · intro s; omega
  · omega
  · omega
  · exact tau_904590_mul_prime_gt92


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 40 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s40 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 1876875) := by
  apply hensel_rootline_closure 9 4761 24433981 1876875 12932920 993431
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 111 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s111 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 5156294) := by
  apply hensel_rootline_closure 24 12696 24433981 5156294 4849845 1023461
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 249 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s249 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 11530376) := by
  apply hensel_rootline_closure 1 529 24433981 11530376 116396280 54927311
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 29315, s ≡ 480 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29315_s480 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 22200035) := by
  apply hensel_rootline_closure 20 10580 24433981 22200035 5819814 5287721
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 508 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s508 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 23493613) := by
  apply hensel_rootline_closure 84 755412 24433981 23493613 81510 78373
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 6 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s6 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 306735) := by
  apply hensel_rootline_closure 45 452295 24433981 306735 136136 1709
  · intro s; omega
  · omega
  · omega
  · exact tau_452295_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 513 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s513 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 23724558) := by
  apply hensel_rootline_closure 18 9522 24433981 23724558 6466460 6278711
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 193 (mod 529). Inside open mod-23 parent class 9. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s193 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 8944078) := by
  apply hensel_rootline_closure 10 5290 24433981 8944078 11639628 4260695
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 153 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s153 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 7096518) := by
  apply hensel_rootline_closure 9 4761 24433981 7096518 12932920 3756191
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 522 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s522 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 24140259) := by
  apply hensel_rootline_closure 5 2645 24433981 24140259 23279256 22999415
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 224 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s224 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 10375937) := by
  apply hensel_rootline_closure 24 12696 24433981 10375937 4849845 2059496
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 362 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s362 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 16750019) := by
  apply hensel_rootline_closure 1 529 24433981 16750019 116396280 79792151
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 64 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s64 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 2985697) := by
  apply hensel_rootline_closure 20 10580 24433981 2985697 5819814 711149
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 29601, s ≡ 113 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r29601_s113 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 5248958) := by
  apply hensel_rootline_closure 8 4232 24433981 5248958 14549535 3125561
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 415 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s415 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 19200038) := by
  apply hensel_rootline_closure 9 4761 24433981 19200038 12932920 10162591
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 255 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s255 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 11809798) := by
  apply hensel_rootline_closure 5 2645 24433981 11809798 23279256 11251679
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 95 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s95 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 4419558) := by
  apply hensel_rootline_closure 1 529 24433981 4419558 116396280 21053471
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 486 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s486 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 22479457) := by
  apply hensel_rootline_closure 24 12696 24433981 22479457 4849845 4461896
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 326 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s326 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 15089217) := by
  apply hensel_rootline_closure 20 10580 24433981 15089217 5819814 3594029
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 375 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s375 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 17352478) := by
  apply hensel_rootline_closure 8 4232 24433981 17352478 14549535 10332761
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 246 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s246 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 11394097) := by
  apply hensel_rootline_closure 18 9522 24433981 11394097 6466460 3015451
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 31603, s ≡ 455 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r31603_s455 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 21047598) := by
  apply hensel_rootline_closure 10 5290 24433981 21047598 11639628 10026455
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 0 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s0 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 32032) := by
  apply hensel_rootline_closure 1 529 24433981 32032 116396280 152591
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 391 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s391 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 18091931) := by
  apply hensel_rootline_closure 24 12696 24433981 18091931 4849845 3591026
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 231 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s231 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 10701691) := by
  apply hensel_rootline_closure 20 10580 24433981 10701691 5819814 2548985
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 280 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s280 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 12964952) := by
  apply hensel_rootline_closure 8 4232 24433981 12964952 14549535 7720151
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 146 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s146 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 6775626) := by
  apply hensel_rootline_closure 84 755412 24433981 6775626 81510 22603
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 151 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s151 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 7006571) := by
  apply hensel_rootline_closure 18 9522 24433981 7006571 6466460 1854291
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 386 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s386 :
    ∀ s : ℕ, ¬ goodOn {90} (24433981 * s + 17860986) := by
  apply hensel_rootline_closure 90 904590 24433981 17860986 68068 49757
  · intro s; omega
  · omega
  · omega
  · exact tau_904590_mul_prime_gt92


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 320 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s320 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 14812512) := by
  apply hensel_rootline_closure 9 4761 24433981 14812512 12932920 7840271
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 32032, s ≡ 160 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32032_s160 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 7422272) := by
  apply hensel_rootline_closure 5 2645 24433981 7422272 23279256 7071503
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 185 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s185 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 8577426) := by
  apply hensel_rootline_closure 8 4232 24433981 8577426 14549535 5107541
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 56 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s56 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 2619045) := by
  apply hensel_rootline_closure 18 9522 24433981 2619045 6466460 693131
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 265 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s265 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 12272546) := by
  apply hensel_rootline_closure 10 5290 24433981 12272546 11639628 5846279
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 385 (mod 529). Inside open mod-23 parent class 17. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s385 :
    ∀ s : ℕ, ¬ goodOn {13} (24433981 * s + 17815226) := by
  apply hensel_rootline_closure 13 130663 24433981 17815226 471240 343589
  · intro s; omega
  · omega
  · omega
  · exact tau_130663_mul_prime_gt15


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 65 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s65 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 3034746) := by
  apply hensel_rootline_closure 5 2645 24433981 3034746 23279256 2891327
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 296 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s296 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 13704405) := by
  apply hensel_rootline_closure 24 12696 24433981 13704405 4849845 2720156
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 434 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s434 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 20078487) := by
  apply hensel_rootline_closure 1 529 24433981 20078487 116396280 95647991
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 32461, s ≡ 136 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r32461_s136 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 6314165) := by
  apply hensel_rootline_closure 20 10580 24433981 6314165 5819814 1503941
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 368 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s368 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 17032873) := by
  apply hensel_rootline_closure 24 12696 24433981 17032873 4849845 3380816
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 506 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s506 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 23406955) := by
  apply hensel_rootline_closure 1 529 24433981 23406955 116396280 111503831
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 208 (mod 529). Inside open mod-23 parent class 1. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s208 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 9642633) := by
  apply hensel_rootline_closure 20 10580 24433981 9642633 5819814 2296733
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 257 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s257 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 11905894) := by
  apply hensel_rootline_closure 8 4232 24433981 11905894 14549535 7089521
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 128 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s128 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 5947513) := by
  apply hensel_rootline_closure 18 9522 24433981 5947513 6466460 1574011
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 337 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s337 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 15601014) := by
  apply hensel_rootline_closure 10 5290 24433981 15601014 11639628 7431863
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 297 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s297 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 13753454) := by
  apply hensel_rootline_closure 9 4761 24433981 13753454 12932920 7279711
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 35321, s ≡ 137 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r35321_s137 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 6363214) := by
  apply hensel_rootline_closure 5 2645 24433981 6363214 23279256 6062495
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 92 (mod 529). Inside open mod-23 parent class 0. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s92 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 4285996) := by
  apply hensel_rootline_closure 11 98923 24433981 4285996 622440 109183
  · intro s; omega
  · omega
  · omega
  · exact tau_98923_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 394 (mod 529). Inside open mod-23 parent class 3. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s394 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 18235074) := by
  apply hensel_rootline_closure 45 404685 24433981 18235074 152152 113551
  · intro s; omega
  · omega
  · omega
  · exact tau_404685_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 372 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s372 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 17218916) := by
  apply hensel_rootline_closure 18 9522 24433981 17218916 6466460 4556991
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 52 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s52 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 2438436) := by
  apply hensel_rootline_closure 10 5290 24433981 2438436 11639628 1161599
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 12 (mod 529). Inside open mod-23 parent class 12. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s12 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 590876) := by
  apply hensel_rootline_closure 9 4761 24433981 590876 12932920 312751
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 83 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s83 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 3870295) := by
  apply hensel_rootline_closure 24 12696 24433981 3870295 4849845 768206
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 221 (mod 529). Inside open mod-23 parent class 14. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s221 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 10244377) := by
  apply hensel_rootline_closure 1 529 24433981 10244377 116396280 48801191
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 452 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s452 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 20914036) := by
  apply hensel_rootline_closure 20 10580 24433981 20914036 5819814 4981415
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 36608, s ≡ 501 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r36608_s501 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 23177297) := by
  apply hensel_rootline_closure 8 4232 24433981 23177297 14549535 13801226
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 464 (mod 529). Inside open mod-23 parent class 4. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s464 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 21469448) := by
  apply hensel_rootline_closure 9 4761 24433981 21469448 12932920 11363791
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 304 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s304 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 14079208) := by
  apply hensel_rootline_closure 5 2645 24433981 14079208 23279256 13413839
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 6 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s6 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 314886) := by
  apply hensel_rootline_closure 24 12696 24433981 314886 4849845 62501
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 144 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s144 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 6688968) := by
  apply hensel_rootline_closure 1 529 24433981 6688968 116396280 31864271
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 375 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s375 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 17358627) := by
  apply hensel_rootline_closure 20 10580 24433981 17358627 5819814 4134569
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 424 (mod 529). Inside open mod-23 parent class 10. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s424 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 19621888) := by
  apply hensel_rootline_closure 8 4232 24433981 19621888 14549535 11684111
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 317 (mod 529). Inside open mod-23 parent class 18. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s317 :
    ∀ s : ℕ, ¬ goodOn {45} (24433981 * s + 14679665) := by
  apply hensel_rootline_closure 45 452295 24433981 14679665 136136 81789
  · intro s; omega
  · omega
  · omega
  · exact tau_452295_mul_prime_gt47


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 295 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s295 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 13663507) := by
  apply hensel_rootline_closure 18 9522 24433981 13663507 6466460 3616051
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 37752, s ≡ 504 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r37752_s504 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 23317008) := by
  apply hensel_rootline_closure 10 5290 24433981 23317008 11639628 11107535
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 347 (mod 529). Inside open mod-23 parent class 2. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s347 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 16066479) := by
  apply hensel_rootline_closure 8 4232 24433981 16066479 14549535 9566996
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 218 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s218 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 10108098) := by
  apply hensel_rootline_closure 18 9522 24433981 10108098 6466460 2675111
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 427 (mod 529). Inside open mod-23 parent class 13. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s427 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 19761599) := by
  apply hensel_rootline_closure 10 5290 24433981 19761599 11639628 9413843
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 387 (mod 529). Inside open mod-23 parent class 19. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s387 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 17914039) := by
  apply hensel_rootline_closure 9 4761 24433981 17914039 12932920 9481911
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 227 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s227 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 10523799) := by
  apply hensel_rootline_closure 5 2645 24433981 10523799 23279256 10026455
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 67 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s67 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 3133559) := by
  apply hensel_rootline_closure 1 529 24433981 3133559 116396280 14927351
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 458 (mod 529). Inside open mod-23 parent class 21. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s458 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 21193458) := by
  apply hensel_rootline_closure 24 12696 24433981 21193458 4849845 4206641
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 38896, s ≡ 298 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r38896_s298 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 13803218) := by
  apply hensel_rootline_closure 20 10580 24433981 13803218 5819814 3287723
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 97 (mod 529). Inside open mod-23 parent class 5. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s97 :
    ∀ s : ℕ, ¬ goodOn {9} (24433981 * s + 4524520) := by
  apply hensel_rootline_closure 9 4761 24433981 4524520 12932920 2394831
  · intro s; omega
  · omega
  · omega
  · exact tau_4761_mul_prime_gt11


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 466 (mod 529). Inside open mod-23 parent class 6. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s466 :
    ∀ s : ℕ, ¬ goodOn {5} (24433981 * s + 21568261) := by
  apply hensel_rootline_closure 5 2645 24433981 21568261 23279256 20548967
  · intro s; omega
  · omega
  · omega
  · exact tau_2645_mul_prime_gt7


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 168 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s168 :
    ∀ s : ℕ, ¬ goodOn {24} (24433981 * s + 7803939) := by
  apply hensel_rootline_closure 24 12696 24433981 7803939 4849845 1548986
  · intro s; omega
  · omega
  · omega
  · exact tau_12696_mul_prime_gt26


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 306 (mod 529). Inside open mod-23 parent class 7. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s306 :
    ∀ s : ℕ, ¬ goodOn {1} (24433981 * s + 14178021) := by
  apply hensel_rootline_closure 1 529 24433981 14178021 116396280 67539911
  · intro s; omega
  · omega
  · omega
  · exact tau_529_mul_prime_gt3


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 8 (mod 529). Inside open mod-23 parent class 8. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s8 :
    ∀ s : ℕ, ¬ goodOn {20} (24433981 * s + 413699) := by
  apply hensel_rootline_closure 20 10580 24433981 413699 5819814 98537
  · intro s; omega
  · omega
  · omega
  · exact tau_10580_mul_prime_gt22


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 57 (mod 529). Inside open mod-23 parent class 11. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s57 :
    ∀ s : ℕ, ¬ goodOn {8} (24433981 * s + 2676960) := by
  apply hensel_rootline_closure 8 4232 24433981 2676960 14549535 1594031
  · intro s; omega
  · omega
  · omega
  · exact tau_4232_mul_prime_gt10


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 452 (mod 529). Inside open mod-23 parent class 15. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s452 :
    ∀ s : ℕ, ¬ goodOn {84} (24433981 * s + 20921615) := by
  apply hensel_rootline_closure 84 755412 24433981 20921615 81510 69793
  · intro s; omega
  · omega
  · omega
  · exact tau_755412_mul_prime_gt86


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 177 (mod 529). Inside open mod-23 parent class 16. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s177 :
    ∀ s : ℕ, ¬ goodOn {11} (24433981 * s + 8219640) := by
  apply hensel_rootline_closure 11 110561 24433981 8219640 556920 187349
  · intro s; omega
  · omega
  · omega
  · exact tau_110561_mul_prime_gt13


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 457 (mod 529). Inside open mod-23 parent class 20. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s457 :
    ∀ s : ℕ, ¬ goodOn {18} (24433981 * s + 21152560) := by
  apply hensel_rootline_closure 18 9522 24433981 21152560 6466460 5598031
  · intro s; omega
  · omega
  · omega
  · exact tau_9522_mul_prime_gt20


/-- Mod-529 rootline partial certificate at residue r = 44187, s ≡ 137 (mod 529). Inside open mod-23 parent class 22. Closes a sub-AP of relative density 1/529 inside the base AP. -/
theorem mod529_rootline_partial_r44187_s137 :
    ∀ s : ℕ, ¬ goodOn {10} (24433981 * s + 6372080) := by
  apply hensel_rootline_closure 10 5290 24433981 6372080 11639628 3035471
  · intro s; omega
  · omega
  · omega
  · exact tau_5290_mul_prime_gt12

