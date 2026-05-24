import Mathlib.Tactic

/-!
# Bridge to legacy v1 formalization (Lean 4.28.0)

The legacy v1 project
contains fully proved theorems for the upstream reduction of Erdős #647.
Due to a toolchain mismatch (v1 uses Lean 4.28.0, main workspace uses
4.30.0-rc1), direct import is not possible.

This file STATES the v1 theorems in the main workspace's convention,
with `sorry` standing in for proofs that exist in v1. Each sorry is
annotated with the v1 file and theorem name where the proof lives.

The v1 project compiles cleanly and these theorems are machine-checked
in that project. The sorries here are IMPORT DEBT, not open mathematics.

## Theorems available from v1

- `erdos647_div_2520'` — 2520 | n for n > 84 satisfying #647
- `shape_package_of_erdos647` — the 12-shape almost-prime package
- `isErdos647_iff_isErdos647'` — equivalence of two formulations
- `not_sq_2520N_sub_one` — 2520N−1 is not a perfect square
- `mod11_forcing` — N ≡ 0 mod 11 (complete case analysis)
- `explicitCandidate_fails` — n₀ = 604517614941240 fails at k=14
-/

namespace Erdos647BridgeV1

/-- The Erdős 647 predicate (v1 convention: `Nat.numDivisors`). -/
def IsErdos647 (n : ℕ) : Prop :=
  ∀ m, 1 ≤ m → m < n → m + Nat.card (Nat.divisors m) ≤ n + 2

-- Convert Nat.card of a Finset (coerced to a type) to Finset.card
private lemma natCard_div_eq_card (m : ℕ) :
    Nat.card (Nat.divisors m) = (Nat.divisors m).card :=
  Nat.card_eq_finsetCard _

-- Apply IsErdos647, getting a Finset.card inequality
private lemma erdos_bound {n m : ℕ} (hE : IsErdos647 n) (hm1 : 1 ≤ m) (hm2 : m < n) :
    m + (Nat.divisors m).card ≤ n + 2 := by
  have h := hE m hm1 hm2; rwa [natCard_div_eq_card] at h

-- A Finset subset of divisors
private lemma sub_div {m : ℕ} (hm : m ≠ 0) {s : Finset ℕ} (hs : ∀ d ∈ s, d ∣ m) :
    s ⊆ Nat.divisors m :=
  fun _ hd => Nat.mem_divisors.mpr ⟨hs _ hd, hm⟩

-- Step 6 auxiliary: 5 ∣ n given 2,3,8,9 ∣ n and n > 84
set_option maxHeartbeats 800000 in
private lemma aux_5_dvd {n : ℕ} (hn : 84 < n) (hE : IsErdos647 n)
    (h2 : 2 ∣ n) (h3 : 3 ∣ n) (h8 : 8 ∣ n) (h9 : 9 ∣ n) : 5 ∣ n := by
  have h72 : 72 ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h8 h9
  by_contra h5n
  have hn72 : 72 ≤ n := Nat.le_of_dvd (by linarith) h72
  rcases (show n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 from by omega)
    with hmod | hmod | hmod | hmod
  · set m := n - 1
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm5 : 5 ∣ m := by omega
    set j := m / 5
    have hj : j ≥ 29 := by omega
    have hmj : m = 5 * j := by omega
    have hdvd : ∀ d ∈ ({1, 5, j, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact hm5
      · exact ⟨5, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({5, j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5nm : (5 : ℕ) ∉ ({j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hjnm : j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 5, j, m} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h5nm,
          Finset.card_insert_of_notMem hjnm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 4 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2; omega
  · set m := n - 2
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm5 : 5 ∣ m := by omega
    have hm2d : 2 ∣ m := Nat.dvd_sub h2 (dvd_refl 2)
    have hm10 : 10 ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm2d hm5
    set j := m / 10
    have hj : j ≥ 14 := by omega
    have hmj : m = 10 * j := by omega
    have hdvd : ∀ d ∈ ({1, 2, 5, 10, j, 2*j, 5*j, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact hm2d
      · exact hm5
      · exact hm10
      · exact ⟨10, by omega⟩
      · exact ⟨5, by omega⟩
      · exact ⟨2, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({2, 5, 10, j, 2*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2nm : (2 : ℕ) ∉ ({5, 10, j, 2*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5nm : (5 : ℕ) ∉ ({10, j, 2*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h10nm : (10 : ℕ) ∉ ({j, 2*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hjnm : j ∉ ({2*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2jnm : 2*j ∉ ({5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5jnm : 5*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 2, 5, 10, j, 2*j, 5*j, m} : Finset ℕ).card = 8 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
          Finset.card_insert_of_notMem h5nm, Finset.card_insert_of_notMem h10nm,
          Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h2jnm,
          Finset.card_insert_of_notMem h5jnm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2; omega
  · set m := n - 3
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm5 : 5 ∣ m := by omega
    have hm3d : 3 ∣ m := by omega
    have hm15 : 15 ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm3d hm5
    set j := m / 15
    have hj : j ≥ 10 := by omega
    have hmj : m = 15 * j := by omega
    have hdvd : ∀ d ∈ ({1, 3, 5, 15, j, 3*j, 5*j, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact hm3d
      · exact hm5
      · exact hm15
      · exact ⟨15, by omega⟩
      · exact ⟨5, by omega⟩
      · exact ⟨3, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({3, 5, 15, j, 3*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h3nm : (3 : ℕ) ∉ ({5, 15, j, 3*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5nm : (5 : ℕ) ∉ ({15, j, 3*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h15nm : (15 : ℕ) ∉ ({j, 3*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hjnm : j ∉ ({3*j, 5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h3jnm : 3*j ∉ ({5*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5jnm : 5*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 3, 5, 15, j, 3*j, 5*j, m} : Finset ℕ).card = 8 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h3nm,
          Finset.card_insert_of_notMem h5nm, Finset.card_insert_of_notMem h15nm,
          Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h3jnm,
          Finset.card_insert_of_notMem h5jnm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2; omega
  · set m := n - 4
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm5 : 5 ∣ m := by omega
    have hm4d : 4 ∣ m := Nat.dvd_sub (dvd_trans (by norm_num : (4:ℕ) ∣ 8) h8) (dvd_refl 4)
    have hm20 : 20 ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm4d hm5
    have hm2d : 2 ∣ m := dvd_trans (by norm_num) hm20
    have hdvd : ∀ d ∈ ({1, 2, 4, 5, 10, 20, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact hm2d
      · exact hm4d
      · exact hm5
      · exact dvd_trans (by norm_num) hm20
      · exact hm20
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({2, 4, 5, 10, 20, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2nm : (2 : ℕ) ∉ ({4, 5, 10, 20, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h4nm : (4 : ℕ) ∉ ({5, 10, 20, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h5nm : (5 : ℕ) ∉ ({10, 20, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h10nm : (10 : ℕ) ∉ ({20, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h20nm : (20 : ℕ) ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 2, 4, 5, 10, 20, m} : Finset ℕ).card = 7 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
          Finset.card_insert_of_notMem h4nm, Finset.card_insert_of_notMem h5nm,
          Finset.card_insert_of_notMem h10nm, Finset.card_insert_of_notMem h20nm,
          Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 7 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2; omega

-- Step 7: split into per-case sub-lemmas to stay within heartbeat limits

-- Case 1: n % 7 = 1, m = n - 1, 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case1 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 1) : False := by
  set m := n - 1
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  set j := m / 7
  have hj : j ≥ 51 := by omega
  have hmj : m = 7 * j := by omega
  have hdvd : ∀ d ∈ ({1, 7, j, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm7
    · exact ⟨7, by omega⟩
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({7, j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hjnm : j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 7, j, m} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h7nm,
        Finset.card_insert_of_notMem hjnm, Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 4 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Case 2: n % 7 = 2, m = n - 2, 2 | m (via Nat.dvd_sub h2) and 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case2 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 2) : False := by
  set m := n - 2
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  have hm2d : 2 ∣ m := by omega
  have hm14 : 14 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm2d hm7
  set j := m / 14
  have hj : j ≥ 25 := by omega
  have hmj : m = 14 * j := by omega
  have hdvd : ∀ d ∈ ({1, 2, 7, 14, j, 2*j, 7*j, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm2d
    · exact hm7
    · exact hm14
    · exact ⟨14, by omega⟩
    · exact ⟨7, by omega⟩
    · exact ⟨2, by omega⟩
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({2, 7, 14, j, 2*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2nm : (2 : ℕ) ∉ ({7, 14, j, 2*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({14, j, 2*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h14nm : (14 : ℕ) ∉ ({j, 2*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hjnm : j ∉ ({2*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2jnm : 2*j ∉ ({7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7jnm : 7*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 2, 7, 14, j, 2*j, 7*j, m} : Finset ℕ).card = 8 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
        Finset.card_insert_of_notMem h7nm, Finset.card_insert_of_notMem h14nm,
        Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h2jnm,
        Finset.card_insert_of_notMem h7jnm, Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Case 3: n % 7 = 3, m = n - 3, 3 | m and 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case3 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 3) : False := by
  set m := n - 3
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  have hm3d : 3 ∣ m := by omega
  have hm21 : 21 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm3d hm7
  set j := m / 21
  have hj : j ≥ 17 := by omega
  have hmj : m = 21 * j := by omega
  have hdvd : ∀ d ∈ ({1, 3, 7, 21, j, 3*j, 7*j, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm3d
    · exact hm7
    · exact hm21
    · exact ⟨21, by omega⟩
    · exact ⟨7, by omega⟩
    · exact ⟨3, by omega⟩
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({3, 7, 21, j, 3*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h3nm : (3 : ℕ) ∉ ({7, 21, j, 3*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({21, j, 3*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h21nm : (21 : ℕ) ∉ ({j, 3*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hjnm : j ∉ ({3*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h3jnm : 3*j ∉ ({7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7jnm : 7*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 3, 7, 21, j, 3*j, 7*j, m} : Finset ℕ).card = 8 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h3nm,
        Finset.card_insert_of_notMem h7nm, Finset.card_insert_of_notMem h21nm,
        Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h3jnm,
        Finset.card_insert_of_notMem h7jnm, Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Case 4: n % 7 = 4, m = n - 4, 4 | m and 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case4 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 4) : False := by
  set m := n - 4
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  have hm4d : 4 ∣ m := by omega
  have hm28 : 28 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm4d hm7
  have hm2d : 2 ∣ m := dvd_trans (by norm_num) hm28
  have hdvd : ∀ d ∈ ({1, 2, 4, 7, 14, 28, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm2d
    · exact hm4d
    · exact hm7
    · exact dvd_trans (by norm_num) hm28
    · exact hm28
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({2, 4, 7, 14, 28, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2nm : (2 : ℕ) ∉ ({4, 7, 14, 28, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h4nm : (4 : ℕ) ∉ ({7, 14, 28, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({14, 28, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h14nm : (14 : ℕ) ∉ ({28, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h28nm : (28 : ℕ) ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 2, 4, 7, 14, 28, m} : Finset ℕ).card = 7 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
        Finset.card_insert_of_notMem h4nm, Finset.card_insert_of_notMem h7nm,
        Finset.card_insert_of_notMem h14nm, Finset.card_insert_of_notMem h28nm,
        Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 7 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Case 5: n % 7 = 5, m = n - 5, 5 | m and 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case5 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 5) : False := by
  set m := n - 5
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  have hm5d : 5 ∣ m := by omega
  have hm35 : 35 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm5d hm7
  set j := m / 35
  have hj : j ≥ 10 := by omega
  have hmj : m = 35 * j := by omega
  have hdvd : ∀ d ∈ ({1, 5, 7, 35, j, 5*j, 7*j, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm5d
    · exact hm7
    · exact hm35
    · exact ⟨35, by omega⟩
    · exact ⟨7, by omega⟩
    · exact ⟨5, by omega⟩
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({5, 7, 35, j, 5*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h5nm : (5 : ℕ) ∉ ({7, 35, j, 5*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({35, j, 5*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h35nm : (35 : ℕ) ∉ ({j, 5*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hjnm : j ∉ ({5*j, 7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h5jnm : 5*j ∉ ({7*j, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7jnm : 7*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 5, 7, 35, j, 5*j, 7*j, m} : Finset ℕ).card = 8 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h5nm,
        Finset.card_insert_of_notMem h7nm, Finset.card_insert_of_notMem h35nm,
        Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h5jnm,
        Finset.card_insert_of_notMem h7jnm, Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Case 6: n % 7 = 6, m = n - 6, 2 | m, 3 | m, 7 | m
set_option maxHeartbeats 400000 in
private lemma aux_7_case6 {n : ℕ} (h360 : 360 ∣ n) (hE : IsErdos647 n)
    (hmod : n % 7 = 6) : False := by
  set m := n - 6
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < n := by omega
  have hmne : m ≠ 0 := by omega
  have hm7 : 7 ∣ m := by omega
  have hm3d : 3 ∣ m := by omega
  have hm2d : 2 ∣ m := by omega
  have hm6 : 6 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm2d hm3d
  have hm42 : 42 ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm6 hm7
  have hdvd : ∀ d ∈ ({1, 2, 3, 6, 7, 14, 21, 42, m} : Finset ℕ), d ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact hm2d
    · exact hm3d
    · exact hm6
    · exact hm7
    · exact dvd_trans (by norm_num) hm42
    · exact dvd_trans (by norm_num) hm42
    · exact hm42
    · exact dvd_refl _
  have hsub := sub_div hmne hdvd
  have h1nm : (1 : ℕ) ∉ ({2, 3, 6, 7, 14, 21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h2nm : (2 : ℕ) ∉ ({3, 6, 7, 14, 21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h3nm : (3 : ℕ) ∉ ({6, 7, 14, 21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h6nm : (6 : ℕ) ∉ ({7, 14, 21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h7nm : (7 : ℕ) ∉ ({14, 21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h14nm : (14 : ℕ) ∉ ({21, 42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h21nm : (21 : ℕ) ∉ ({42, m} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have h42nm : (42 : ℕ) ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hcard : ({1, 2, 3, 6, 7, 14, 21, 42, m} : Finset ℕ).card = 9 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
        Finset.card_insert_of_notMem h3nm, Finset.card_insert_of_notMem h6nm,
        Finset.card_insert_of_notMem h7nm, Finset.card_insert_of_notMem h14nm,
        Finset.card_insert_of_notMem h21nm, Finset.card_insert_of_notMem h42nm,
        Finset.card_singleton]
  have hge : (Nat.divisors m).card ≥ 9 := hcard ▸ Finset.card_le_card hsub
  have hb := erdos_bound hE hm1 hm2; omega

-- Dispatcher: 7 ∣ n
set_option maxHeartbeats 400000 in
private lemma aux_7_dvd {n : ℕ} (_hn : 84 < n) (hE : IsErdos647 n)
    (_h2 : 2 ∣ n) (_h3 : 3 ∣ n) (_h4 : 4 ∣ n) (h5 : 5 ∣ n)
    (h8 : 8 ∣ n) (h9 : 9 ∣ n) : 7 ∣ n := by
  have h72 : 72 ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h8 h9
  have h360 : 360 ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h72 h5
  by_contra h7n
  clear _hn _h2 _h3 _h4 h5 h8 h9 h72
  rcases (show n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6
    from by omega) with hmod | hmod | hmod | hmod | hmod | hmod
  · exact aux_7_case1 h360 hE hmod
  · exact aux_7_case2 h360 hE hmod
  · exact aux_7_case3 h360 hE hmod
  · exact aux_7_case4 h360 hE hmod
  · exact aux_7_case5 h360 hE hmod
  · exact aux_7_case6 h360 hE hmod

set_option maxHeartbeats 0 in
/-- **2520-divisibility.** Any n > 84 satisfying #647 has 2520 | n.
    Proved in v1: `Erdos647/Div2520.lean` → `erdos647_div_2520'`
    and `Erdos647/ShapePackage.lean` → `erdos647_div_2520`. -/
theorem erdos647_div_2520 (n : ℕ) (hn : 84 < n) (hE : IsErdos647 n) :
    2520 ∣ n := by
  -- Helper: given a subset of divisors with known card, bound (Nat.divisors m).card from below
  -- and derive contradiction
  -- Step 1: 2 ∣ n
  have h2 : 2 ∣ n := by
    by_contra h2n
    have hno : n % 2 = 1 := by omega
    -- m = n - 1 is even, ≥ 84
    set m := n - 1
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm2d : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    set k := m / 2
    have hk : k ≥ 42 := by omega
    have hmk : m = 2 * k := by omega
    -- Four distinct divisors: 1, 2, k, m
    have hdvd : ∀ d ∈ ({1, 2, k, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact hm2d
      · exact ⟨2, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({2, k, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2nm : (2 : ℕ) ∉ ({k, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hknm : k ∉ ({m} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 2, k, m} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
          Finset.card_insert_of_notMem hknm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 4 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2
    omega
  -- Step 2: 4 ∣ n
  have h4 : 4 ∣ n := by
    obtain ⟨k, hk⟩ := h2
    by_contra h4n
    have hko : k % 2 = 1 := by
      have : ¬ (2 ∣ k) := fun ⟨j, hj⟩ => h4n ⟨j, by omega⟩
      omega
    -- m = n - 2 is divisible by 4 (since n ≡ 2 mod 4)
    set m := n - 2
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm4 : 4 ∣ m := by omega
    set j := m / 4
    have hj : j ≥ 21 := by omega
    have hmj : m = 4 * j := by omega
    have hdvd : ∀ d ∈ ({1, 2, 4, j, 2*j, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact dvd_trans (by norm_num) hm4
      · exact hm4
      · exact ⟨4, by omega⟩
      · exact ⟨2, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({2, 4, j, 2*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2nm : (2 : ℕ) ∉ ({4, j, 2*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h4nm : (4 : ℕ) ∉ ({j, 2*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hjnm : j ∉ ({2*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2jnm : 2*j ∉ ({m} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 2, 4, j, 2*j, m} : Finset ℕ).card = 6 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
          Finset.card_insert_of_notMem h4nm, Finset.card_insert_of_notMem hjnm,
          Finset.card_insert_of_notMem h2jnm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 6 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2
    omega
  -- Step 3: 8 ∣ n
  have h8 : 8 ∣ n := by
    obtain ⟨k, hk⟩ := h4
    by_contra h8n
    have hko : k % 2 = 1 := by
      have : ¬ (2 ∣ k) := fun ⟨j, hj⟩ => h8n ⟨j, by omega⟩
      omega
    -- m = n - 4 divisible by 8 (since n ≡ 4 mod 8)
    set m := n - 4
    have hm1 : 1 ≤ m := by omega
    have hm2 : m < n := by omega
    have hmne : m ≠ 0 := by omega
    have hm8 : 8 ∣ m := by omega
    set j := m / 8
    have hj : j ≥ 11 := by omega
    have hmj : m = 8 * j := by omega
    have hdvd : ∀ d ∈ ({1, 2, 4, 8, j, 2*j, 4*j, m} : Finset ℕ), d ∣ m := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_dvd _
      · exact dvd_trans (by norm_num) hm8
      · exact dvd_trans (by norm_num) hm8
      · exact hm8
      · exact ⟨8, by omega⟩
      · exact ⟨4, by omega⟩
      · exact ⟨2, by omega⟩
      · exact dvd_refl _
    have hsub := sub_div hmne hdvd
    have h1nm : (1 : ℕ) ∉ ({2, 4, 8, j, 2*j, 4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2nm : (2 : ℕ) ∉ ({4, 8, j, 2*j, 4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h4nm : (4 : ℕ) ∉ ({8, j, 2*j, 4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h8nm : (8 : ℕ) ∉ ({j, 2*j, 4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hjnm : j ∉ ({2*j, 4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2jnm : 2*j ∉ ({4*j, m} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h4jnm : 4*j ∉ ({m} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    have hcard : ({1, 2, 4, 8, j, 2*j, 4*j, m} : Finset ℕ).card = 8 := by
      rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
          Finset.card_insert_of_notMem h4nm, Finset.card_insert_of_notMem h8nm,
          Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h2jnm,
          Finset.card_insert_of_notMem h4jnm, Finset.card_singleton]
    have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
    have hb := erdos_bound hE hm1 hm2
    omega
  -- Step 4: 3 ∣ n
  have h3 : 3 ∣ n := by
    by_contra h3n
    rcases (show n % 3 = 1 ∨ n % 3 = 2 from by omega) with hmod | hmod
    · -- n ≡ 1 mod 3: m = n-1, 3 ∣ m (since n-1 ≡ 0 mod 3), m odd (8 ∣ n → n even)
      set m := n - 1
      have hm1 : 1 ≤ m := by omega
      have hm2 : m < n := by omega
      have hmne : m ≠ 0 := by omega
      have hm3 : 3 ∣ m := by omega
      set j := m / 3
      have hj : j ≥ 28 := by omega
      have hmj : m = 3 * j := by omega
      have hdvd : ∀ d ∈ ({1, 3, j, m} : Finset ℕ), d ∣ m := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact one_dvd _
        · exact hm3
        · exact ⟨3, by omega⟩
        · exact dvd_refl _
      have hsub := sub_div hmne hdvd
      have h1nm : (1 : ℕ) ∉ ({3, j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3nm : (3 : ℕ) ∉ ({j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hjnm : j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
      have hcard : ({1, 3, j, m} : Finset ℕ).card = 4 := by
        rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h3nm,
            Finset.card_insert_of_notMem hjnm, Finset.card_singleton]
      have hge : (Nat.divisors m).card ≥ 4 := hcard ▸ Finset.card_le_card hsub
      have hb := erdos_bound hE hm1 hm2; omega
    · -- n ≡ 2 mod 3: m = n-2, 3 ∣ m and 2 ∣ m (since 8 ∣ n → 2 ∣ n), so 6 ∣ m
      set m := n - 2
      have hm1 : 1 ≤ m := by omega
      have hm2 : m < n := by omega
      have hmne : m ≠ 0 := by omega
      have hm3 : 3 ∣ m := by omega
      have hm2d : 2 ∣ m := by
        exact Nat.dvd_sub h2 (dvd_refl 2)
      have hm6 : 6 ∣ m :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm2d hm3
      set j := m / 6
      have hj : j ≥ 14 := by omega
      have hmj : m = 6 * j := by omega
      have hdvd : ∀ d ∈ ({1, 2, 3, 6, j, 2*j, 3*j, m} : Finset ℕ), d ∣ m := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact one_dvd _
        · exact hm2d
        · exact hm3
        · exact hm6
        · exact ⟨6, by omega⟩
        · exact ⟨3, by omega⟩
        · exact ⟨2, by omega⟩
        · exact dvd_refl _
      have hsub := sub_div hmne hdvd
      have h1nm : (1 : ℕ) ∉ ({2, 3, 6, j, 2*j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h2nm : (2 : ℕ) ∉ ({3, 6, j, 2*j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3nm : (3 : ℕ) ∉ ({6, j, 2*j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h6nm : (6 : ℕ) ∉ ({j, 2*j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hjnm : j ∉ ({2*j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h2jnm : 2*j ∉ ({3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3jnm : 3*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
      have hcard : ({1, 2, 3, 6, j, 2*j, 3*j, m} : Finset ℕ).card = 8 := by
        rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
            Finset.card_insert_of_notMem h3nm, Finset.card_insert_of_notMem h6nm,
            Finset.card_insert_of_notMem hjnm, Finset.card_insert_of_notMem h2jnm,
            Finset.card_insert_of_notMem h3jnm, Finset.card_singleton]
      have hge : (Nat.divisors m).card ≥ 8 := hcard ▸ Finset.card_le_card hsub
      have hb := erdos_bound hE hm1 hm2; omega
  -- Step 5: 9 ∣ n. We have 24 ∣ n.
  have h24 : 24 ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h8 h3
  have h9 : 9 ∣ n := by
    by_contra h9n
    rcases (show n % 9 = 3 ∨ n % 9 = 6 from by omega) with hmod | hmod
    · -- n ≡ 3 mod 9 and 24 ∣ n → 9 ∣ (n-3)
      -- n ≡ 0 mod 24 and n ≡ 3 mod 9. 9 ∣ (n-3) since n ≡ 3 mod 9.
      set m := n - 3
      have hm1 : 1 ≤ m := by omega
      have hm2 : m < n := by omega
      have hmne : m ≠ 0 := by omega
      have hm9 : 9 ∣ m := by omega
      have hm3 : 3 ∣ m := dvd_trans (by norm_num) hm9
      set j := m / 9
      have hj : j ≥ 9 := by
        have hm_ge : m ≥ 81 := by omega
        omega
      have hmj : m = 9 * j := by omega
      have hdvd : ∀ d ∈ ({1, 3, 9, j, 3*j, m} : Finset ℕ), d ∣ m := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
        · exact one_dvd _
        · exact hm3
        · exact hm9
        · exact ⟨9, by omega⟩
        · exact ⟨3, by omega⟩
        · exact dvd_refl _
      have hsub := sub_div hmne hdvd
      have h1nm : (1 : ℕ) ∉ ({3, 9, j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3nm : (3 : ℕ) ∉ ({9, j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h9nm : (9 : ℕ) ∉ ({j, 3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hjnm : j ∉ ({3*j, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3jnm : 3*j ∉ ({m} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
      have hcard : ({1, 3, 9, j, 3*j, m} : Finset ℕ).card = 6 := by
        rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h3nm,
            Finset.card_insert_of_notMem h9nm, Finset.card_insert_of_notMem hjnm,
            Finset.card_insert_of_notMem h3jnm, Finset.card_singleton]
      have hge : (Nat.divisors m).card ≥ 6 := hcard ▸ Finset.card_le_card hsub
      have hb := erdos_bound hE hm1 hm2; omega
    · -- n ≡ 6 mod 9 and 24 ∣ n. n ≡ 24 mod 72, n-6 ≡ 18 mod 72, so 18 ∣ (n-6).
      -- Use 9 divisors: {1,2,3,6,9,18,m/3,m/2,m} where m/3 = 6j, m/2 = 9j (j = m/18).
      set m := n - 6
      have hm1 : 1 ≤ m := by omega
      have hm2 : m < n := by omega
      have hmne : m ≠ 0 := by omega
      have hm9 : 9 ∣ m := by omega
      have hm2d : 2 ∣ m := by
        exact Nat.dvd_sub h2 (by norm_num : (2:ℕ) ∣ 6)
      have hm18 : 18 ∣ m :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) hm2d hm9
      have hm3 : 3 ∣ m := dvd_trans (by norm_num) hm9
      have hm6 : 6 ∣ m := dvd_trans (by norm_num) hm18
      -- m ≥ 90 (since n > 84 and 24 ∣ n, so n ≥ 96, m = n-6 ≥ 90)
      have hm_ge : m ≥ 90 := by omega
      -- m/3 and m/2 are additional divisors, both > 18
      -- a = m/3 (divisor since 3 ∣ m), b = m/2 (divisor since 2 ∣ m)
      set a := m / 3 with ha_def
      set b := m / 2 with hb_def
      have ha_eq : m = 3 * a := by omega
      have hb_eq : m = 2 * b := by omega
      have ha_ge : a ≥ 30 := by omega
      have hb_ge : b ≥ 45 := by omega
      have ha_dvd : a ∣ m := ⟨3, by omega⟩
      have hb_dvd : b ∣ m := ⟨2, by omega⟩
      have hdvd : ∀ d ∈ ({1, 2, 3, 6, 9, 18, a, b, m} : Finset ℕ), d ∣ m := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact one_dvd _
        · exact hm2d
        · exact hm3
        · exact hm6
        · exact hm9
        · exact hm18
        · exact ha_dvd
        · exact hb_dvd
        · exact dvd_refl _
      have hsub := sub_div hmne hdvd
      have h1nm : (1 : ℕ) ∉ ({2, 3, 6, 9, 18, a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h2nm : (2 : ℕ) ∉ ({3, 6, 9, 18, a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h3nm : (3 : ℕ) ∉ ({6, 9, 18, a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h6nm : (6 : ℕ) ∉ ({9, 18, a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h9nm : (9 : ℕ) ∉ ({18, a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have h18nm : (18 : ℕ) ∉ ({a, b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hanm : a ∉ ({b, m} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hbnm : b ∉ ({m} : Finset ℕ) := by
        simp only [Finset.mem_singleton]; omega
      have hcard : ({1, 2, 3, 6, 9, 18, a, b, m} : Finset ℕ).card = 9 := by
        rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem h2nm,
            Finset.card_insert_of_notMem h3nm, Finset.card_insert_of_notMem h6nm,
            Finset.card_insert_of_notMem h9nm, Finset.card_insert_of_notMem h18nm,
            Finset.card_insert_of_notMem hanm, Finset.card_insert_of_notMem hbnm,
            Finset.card_singleton]
      have hge : (Nat.divisors m).card ≥ 9 := hcard ▸ Finset.card_le_card hsub
      have hbnd := erdos_bound hE hm1 hm2; omega
  -- Step 6: 5 ∣ n (by auxiliary lemma)
  have h5 : 5 ∣ n := aux_5_dvd hn hE h2 h3 h8 h9
  -- Step 7: 7 ∣ n (by auxiliary lemma)
  have h7 : 7 ∣ n := aux_7_dvd hn hE h2 h3 h4 h5 h8 h9
  -- Step 8: 2520 = 8 × 315 = 8 × 9 × 5 × 7
  have h315 : 315 ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h9
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h5 h7)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by native_decide) h8 h315

/-- **2520N−1 is not a perfect square.** Key lemma for the k=1 shape.
    Proved in v1: `Erdos647/ShapeProofs.lean` → `not_sq_2520N_sub_one`. -/
theorem not_sq_2520N_sub_one (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ r, r * r = 2520 * N - 1 := by
  intro ⟨r, hr⟩
  have h1 : r * r + 1 = 2520 * N := by omega
  have h2 : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases h2 with h | h
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have h3 : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [h3] at h1
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    have h3 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    rw [h3] at h1
    omega

/-- **Explicit candidate fails.** n₀ = 604517614941240 = 2520·239887942437
    satisfies τ(n₀−k) ≤ k+2 for k ≤ 13 and k=24, but fails at k=14
    with τ(n₀−14) = 192 > 16.
    Proved in v1: `Erdos647/Sieve.lean` → `explicitCandidate_fails`. -/
theorem explicit_candidate_fails :
    let n₀ := 604517614941240
    let k := 14
    -- τ(n₀ − 14) > k + 2
    (Nat.divisors (n₀ - k)).card > k + 2 := by
  -- n₀ - k = 604517614941226 = 2 × 7² × 19 × 23 × 71 × 5237 × 37963
  -- Exhibit 17 distinct divisors to show τ ≥ 17 > 16
  show (Nat.divisors 604517614941226).card > 16
  have hn : 604517614941226 ≠ 0 := by omega
  have hsub : {1, 2, 7, 14, 19, 23, 38, 46, 49, 71, 98, 133, 142, 161, 266, 322, 437}
      ⊆ Nat.divisors 604517614941226 := by
    intro x hx
    simp only [Nat.mem_divisors]
    refine ⟨?_, hn⟩
    fin_cases hx <;>
      first
      | exact ⟨604517614941226, by omega⟩
      | exact ⟨302258807470613, by omega⟩
      | exact ⟨86359659277318, by omega⟩
      | exact ⟨43179829638659, by omega⟩
      | exact ⟨31816716575854, by omega⟩
      | exact ⟨26283374562662, by omega⟩
      | exact ⟨15908358287927, by omega⟩
      | exact ⟨13141687281331, by omega⟩
      | exact ⟨12337094182474, by omega⟩
      | exact ⟨8514332604806, by omega⟩
      | exact ⟨6168547091237, by omega⟩
      | exact ⟨4545245225122, by omega⟩
      | exact ⟨4257166302403, by omega⟩
      | exact ⟨3754767794666, by omega⟩
      | exact ⟨2272622612561, by omega⟩
      | exact ⟨1877383897333, by omega⟩
      | exact ⟨1383335503298, by omega⟩
  have hcard : ({1, 2, 7, 14, 19, 23, 38, 46, 49, 71, 98, 133, 142, 161,
      266, 322, 437} : Finset ℕ).card = 17 := by native_decide
  linarith [Finset.card_le_card hsub]

end Erdos647BridgeV1
