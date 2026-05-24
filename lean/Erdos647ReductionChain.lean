import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Erdos647Main
import Erdos647BridgeV1
import Erdos647SieveCertificate
import Erdos647ValuationCore
import Erdos647SingleOverlapClosure
import Erdos647DirectFullValueClosure
import Erdos647ResiduePartitionStage1
import Bridge2

/-!
# Erdős #647 Stage-1 reduction chain

This file replaces the old Bridge-3-based proof path with the Stage-1
formal core:

* theorem-grade full-value closures for the currently closed residues
* proof-critical open set defined as the complement of those closures
  inside the `96` sieve survivors
* a conditional theorem parameterized by the open-set no-solution
  hypothesis

No theorem in this file imports or depends on `Bridge3`, `branchForms`,
or `SatisfiesBudgets`.
-/

namespace Erdos647ReductionChain

open ArithmeticFunction
open Erdos647Main
open Erdos647BridgeV1
open Erdos647SieveCertificate
open Erdos647ValuationCore
open Erdos647SingleOverlapClosure
open Erdos647DirectFullValueClosure
open Erdos647ResiduePartitionStage1

/-! ## Bridge 1: `Candidate` to `IsErdos647` -/

theorem bridge_candidate_to_isErdos647 (n : ℕ) (hc : Candidate n) :
    IsErdos647 n := by
  intro m _hm1 hm2
  have h := hc m hm2
  have hsigma : (sigma 0) m = (Nat.divisors m).card := sigma_zero_apply m
  have hcard : Nat.card (Nat.divisors m) = (Nat.divisors m).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard]
  rw [hsigma] at h
  exact h

/-! ## Bridge 2: theorem-grade reduction to the 96 sieve survivors -/

private lemma isErdos647_equiv (n : ℕ) :
    IsErdos647 n ↔ Bridge2.IsErdos647 n := by
  unfold IsErdos647 Bridge2.IsErdos647
  have h : ∀ m : ℕ, Nat.card ↑(Nat.divisors m) = (Nat.divisors m).card := by
    intro m
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp_rw [h]

private lemma survives_eq (r : ℕ) :
    Erdos647SieveCertificate.survives r = Bridge2.survives r := by
  simp only [Erdos647SieveCertificate.survives, Bridge2.survives,
    Erdos647SieveCertificate.coeffs, Bridge2.coeffs,
    Erdos647SieveCertificate.sievePrimes, Bridge2.sievePrimes,
    List.all_cons, List.all_nil, Bool.and_true, ne_eq, decide_not]
  rfl

theorem bridge_isErdos647_to_sieve (N : ℕ) (hN : 84 < 2520 * N)
    (hE : IsErdos647 (2520 * N)) :
    N % M ∈ survivingResidues96 := by
  have hE' : Bridge2.IsErdos647 (2520 * N) := (isErdos647_equiv _).mp hE
  have hsurvives : Bridge2.survives (N % Bridge2.M) = true :=
    Bridge2.bridge_isErdos647_to_sieve N hN hE'
  have hM_eq : Bridge2.M = M := rfl
  rw [hM_eq] at hsurvives
  rw [← survives_eq] at hsurvives
  have hMpos : 0 < M := by native_decide
  have hlt : N % M < M := Nat.mod_lt _ hMpos
  simpa [survivingResidues96, hlt] using
    (show N % M ∈ Erdos647SieveCertificate.survivingResidues from by
      simp [Erdos647SieveCertificate.survivingResidues, hsurvives, hlt])

/-! ## Conditional Stage-1 reduction -/

theorem candidate_false_large_conditional_on_openResiduesStage1
    (hOpen : ∀ N, N % M ∈ openResiduesStage1 → ¬ IsErdos647 (2520 * N)) :
    ∀ n, 84 < n → ¬ Candidate n := by
  intro n hn hc
  have hE : IsErdos647 n := bridge_candidate_to_isErdos647 n hc
  have hdvd : 2520 ∣ n := erdos647_div_2520 n hn hE
  obtain ⟨N, rfl⟩ := hdvd
  have hsieve : N % M ∈ survivingResidues96 :=
    bridge_isErdos647_to_sieve N (by omega) hE
  by_cases hsingle : N % M ∈ singleOverlapResidues42
  · exact no_erdos647_of_mem_singleOverlapResidues42 N hsingle hE
  · by_cases hdirect : N % M ∈ directFullValueResidues13
    · exact no_erdos647_of_mem_directFullValueResidues13 N hdirect hE
    · have hclosed : N % M ∉ closedResiduesStage1 := by
        intro hc'
        rcases (mem_closedResiduesStage1_iff).mp hc' with hc' | hc'
        · exact hsingle hc'
        · exact hdirect hc'
      have hopen : N % M ∈ openResiduesStage1 :=
        mem_openResiduesStage1_of_mem_surviving_not_mem_closed hsieve hclosed
      exact hOpen N hopen hE

/-- Large-`N` version of the Stage-1 conditional reduction.

This is the form needed by structural theorem-design routes that only
prove the open-residue contradiction in the range where the reduction
chain actually applies it. -/
theorem candidate_false_large_conditional_on_openResiduesStage1_large
    (hOpen :
      ∀ N, N % M ∈ openResiduesStage1 → 84 < 2520 * N →
        ¬ IsErdos647 (2520 * N)) :
    ∀ n, 84 < n → ¬ Candidate n := by
  intro n hn hc
  have hE : IsErdos647 n := bridge_candidate_to_isErdos647 n hc
  have hdvd : 2520 ∣ n := erdos647_div_2520 n hn hE
  obtain ⟨N, rfl⟩ := hdvd
  have hlargeN : 84 < 2520 * N := by omega
  have hsieve : N % M ∈ survivingResidues96 :=
    bridge_isErdos647_to_sieve N hlargeN hE
  by_cases hsingle : N % M ∈ singleOverlapResidues42
  · exact no_erdos647_of_mem_singleOverlapResidues42 N hsingle hE
  · by_cases hdirect : N % M ∈ directFullValueResidues13
    · exact no_erdos647_of_mem_directFullValueResidues13 N hdirect hE
    · have hclosed : N % M ∉ closedResiduesStage1 := by
        intro hc'
        rcases (mem_closedResiduesStage1_iff).mp hc' with hc' | hc'
        · exact hsingle hc'
        · exact hdirect hc'
      have hopen : N % M ∈ openResiduesStage1 :=
        mem_openResiduesStage1_of_mem_surviving_not_mem_closed hsieve hclosed
      exact hOpen N hopen hlargeN hE

theorem erdos647_conditional_on_openResiduesStage1
    (hOpen : ∀ N, N % M ∈ openResiduesStage1 → ¬ IsErdos647 (2520 * N)) :
    ∀ n, 24 < n → ¬ Candidate n := by
  intro n h hc
  by_cases h84 : n ≤ 84
  · exact candidate_false_finite n h h84 hc
  · exact candidate_false_large_conditional_on_openResiduesStage1 hOpen n
      (Nat.lt_of_not_ge h84) hc

/-- Large-`N` version of the final conditional theorem. -/
theorem erdos647_conditional_on_openResiduesStage1_large
    (hOpen :
      ∀ N, N % M ∈ openResiduesStage1 → 84 < 2520 * N →
        ¬ IsErdos647 (2520 * N)) :
    ∀ n, 24 < n → ¬ Candidate n := by
  intro n h hc
  by_cases h84 : n ≤ 84
  · exact candidate_false_finite n h h84 hc
  · exact candidate_false_large_conditional_on_openResiduesStage1_large hOpen n
      (Nat.lt_of_not_ge h84) hc

end Erdos647ReductionChain
