import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Barrier Theorem for Finite Prime-by-Prime Local-Divisibility Descent

Formalization of the abstract barrier theorem from the multi-model
session on Erdős Problem #647 (April 2026).

## Statement

For any noncontradictory budgeted affine state with `m` active clauses,
no further finite prime-by-prime local-divisibility descent step at any
regular prime `q > m` can eliminate the state.

## Proof outline

Each clause `L_i(x) = α_i x + β_i` (with `α_i ≠ 0` mod the chosen prime
`q`) has at most one bad residue mod `q` (the unique `s` with
`q ∣ L_i(s)`). With `m` clauses there are at most `m` bad residues.
Since `q > m`, at least one good residue survives in `Fin q`. Combined
with CRT, persistence through any finite set of large regular primes
follows by induction.

This file proves the **combinatorial heart** of the argument cleanly
(no `sorry`) and *states* the application to the residual hard-root
states from the verified reduction.
-/

namespace Erdos647BarrierTheorem

open Finset

/-- **One-prime escape (combinatorial form).** For a finite set `bad`
    of residues mod `q` with `bad.card < q`, there is a residue
    `s : Fin q` not in `bad`.

    This is direct: `bad` is a strict subset of `Finset.univ : Finset (Fin q)`,
    so the complement is nonempty. -/
theorem one_prime_escape (q : ℕ) (bad : Finset (Fin q))
    (h_card : bad.card < q) : ∃ s : Fin q, s ∉ bad := by
  have h_univ : (Finset.univ : Finset (Fin q)).card = q :=
    Finset.card_univ.trans (Fintype.card_fin q)
  have h_lt : bad.card < (Finset.univ : Finset (Fin q)).card := by
    rw [h_univ]; exact h_card
  -- Strict subset implies complement is nonempty.
  have : ∃ s, s ∈ (Finset.univ : Finset (Fin q)) ∧ s ∉ bad := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset (Fin q)) ⊆ bad := fun s hs => h s hs
    have : (Finset.univ : Finset (Fin q)).card ≤ bad.card :=
      Finset.card_le_card this
    omega
  obtain ⟨s, _, hsb⟩ := this
  exact ⟨s, hsb⟩

/-- **List-version: bad-residue list.** For any list `bad : List (Fin q)`
    with `bad.length < q`, there is some `s : Fin q` not in `bad`. -/
theorem one_prime_escape_list (q : ℕ) (bad : List (Fin q))
    (h_len : bad.length < q) : ∃ s : Fin q, s ∉ bad := by
  have hcard : bad.toFinset.card ≤ bad.length := List.toFinset_card_le bad
  have : bad.toFinset.card < q := lt_of_le_of_lt hcard h_len
  obtain ⟨s, hs⟩ := one_prime_escape q bad.toFinset this
  refine ⟨s, ?_⟩
  intro h
  exact hs (List.mem_toFinset.mpr h)

/-- A budgeted affine state (abstract): congruence `x ≡ a (mod M)` plus
    a list of linear forms `α_i x + β_i` with `α_i > 0`. The barrier
    theorem is about the COUNTING of bad residues, independent of how
    higher-budget shapes are interpreted. -/
structure State where
  M : ℕ
  a : ℕ
  forms : List (ℕ × ℤ)
  M_pos : 0 < M

/-- A regular prime for a state: `q ∤ M` and `q ∤ α` for every form. -/
def regular (st : State) (q : ℕ) : Prop :=
  ¬ q ∣ st.M ∧ ∀ f ∈ st.forms, ¬ q ∣ f.1

set_option maxHeartbeats 800000 in
/-- **Statement of the abstract barrier theorem.** For any state `st`
    and any finite set `S` of regular primes each greater than the
    number of forms, there is a single residue `a_S` such that no
    prime in `S` divides any form value at `a_S`.

    Proof: by induction on `|S|`. At each step `one_prime_escape_list`
    gives a good residue at the new prime; CRT combines it with the
    inductive hypothesis. -/
theorem barrier_statement_form :
    ∀ (st : State) (S : Finset ℕ),
      (∀ q ∈ S, Nat.Prime q) →
      (∀ q ∈ S, regular st q) →
      (∀ q ∈ S, st.forms.length < q) →
      ∃ a_S : ℕ,
        ∀ q ∈ S, ∀ f ∈ st.forms, ¬ (q : ℤ) ∣ ((f.1 : ℤ) * a_S + f.2) := by
  intro st
  apply Finset.induction
  · -- Base case: S = ∅
    intro _ _ _
    exact ⟨0, fun q hq => by simp at hq⟩
  · -- Inductive step: S = insert q₀ S', q₀ ∉ S'
    intro q₀ S' hq₀_notin IH hprime hreg hlen
    -- Restrict hypotheses to S'
    have h_prime' : ∀ q ∈ S', Nat.Prime q :=
      fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have h_reg' : ∀ q ∈ S', regular st q :=
      fun q hq => hreg q (Finset.mem_insert_of_mem hq)
    have h_len' : ∀ q ∈ S', st.forms.length < q :=
      fun q hq => hlen q (Finset.mem_insert_of_mem hq)
    -- Get a₀ from inductive hypothesis
    obtain ⟨a₀, ha₀⟩ := IH h_prime' h_reg' h_len'
    -- Prime facts about q₀
    have hpq₀ : Nat.Prime q₀ := hprime q₀ (Finset.mem_insert_self q₀ S')
    have hregq₀ : regular st q₀ := hreg q₀ (Finset.mem_insert_self q₀ S')
    have hlenq₀ : st.forms.length < q₀ := hlen q₀ (Finset.mem_insert_self q₀ S')
    -- Set up ZMod instances for q₀
    haveI hNeZero : NeZero q₀ := ⟨hpq₀.ne_zero⟩
    haveI hFact : Fact (Nat.Prime q₀) := ⟨hpq₀⟩
    -- Rewrite q₀ as a successor so ZMod q₀ = Fin q₀ definitionally
    obtain ⟨q₀', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpq₀.ne_zero
    -- Now ZMod (q₀' + 1) = Fin (q₀' + 1) definitionally
    -- For each form (α, β), the bad residue mod (q₀'+1) is
    --   r = -(β : ZMod (q₀'+1)) * (α : ZMod (q₀'+1))⁻¹
    -- Build the bad-residue list as List (Fin (q₀' + 1))
    -- (using the definitional equality ZMod (q₀'+1) = Fin (q₀'+1))
    let bad : List (Fin (q₀' + 1)) :=
      st.forms.map (fun f => -(f.2 : ZMod (q₀' + 1)) * (f.1 : ZMod (q₀' + 1))⁻¹)
    -- The bad list has length = forms.length < q₀' + 1
    have hbad_len : bad.length < q₀' + 1 := by
      simp only [bad, List.length_map]
      exact hlenq₀
    -- Find escape residue s not in bad
    obtain ⟨s, hs⟩ := one_prime_escape_list (q₀' + 1) bad hbad_len
    -- The product P = ∏ q ∈ S', q
    let P := S'.prod id
    -- q₀' + 1 is coprime to P: for each q ∈ S', (q₀'+1) and q are coprime distinct primes
    have hcop : (q₀' + 1).Coprime P := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      show (q₀' + 1).Coprime q
      apply (Nat.coprime_primes hFact.out (h_prime' q hq)).mpr
      intro heq
      exact hq₀_notin (heq ▸ hq)
    -- Use CRT to find a₁ with a₁ ≡ s.val [MOD q₀'+1] and a₁ ≡ a₀ [MOD P]
    let crt := Nat.chineseRemainder hcop s.val a₀
    obtain ⟨ha₁_q₀, ha₁_P⟩ := crt.prop
    use crt.val
    -- Show a₁ works for all q ∈ insert (q₀'+1) S'
    intro q hq_in f hf
    rcases Finset.mem_insert.mp hq_in with rfl | hq_S'
    · -- Case q = q₀' + 1: use ha₁_q₀ and the escape s
      -- Step 1: Reduce to showing ¬(q₀'+1 : ℤ) ∣ f.1 * s.val + f.2
      -- since a₁ ≡ s.val [MOD q₀'+1], i.e. (q₀'+1 : ℤ) ∣ s.val - a₁
      have hdvd_sval_a₁ : (q₀' + 1 : ℤ) ∣ (s.val : ℤ) - crt.val := ha₁_q₀.dvd
      suffices h_s_bad : ¬ (q₀' + 1 : ℤ) ∣ ((f.1 : ℤ) * s.val + f.2) by
        intro hdiv
        apply h_s_bad
        have hmul : (q₀' + 1 : ℤ) ∣ (f.1 : ℤ) * ((s.val : ℤ) - crt.val) :=
          dvd_mul_of_dvd_right hdvd_sval_a₁ _
        have : (q₀' + 1 : ℤ) ∣ (f.1 : ℤ) * s.val + f.2 := by
          have heq : (f.1 : ℤ) * s.val + f.2 =
              (f.1 : ℤ) * crt.val + f.2 + (f.1 : ℤ) * ((s.val : ℤ) - crt.val) := by ring
          rw [heq]; exact dvd_add hdiv hmul
        exact this
      -- Step 2: ¬(q₀'+1 : ℤ) ∣ f.1 * s.val + f.2
      -- α = f.1 ≠ 0 in ZMod because ¬(q₀'+1) ∣ f.1
      have hα_ne : (f.1 : ZMod (q₀' + 1)) ≠ 0 :=
        fun h => hregq₀.2 f hf ((ZMod.natCast_eq_zero_iff f.1 (q₀' + 1)).mp h)
      -- s.val cast to ZMod = bad residue for f would give contradiction
      -- First: hs_ne_bad: (s.val : ZMod) ≠ -(β : ZMod) * (α : ZMod)⁻¹
      have hs_ne_bad : (s.val : ZMod (q₀' + 1)) ≠
          -(f.2 : ZMod (q₀' + 1)) * (f.1 : ZMod (q₀' + 1))⁻¹ := by
        intro heq_s
        apply hs
        simp only [bad, List.mem_map]
        refine ⟨f, hf, ?_⟩
        -- heq_s : (s.val : ZMod (q₀'+1)) = -(f.2 : ZMod) * (f.1 : ZMod)⁻¹
        -- Need: -(f.2 : ZMod) * (f.1 : ZMod)⁻¹ = s  (in Fin (q₀'+1))
        -- Both sides live in ZMod (q₀'+1) = Fin (q₀'+1)
        -- (s.val : ZMod (q₀'+1)) = s because natCast_zmod_val
        have hsval : (s.val : ZMod (q₀' + 1)) = s :=
          ZMod.natCast_zmod_val (n := q₀' + 1) s
        rw [← hsval, heq_s]
      -- Translate ¬ dvd to ≠ 0 in ZMod
      intro hdvd_bad
      -- In ZMod (q₀'+1): (α : ZMod) * (s.val : ZMod) + (β : ZMod) = 0
      -- because (q₀'+1 : ℤ) ∣ α * s.val + β
      have hzero : (f.1 : ZMod (q₀' + 1)) * (s.val : ZMod (q₀' + 1)) +
          (f.2 : ZMod (q₀' + 1)) = 0 := by
        -- Use: ¬(q₀'+1 : ℤ) ∣ n ↔ (n : ZMod (q₀'+1)) ≠ 0
        have hmod := (ZMod.intCast_zmod_eq_zero_iff_dvd
            ((f.1 : ℤ) * s.val + f.2) (q₀' + 1)).mpr hdvd_bad
        -- hmod : ((f.1 : ℤ) * ↑s.val + f.2 : ZMod (q₀' + 1)) = 0
        -- Simplify the int cast:
        push_cast at hmod
        -- hmod : (f.1 : ZMod) * (s.val : ZMod) + (f.2 : ZMod) = 0
        exact hmod
      -- From hzero: α * s.val = -β
      have hmuls : (f.1 : ZMod (q₀' + 1)) * (s.val : ZMod (q₀' + 1)) =
          -(f.2 : ZMod (q₀' + 1)) :=
        eq_neg_of_add_eq_zero_left hzero
      -- (s.val : ZMod) = -β * α⁻¹ = bad residue, contradiction
      apply hs_ne_bad
      -- From hmuls: α * s = -β, so s = -β * α⁻¹
      have hcancel : (s.val : ZMod (q₀' + 1)) =
          -(f.2 : ZMod (q₀' + 1)) * (f.1 : ZMod (q₀' + 1))⁻¹ := by
        have key : (f.1 : ZMod (q₀' + 1))⁻¹ * ((f.1 : ZMod (q₀' + 1)) *
            (s.val : ZMod (q₀' + 1))) = (f.1 : ZMod (q₀' + 1))⁻¹ *
            (-(f.2 : ZMod (q₀' + 1))) := by rw [hmuls]
        rw [← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul, mul_comm] at key
        exact key
      exact hcancel
    · -- Case q ∈ S': use ha₁_P and ha₀
      -- a₁ ≡ a₀ [MOD P] and q | P, so a₁ ≡ a₀ [MOD q]
      have hq_dvd_P : q ∣ P := Finset.dvd_prod_of_mem id hq_S'
      have ha₁_q : crt.val ≡ a₀ [MOD q] := ha₁_P.of_dvd hq_dvd_P
      -- (q : ℤ) ∣ (a₀ : ℤ) - crt.val
      have hdvd : (q : ℤ) ∣ (a₀ : ℤ) - crt.val := ha₁_q.dvd
      intro hdiv
      apply ha₀ q hq_S' f hf
      have hmul : (q : ℤ) ∣ (f.1 : ℤ) * ((a₀ : ℤ) - crt.val) :=
        dvd_mul_of_dvd_right hdvd _
      have heq : (f.1 : ℤ) * a₀ + f.2 =
          (f.1 : ℤ) * crt.val + f.2 + (f.1 : ℤ) * ((a₀ : ℤ) - crt.val) := by ring
      rw [heq]; exact dvd_add hdiv hmul

/-! ### Application to the residual hard-root states

The verified reduction yields two budgeted affine states `st_0` and
`st_24310` (corresponding to `r = 0` and `r = 24310` mod `46189`) with
at most 26 active clauses each. The session exhausted all primes
`≤ 5000` via local-divisibility descent without contradiction. By
`one_prime_escape_list` at any single prime ≥ 27, at least one good
residue exists; by `barrier_statement_form` (when fully proved), no
finite extension by additional primes can eliminate the hard states.

The "Residual Hard-Residue Sublemma" — prove neither state has an
integer solution, or exhibit one — therefore requires a non-elementary
input (witness search at true scale, nonlinear identity, global
analytic estimate, etc.).

The combinatorial heart of this barrier (`one_prime_escape` and its
list-form) is proved above with no `sorry`. -/

end Erdos647BarrierTheorem
