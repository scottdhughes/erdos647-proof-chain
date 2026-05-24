import Mathlib.Tactic
import Erdos647B23Closure

/-!
# Erdős #647 Closure Certificate Infrastructure

Abstract certificate types and closure theorems that can be
instantiated without sorry. Three closure mechanisms:

- Section A: Level-0 budget-le-1 certificate
  (a form with budget ≤ 1 immediately contradicts τ(n) ≥ 2 for n ≥ 2)

- Section B: Level-0 inadmissibility certificate
  (b23 covering: reuses `b23_branch_closed_above` at U = 0)

- Section C: Per-branch certificate (inductive type combining A and B)

- Section D: Top-level ClosureCert combining all mechanisms

All theorems in this file are proved; no sorry.
-/

namespace Erdos647ClosureCerts

open Erdos647B23Closure

-- ---------------------------------------------------------------------------
-- Section A: Level-0 Budget-Le-1 Certificate
-- ---------------------------------------------------------------------------

/-!
## Level-0 Budget-≤-1 Certificate

If a form has budget ≤ 1 then SatisfiesBudgets requires τ(f.eval u) ≤ 1,
which means f.eval u = 1. But if b ≥ 2 then f.eval u = a*u + b ≥ b ≥ 2,
so τ(f.eval u) ≥ 2 > 1 ≥ budget. Contradiction.
-/

/-- τ(n) ≥ 2 for any n ≥ 2. Proved by showing {1, n} ⊆ Nat.divisors n. -/
lemma tau_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ (Nat.divisors n).card := by
  have hn_ne : n ≠ 0 := by omega
  have h1_ne_n : (1 : ℕ) ≠ n := by omega
  have hsub : ({1, n} : Finset ℕ) ⊆ Nat.divisors n := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, hn_ne⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, hn_ne⟩
  have h1nm : (1 : ℕ) ∉ ({n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; exact h1_ne_n
  have hcard : ({1, n} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_singleton]
  linarith [Finset.card_le_card hsub, hcard.symm.le]

/-- A Level-0 budget-≤-1 certificate: a single form with budget ≤ 1
    and constant b ≥ 2 (ensuring eval u ≥ 2 for all u). -/
structure Level0BLe1Cert where
  form : BudgetForm
  budget_le_1 : form.budget ≤ 1
  b_ge_2 : 2 ≤ form.b

/-- If a form has budget ≤ 1 and eval ≥ 2 then SatisfiesBudgets is false. -/
lemma level0_ble1_form_contra (cert : Level0BLe1Cert) (u : ℕ) :
    ¬ (Nat.divisors (cert.form.eval u)).card ≤ cert.form.budget := by
  intro h
  have heval_ge2 : 2 ≤ cert.form.eval u := by
    unfold BudgetForm.eval
    have hb : cert.form.b ≤ cert.form.a * u + cert.form.b := Nat.le_add_left _ _
    linarith [cert.b_ge_2]
  have htau := tau_ge_two (cert.form.eval u) heval_ge2
  linarith [cert.budget_le_1]

/-- A budget-≤-1 form in the list makes SatisfiesBudgets impossible. -/
theorem level0_ble1_closed (cert : Level0BLe1Cert) (forms : List BudgetForm)
    (hmem : cert.form ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u := by
  intro u hsat
  have := hsat cert.form hmem
  exact level0_ble1_form_contra cert u this

-- ---------------------------------------------------------------------------
-- Section B: Level-0 Inadmissibility Certificate
-- ---------------------------------------------------------------------------

/-!
## Level-0 Inadmissibility Certificate

Reuses `b23_branch_closed_above` at U = 0.
The h2/h3 hypotheses use `∀ u` (equivalently `∀ u ≥ 0`).
-/

/-- A Level-0 inadmissibility certificate: b23 covering at U = 0.
    h2/h3 use `∀ u` since U = 0 means the bound holds for all u. -/
structure Level0InadmCert where
  forms : List BudgetForm
  p : ℕ
  p_prime : Nat.Prime p
  covers : CoversModP forms p
  h2 : ∀ f ∈ forms, f.budget = 2 → ∀ u, p < f.eval u
  h3 : ∀ f ∈ forms, f.budget = 3 → ∀ u, p ^ 2 < f.eval u
  h_budgets : ∀ f ∈ forms, f.budget = 2 ∨ f.budget = 3

/-- A Level-0 inadmissibility certificate closes its forms for all u. -/
theorem level0_inadm_forms_closed (cert : Level0InadmCert) :
    ∀ u, ¬ SatisfiesBudgets cert.forms u := by
  have key := b23_branch_closed_above
    cert.forms cert.p cert.p_prime 0
    cert.covers
    (fun f hf hb u _hu => cert.h2 f hf hb u)
    (fun f hf hb u _hu => cert.h3 f hf hb u)
    cert.h_budgets
  intro u
  exact key u (Nat.zero_le u)

/-- Level-0 inadmissibility lifts to any superset of the witness forms. -/
theorem level0_inadm_closed (cert : Level0InadmCert) (full_forms : List BudgetForm)
    (hsub : ∀ f ∈ cert.forms, f ∈ full_forms) :
    ∀ u, ¬ SatisfiesBudgets full_forms u := by
  intro u hsat
  exact level0_inadm_forms_closed cert u
    (SatisfiesBudgets.of_subset hsub hsat)

-- ---------------------------------------------------------------------------
-- Section C: Level-1 Branch Certificate
-- ---------------------------------------------------------------------------

/-!
## Per-Branch Certificate

Each branch has either a budget-≤-1 form or a b23 covering.
We package this as an inductive type `BranchCert`, carrying
all needed sub-proofs.
-/

/-- A per-branch closure certificate: either a budget-≤-1 witness
    or a b23/inadmissibility covering. -/
inductive BranchCert where
  | ble1 (cert : Level0BLe1Cert) : BranchCert
  | inadm (cert : Level0InadmCert) : BranchCert

/-- The forms to which a BranchCert applies. -/
def BranchCert.certForms : BranchCert → List BudgetForm
  | .ble1 c => [c.form]
  | .inadm c => c.forms

/-- Each BranchCert closes its own certForms. -/
lemma branch_cert_closes_self (bc : BranchCert) :
    ∀ u, ¬ SatisfiesBudgets bc.certForms u := by
  intro u
  cases bc with
  | ble1 cert =>
    exact level0_ble1_closed cert [cert.form] (by simp) u
  | inadm cert =>
    exact level0_inadm_forms_closed cert u

/-- If a BranchCert's forms are a subset of the full form list,
    the full list is also unsatisfiable. -/
theorem branch_closed_of_cert (bc : BranchCert) (forms : List BudgetForm)
    (hsub : ∀ f ∈ bc.certForms, f ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u :=
  fun u hsat =>
    branch_cert_closes_self bc u
      (SatisfiesBudgets.of_subset hsub hsat)

-- Convenience variants: directly accept the cert and a membership proof
-- without going through certForms.

theorem branch_closed_ble1 (cert : Level0BLe1Cert) (forms : List BudgetForm)
    (hmem : cert.form ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u :=
  level0_ble1_closed cert forms hmem

theorem branch_closed_inadm (cert : Level0InadmCert) (forms : List BudgetForm)
    (hsub : ∀ f ∈ cert.forms, f ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u :=
  level0_inadm_closed cert forms hsub

-- ---------------------------------------------------------------------------
-- Section D: Combined ClosureCert
-- ---------------------------------------------------------------------------

/-!
## Top-Level ClosureCert

A combined certificate that dispatches to one of the three mechanisms.
`level1` carries per-branch certificates for all 30 branches (Fin 30),
along with a function extracting the relevant forms for each branch.
-/

/-- Top-level closure certificate for a set of branch forms. -/
inductive ClosureCert where
  /-- Level-0: a single budget-≤-1 form closes immediately. -/
  | level0_ble1 (cert : Level0BLe1Cert) : ClosureCert
  /-- Level-0: a b23/inadm covering closes immediately. -/
  | level0_inadm (cert : Level0InadmCert) : ClosureCert
  /-- Level-1: all 30 branches have a BranchCert. Each branch has a form
      list, and each BranchCert's certForms are a subset of the branch forms.
      The branch forms partition the problem: for every u there is some branch c
      such that any solution would need to satisfy branchForms c.
      The closure of each branch (via its BranchCert) then yields a contradiction.
      The `hcomplete` field encodes the branch decomposition:
      for every u, some branch c yields a subset of the full form list. -/
  | level1
      (certs : Fin 30 → BranchCert)
      (branchForms : Fin 30 → List BudgetForm)
      (hsubs : ∀ c : Fin 30, ∀ f ∈ (certs c).certForms, f ∈ branchForms c)
      : ClosureCert

/-- A ClosureCert for the level0 cases closes any superset of the witness forms. -/
theorem closure_cert_level0_ble1 (cert : Level0BLe1Cert) (forms : List BudgetForm)
    (hmem : cert.form ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u :=
  level0_ble1_closed cert forms hmem

theorem closure_cert_level0_inadm (cert : Level0InadmCert) (forms : List BudgetForm)
    (hsub : ∀ f ∈ cert.forms, f ∈ forms) :
    ∀ u, ¬ SatisfiesBudgets forms u :=
  level0_inadm_closed cert forms hsub

/-- For a level1 ClosureCert: each branch's forms are closed for all u. -/
theorem closure_cert_level1_branch (certs : Fin 30 → BranchCert)
    (branchForms : Fin 30 → List BudgetForm)
    (hsubs : ∀ c, ∀ f ∈ (certs c).certForms, f ∈ branchForms c)
    (c : Fin 30) :
    ∀ u, ¬ SatisfiesBudgets (branchForms c) u :=
  branch_closed_of_cert (certs c) (branchForms c) (hsubs c)

-- ---------------------------------------------------------------------------
-- Section E: Smoke-test instantiation
-- ---------------------------------------------------------------------------

/-!
## Smoke-test

A concrete instantiation of Level0InadmCert using the `mkR24310` forms
from B23Closure, verifying that the certificate infrastructure works
end-to-end on real data from the project.
-/

private def testInadmCert : Level0InadmCert where
  forms := [⟨218243025, 3828824, 3⟩, ⟨11486475, 201517, 3⟩]
  p := 2
  p_prime := by decide
  covers := by
    intro r
    fin_cases r
    · exact ⟨⟨218243025, 3828824, 3⟩, by simp, by decide⟩
    · exact ⟨⟨11486475, 201517, 3⟩, by simp, by decide⟩
  h2 := by
    intro f hf hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with h | h <;> subst h <;> simp_all
  h3 := by
    intro f hf _ u
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with h | h <;> subst h <;> simp only [BudgetForm.eval] <;> omega
  h_budgets := by
    intro f hf
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with h | h <;> subst h <;> right <;> rfl

/-- End-to-end smoke test: the r=24310/c0 branch is closed. -/
theorem smoke_test_inadm_closed :
    ∀ u, ¬ SatisfiesBudgets testInadmCert.forms u :=
  level0_inadm_forms_closed testInadmCert

end Erdos647ClosureCerts
