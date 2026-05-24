import Mathlib.Tactic

namespace Erdos647B23Closure

structure BudgetForm where
  a : ℕ
  b : ℕ
  budget : ℕ
  deriving DecidableEq, Repr

def BudgetForm.eval (f : BudgetForm) (u : ℕ) : ℕ := f.a * u + f.b

def SatisfiesBudgets (forms : List BudgetForm) (u : ℕ) : Prop :=
  ∀ f ∈ forms, (Nat.divisors (f.eval u)).card ≤ f.budget

lemma SatisfiesBudgets.of_subset {witness full : List BudgetForm} {u : ℕ}
    (hmem : ∀ f ∈ witness, f ∈ full)
    (hsat : SatisfiesBudgets full u) :
    SatisfiesBudgets witness u :=
  fun f hf => hsat f (hmem f hf)

-- Helper: a Finset subset of Nat.divisors
private lemma sub_div {m : ℕ} (hm : m ≠ 0) {s : Finset ℕ} (hs : ∀ d ∈ s, d ∣ m) :
    s ⊆ Nat.divisors m :=
  fun _ hd => Nat.mem_divisors.mpr ⟨hs _ hd, hm⟩

/-- If prime p divides n and n > p, then τ(n) ≥ 3. -/
lemma tau_ge_three_of_prime_dvd_and_gt {p n : ℕ}
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hgt : p < n) :
    3 ≤ (Nat.divisors n).card := by
  have hn_pos : 0 < n := lt_trans hp.pos hgt
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  have hp_ge2 : 2 ≤ p := hp.two_le
  -- {1, p, n} ⊆ Nat.divisors n
  have hsub : ({1, p, n} : Finset ℕ) ⊆ Nat.divisors n := by
    apply sub_div hn_ne
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact one_dvd _
    · exact hdvd
    · exact dvd_refl _
  -- The three elements are distinct
  have h1p : (1 : ℕ) ∉ ({p, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hpn : p ∉ ({n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  have hcard : ({1, p, n} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem h1p, Finset.card_insert_of_notMem hpn,
        Finset.card_singleton]
  linarith [Finset.card_le_card hsub, hcard.symm.le]

/-- If prime p divides n and n > p², then τ(n) ≥ 4. -/
lemma tau_ge_four_of_prime_dvd_and_gt_sq {p n : ℕ}
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hgt : p ^ 2 < n) :
    4 ≤ (Nat.divisors n).card := by
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hn_pos : 0 < n := by
    calc 0 < p ^ 2 := by positivity
    _ < n := hgt
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  -- Write n = p * k
  obtain ⟨k, hk⟩ := hdvd
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk; omega
    · exact hpos
  have hk_gt_p : p < k := by
    have hpk : p ^ 2 < p * k := hk ▸ hgt
    have hppk : p * p < p * k := by rw [← sq]; exact hpk
    exact Nat.lt_of_mul_lt_mul_left hppk
  -- {1, p, k, n} ⊆ Nat.divisors n
  have hsub : ({1, p, k, n} : Finset ℕ) ⊆ Nat.divisors n := by
    apply sub_div hn_ne
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact ⟨k, hk⟩
    · exact ⟨p, by rw [hk, mul_comm]⟩
    · exact dvd_refl _
  -- The four elements are distinct: 1 < p < k < n (= p * k)
  have hn_eq : n = p * k := hk
  have h1_lt_p : 1 < p := hp.one_lt
  have hk_gt1 : 1 < k := by omega
  have hn_gt_k : k < n := by rw [hn_eq]; nlinarith
  have h1nm : (1 : ℕ) ∉ ({p, k, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hpnm : p ∉ ({k, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hknm : k ∉ ({n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  have hcard : ({1, p, k, n} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem h1nm, Finset.card_insert_of_notMem hpnm,
        Finset.card_insert_of_notMem hknm, Finset.card_singleton]
  linarith [Finset.card_le_card hsub, hcard.symm.le]

-- Section 4: Monotonicity and modular transfer

lemma eval_mono (f : BudgetForm) {U u : ℕ} (h : U ≤ u) :
    f.eval U ≤ f.eval u := by
  unfold BudgetForm.eval
  have : f.a * U ≤ f.a * u := Nat.mul_le_mul_left f.a h
  omega

lemma bound_from_eval_at_U (f : BudgetForm) (k U : ℕ) (h : k < f.eval U) :
    ∀ u, U ≤ u → k < f.eval u :=
  fun _u hu => lt_of_lt_of_le h (eval_mono f hu)

lemma dvd_eval_of_dvd_eval_mod (f : BudgetForm) (p : ℕ) (_hp : 0 < p) (u : ℕ)
    (h : p ∣ f.eval (u % p)) : p ∣ f.eval u := by
  have key : f.eval u % p = f.eval (u % p) % p := by
    unfold BudgetForm.eval
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rwa [Nat.dvd_iff_mod_eq_zero, key, ← Nat.dvd_iff_mod_eq_zero]

-- Section 5: Covering predicate

def CoversModP (forms : List BudgetForm) (p : ℕ) : Prop :=
  ∀ r : Fin p, ∃ f ∈ forms, (p : ℕ) ∣ (f.eval r.val)

def coversModPBool (forms : List BudgetForm) (p : ℕ) : Bool :=
  (List.finRange p).all fun r =>
    forms.any fun f => f.eval r.val % p == 0

lemma coversModPBool_correct (forms : List BudgetForm) (p : ℕ)
    (h : coversModPBool forms p = true) : CoversModP forms p := by
  intro r
  simp only [coversModPBool, List.all_eq_true, List.any_eq_true,
             List.mem_finRange, true_implies] at h
  obtain ⟨f, hf_mem, hf_mod⟩ := h r
  simp only [beq_iff_eq] at hf_mod
  exact ⟨f, hf_mem, Nat.dvd_of_mod_eq_zero hf_mod⟩

-- Section 6: The generic b23 branch-closure theorem

theorem b23_branch_closed_above
    (forms : List BudgetForm)
    (p : ℕ) (hp : Nat.Prime p)
    (U : ℕ)
    (hcov : CoversModP forms p)
    (h2 : ∀ f ∈ forms, f.budget = 2 → ∀ u, U ≤ u → p < f.eval u)
    (h3 : ∀ f ∈ forms, f.budget = 3 → ∀ u, U ≤ u → p ^ 2 < f.eval u)
    (h_budgets : ∀ f ∈ forms, f.budget = 2 ∨ f.budget = 3) :
    ∀ u, U ≤ u → ¬ SatisfiesBudgets forms u := by
  intro u hu hsat
  -- Step 1: get covering form at u % p
  have hp0 : 0 < p := hp.pos
  have hr : (u % p) < p := Nat.mod_lt u hp0
  obtain ⟨f, hf_mem, hf_dvd_mod⟩ := hcov ⟨u % p, hr⟩
  -- Step 2: transfer divisibility
  have hf_dvd : p ∣ f.eval u := dvd_eval_of_dvd_eval_mod f p hp0 u hf_dvd_mod
  -- Step 3: get budget constraint
  have hf_sat := hsat f hf_mem
  -- Step 4: case split on budget
  rcases h_budgets f hf_mem with hb2 | hb3
  · -- budget = 2: tau >= 3 but budget says tau <= 2
    have hgt := h2 f hf_mem hb2 u hu
    have htau := tau_ge_three_of_prime_dvd_and_gt hp hf_dvd hgt
    rw [hb2] at hf_sat; omega
  · -- budget = 3: tau >= 4 but budget says tau <= 3
    have hgt := h3 f hf_mem hb3 u hu
    have htau := tau_ge_four_of_prime_dvd_and_gt_sq hp hf_dvd hgt
    rw [hb3] at hf_sat; omega

-- Section 7: Toy test

private def toyForms : List BudgetForm := [⟨3, 100, 3⟩, ⟨3, 101, 3⟩]

-- toyForms covers Z/2Z:
--   form1 at r=0: eval(0) = 100, 100 % 2 = 0
--   form2 at r=1: eval(1) = 104, 104 % 2 = 0
private lemma toyForms_covers : CoversModP toyForms 2 := by
  intro r
  fin_cases r
  · -- r = 0: form1 covers it
    exact ⟨⟨3, 100, 3⟩, by simp [toyForms], by decide⟩
  · -- r = 1: form2 covers it
    exact ⟨⟨3, 101, 3⟩, by simp [toyForms], by decide⟩

private theorem toy_test : ∀ u, ¬ SatisfiesBudgets toyForms u := by
  have key := b23_branch_closed_above toyForms 2 (by norm_num) 0
    toyForms_covers
    (-- h2: budget = 2 forms need p < eval u. No form has budget = 2.
     by intro f hf hb2
        simp [toyForms] at hf
        rcases hf with rfl | rfl <;> simp at hb2)
    (-- h3: budget = 3 forms need 4 < eval u for u ≥ 0
     by intro f hf _hb3 u _hu
        simp [toyForms] at hf
        rcases hf with rfl | rfl
        · simp only [BudgetForm.eval]; omega
        · simp only [BudgetForm.eval]; omega)
    (-- h_budgets: all budgets are 3
     by intro f hf
        simp [toyForms] at hf
        rcases hf with rfl | rfl <;> simp)
  intro u
  exact key u (Nat.zero_le u)

/-! ## Section 8: Parameterized certificate helper for r=24310

All 6 b23 branches at r=24310 use p=2, U=0, and two budget-3 forms with
fixed leading coefficients a₁=218243025 and a₂=11486475. Only the constant
terms (b₁, b₂) vary per branch.

**Correctness boundary:** The coefficients below are derived from the
Erdős #647 reduction at r=24310 via scripts/classify_all_96.py. The Lean
formalization verifies the b23 closure given these coefficients; it does
NOT verify that the coefficients correctly encode the problem structure.
That verification is external (Python computation + hand-check). -/

/-- Two budget-3 forms for r=24310 branches. The leading coefficients
    are fixed; only the constant terms vary per branch. -/
private def mkR24310 (b1 b2 : ℕ) : List BudgetForm :=
  [⟨218243025, b1, 3⟩, ⟨11486475, b2, 3⟩]

/-- Parameterized closure for r=24310 b23 branches.
    Given constant terms (b1, b2) such that the forms cover Z/2Z
    and both constants exceed 4 = p², the branch closes. -/
theorem mkR24310_closed (b1 b2 : ℕ)
    (hcov : CoversModP (mkR24310 b1 b2) 2)
    (hb1 : 4 < b1) (hb2 : 4 < b2) :
    ∀ u, ¬ SatisfiesBudgets (mkR24310 b1 b2) u := by
  have h := b23_branch_closed_above (mkR24310 b1 b2) 2 (by decide) 0
    hcov
    (by -- h2: vacuous since all forms have budget 3, not 2
        intro f hf hb
        simp only [mkR24310, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with h | h <;> subst h <;> simp_all)
    (by -- h3: 2^2 = 4 < f.eval u, using hb1/hb2
        intro f hf _ u _
        simp only [mkR24310, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with h | h <;> subst h <;> simp only [BudgetForm.eval] <;> omega)
    (by -- h_budgets: all forms have budget 3
        intro f hf
        simp only [mkR24310, List.mem_cons, List.mem_nil_iff, or_false] at hf
        rcases hf with h | h <;> subst h <;> right <;> rfl)
  intro u; exact h u (Nat.zero_le u)

-- The 6 b23 branch certificates, each a one-line application.
-- Covering discharged by native_decide on the Bool checker.
-- Bounds discharged by omega (4 < specific_constant).

theorem r24310_c0_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 3828824 201517) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

theorem r24310_c8_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 62026964 3264577) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

theorem r24310_c10_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 76576499 4030342) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

theorem r24310_c18_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 134774639 7093402) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

theorem r24310_c20_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 149324174 7859167) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

theorem r24310_c28_closed : ∀ u, ¬ SatisfiesBudgets (mkR24310 207522314 10922227) u :=
  mkR24310_closed _ _ (coversModPBool_correct _ _ (by native_decide)) (by omega) (by omega)

/-! ## Section 9: Lifting witness contradictions to full branch forms

The certificates above prove `¬ SatisfiesBudgets witness_forms u` for small
witness lists (2 forms each). To conclude that the FULL branch (all active
forms from the Erdős #647 reduction) is also unsatisfiable, we use:

If `witness ⊆ full` and `¬ SatisfiesBudgets witness u`, then
`¬ SatisfiesBudgets full u`.

This is the contrapositive of `SatisfiesBudgets.of_subset`. -/

/-- Contrapositive of `of_subset`: if a sublist is unsatisfiable,
    any superlist is also unsatisfiable. -/
theorem SatisfiesBudgets.not_of_superset {witness full : List BudgetForm} {u : ℕ}
    (hmem : ∀ f ∈ witness, f ∈ full)
    (hbot : ¬ SatisfiesBudgets witness u) :
    ¬ SatisfiesBudgets full u :=
  fun hsat => hbot (SatisfiesBudgets.of_subset hmem hsat)

/-! **Application to r=24310.**

Each `r24310_c*` list contains the two budget-3 covering forms for that
branch. These are a subset of the full set of divisor constraints that
any Erdős #647 solution at r=24310 must satisfy. By
`SatisfiesBudgets.not_of_superset`, the contradiction on the witness
forms lifts to any superset — including the full constraint system.

Therefore: any list of BudgetForms containing `r24310_c*` as a sublist
is unsatisfiable for all u. This is the formal content of
"branch c closes at r=24310." -/

/-! ## Section 10: Bridge gaps

The certificates above prove about `SatisfiesBudgets` (BudgetForm lists).
The open problem is about `Candidate n` (Mathlib's σ 0). Three bridge
gaps connect them. These are documented here; the actual sorry-bearing
bridge theorems live in `Erdos647ReductionChain.lean` which imports
both Main and BridgeV1.

| Step | Status |
|------|--------|
| Finite coverage (n ≤ 84) | proved (Main) |
| 2520-divisibility (n > 84) | proved (BridgeV1) |
| Sieve card = 96 | proved (SieveCertificate, abstract residues) |
| 6 r=24310 b23 branches | proved (this file) |
| Bridge 1: Candidate ↔ IsErdos647 | NOT YET FORMALIZED |
| Bridge 2: IsErdos647 → sieve residues | NOT YET FORMALIZED |
| Bridge 3: sieve residues → SatisfiesBudgets | NOT YET FORMALIZED |
| Open problem | OPEN |

See `Erdos647ReductionChain.lean` for the sorry-bearing chain. -/

end Erdos647B23Closure
