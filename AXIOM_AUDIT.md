# Axiom audit

The active Lean modules in this repository have been compiled and their
axiom profiles inspected via `#print axioms`. This document records the
current proof-critical surface together with the key legacy and
supporting modules that matter for interpreting the repository state.
Reproduce the main Stage-1 audit with `bash scripts/axiom_audit.sh`.

**Summary (as of 2026-05-24, Stage-1 formal-core rewrite):**

* `0` source-level sorries in `lean/`
* `1` intentional Stage-1 axiom:
  `Erdos647Stage1Axiom.openResiduesStage1_no_solution`

The active theorem path no longer uses `Bridge3`, `branchForms`, or
`SatisfiesBudgets`. Instead it goes through:

* theorem-grade full-value closures for `55` sieve residues
  (`42` single-overlap + `13` direct full-value),
* the proof-critical open set `openResiduesStage1`, defined as the
  complement of those closures inside the `96` theorem-grade sieve
  survivors, and
* the conditional theorem
  `Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1`.

The current honest Stage-1 state is therefore:

* `55` theorem-grade closed residues
* `41` open residues
* diagnostic decomposition:
  * `27` non-`ble1`
  * `14` genuinely hard

The axiom wrapper theorem
`Erdos647Stage1Axiom.erdos647_with_stage1_axiom`
depends on exactly that open-set axiom, plus the ordinary trusted
foundations and the existing `native_decide`-generated native axioms
already present in theorem-grade modules such as `Bridge2`.

Separate from the Stage-1 no-solution frontier, the repository also now
contains a deterministic conditional existence-direction theorem in
`Erdos647ConditionalFiniteWindow.lean`. That module is not on the
active Stage-1 proof path and is audited separately below.

The confirmed 13/13 shape-prime witness at r=0 (t=11,741,230,040,310)
demonstrates that BH's prediction of populated admissibility is
empirically real; the D1 registry (13 records) shows all observed
hits fail the full Erdős condition at small non-shape k ∈ {7, 11, 13, 14}.

---

## Fully verified core (zero sorry)

### Erdos647SieveCertificate.lean

| Theorem | Axioms |
|---------|--------|
| `surviving_card` | propext, Lean.ofReduceBool |
| `no_forced_prime_killer` | propext, Lean.ofReduceBool |

- Sorry count: **0**
- Uses `native_decide`: yes (96 × 1000 sieve evaluations)
- Trusted core: **yes**

### Erdos647HardRootAdmissibility.lean

| Theorem | Axioms |
|---------|--------|
| `hard_root_r_zero_admissible` | propext, Lean.ofReduceBool |
| `hard_root_r_24310_admissible` | propext, Lean.ofReduceBool |
| `hardRootCoeffs_length` | propext, Lean.ofReduceBool |
| `numForbiddenAt_le_length` | propext |
| `admissibleAt_large` | propext |
| `hard_root_r_zero_admissible_all` | propext, Lean.ofReduceBool |
| `hard_root_r_24310_admissible_all` | propext, Lean.ofReduceBool |

- Sorry count: **0**
- Uses `native_decide`: yes (finite check at p ≤ 13)
- Structural proof: `numForbiddenAt_le_length` and `admissibleAt_large`
  use only propext (no native_decide), proving the pigeonhole bound
  for all primes p > 13
- Scope: the Lean proof covers BOTH the 13-form core sub-tuple
  `hardRootCoeffs` (theorems above) AND the full budget-≤3 tuples
  of sizes 13/17/15/15/17 per residue via
  `hard_root_r_{0,1716,4862,16302,17160}_full_admissible_all` and
  their supporting infrastructure (`forbiddenResidueOfFormPair`,
  `numForbiddenAtFull`, `numForbiddenAtFull_le_length`,
  `admissibleAtFull_large`, `fullCoeffs_r*_length`). Full-tuple
  coefficients match `data/hard_root_forms_r*.json` exactly;
  admissibility independently cross-verified at p ≤ 499 in
  `data/admissibility_new_hard_residues.json`.
- Note on redundancy: the sub-tuple theorems (`hard_root_r_*_admissible_all`)
  are mathematically entailed by the full-tuple theorems
  (`hard_root_r_*_full_admissible_all`) but retained because they
  correspond to the smaller tuple relevant to the conditional-Dickson
  prime-core argument in the reduction chain; the full-tuple theorems
  are the complete claim about the budget-≤3 tuples at every prime.
- Trusted core: **yes**

### Erdos647Closure92_Legacy.lean

| Theorem | Axioms |
|---------|--------|
| `partition_counts` | propext, Lean.ofReduceBool |
| `hard_partition` | propext, Lean.ofReduceBool |
| `closed_hard_partition` | propext, Lean.ofReduceBool |
| `hard_residues_divisible_by_2431` | propext, Quot.sound |
| `level2_residues_divisible_by_143` | propext, Quot.sound |
| `r_zero_div_46189` | propext, Quot.sound |
| `r_24310_factorization` | propext, Quot.sound |

- Sorry count: **0**
- Uses `native_decide`: yes (partition count computation)
- Imports: `Erdos647SieveCertificate`
- **Status:** superseded by the 91/5 reclassification. Retained
  for historical continuity and as input to the barrier theorem.
- Trusted core: **yes**

### Erdos647BarrierTheorem.lean

| Theorem | Axioms |
|---------|--------|
| `one_prime_escape` | propext, Classical.choice, Quot.sound |
| `one_prime_escape_list` | propext, Classical.choice, Quot.sound |
| `barrier_statement_form` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |

- Sorry count: **0**
- `barrier_statement_form` proved by `Finset.induction` on `S`,
  applying `one_prime_escape` at each new prime and lifting via
  CRT (modular arithmetic in `ZMod`).
- Trusted core: **yes**

### Erdos647BridgeV1.lean

| Theorem | Axioms |
|---------|--------|
| `erdos647_div_2520` | propext, Lean.ofReduceBool |
| `not_sq_2520N_sub_one` | propext |
| `explicit_candidate_fails` | propext, Lean.ofReduceBool |

- Sorry count: **0**
- `erdos647_div_2520`: case analysis (2, 4, 8, 3, 9, 5, 7) combining
  to 2520 | n. The 7-divisibility step is split into 6 sub-lemmas
  for heartbeat management.
- `not_sq_2520N_sub_one`: mod-4 argument (2520N-1 is 3 mod 4;
  squares are 0 or 1 mod 4).
- `explicit_candidate_fails`: 17 explicit divisors of
  604517614941226 give τ ≥ 17 > 16.
- Trusted core: **yes**

### Erdos647B23Closure.lean

| Theorem | Axioms |
|---------|--------|
| generic b23 closure theorems | propext, Lean.ofReduceBool |
| 6 r=24310 certificate instances | propext, Lean.ofReduceBool |

- Sorry count: **0**
- Provides the generic b23 mechanism (budget-2/3 forms covering
  `Z/pZ` at an operative prime) and 6 concrete certificate
  instances at r = 24310.
- Trusted core: **yes**

### Erdos647ClosureCerts.lean

| Theorem | Axioms |
|---------|--------|
| certificate type constructors + abstract theorems | propext |

- Sorry count: **0**
- Certificate types for the three closure mechanisms: `level0_ble1`,
  `level0_inadm_b2`/`level0_inadm_b23`, `level1_branched`. Abstract
  theorems applied to the 207 concrete instances in
  `Erdos647ClosureData.lean`.
- Trusted core: **yes**

### Erdos647ClosureData.lean

| Artifact | Axioms |
|----------|--------|
| 314 certificate instances | propext, Lean.ofReduceBool |

- Sorry count: **0**
- **Auto-generated** by `scripts/generate_lean_certs.py` from
  `data/closure_certificates_v2.json`.
- Provides one concrete certificate per closed (residue, branch)
  pair, covering 82 of 96 residues across 30 branches.
- Trusted core: **yes**

### Erdos647BranchForms.lean

| Theorem | Axioms |
|---------|--------|
| `branchForms` definition + 82 per-residue closure theorems | propext, Lean.ofReduceBool |
| `closed_residue_all_branches` | propext, Lean.ofReduceBool |

- Sorry count: **0**
- **Auto-generated** by `scripts/generate_branch_forms.py`.
- Provides a concrete (non-opaque) `branchForms : ℕ → Fin 30 → List BudgetForm`
  returning the certificate witness forms. Bridge 4 of the reduction
  chain is discharged here using the 314 v2 certificates.
- Trusted core: **yes**

---

## Reduction chain (conditional theorem + 1 Stage-1 axiom)

### Erdos647ReductionChain.lean

| Theorem | Axioms | Status |
|---------|--------|--------|
| `bridge_candidate_to_isErdos647` | propext | **proved** (Bridge 1, 6 lines) |
| `bridge_isErdos647_to_sieve` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool | **proved** (Bridge 2, via `Bridge2.lean` + two conversion lemmas) |
| `candidate_false_large_conditional_on_openResiduesStage1` | theorem-grade modules + native axioms already present in those modules | **proved** |
| `erdos647_conditional_on_openResiduesStage1` | theorem-grade modules + native axioms already present in those modules | **proved** |
| `openResiduesStage1_no_solution` | **axiom** | Stage-1 open set axiom (`41` residues in Stage-1 state) |
| `erdos647_with_stage1_axiom` | above axiom + theorem-grade modules | **proved from above** |

- Source-level sorry count on the active chain: **0**
- Proof-critical axiom count on the active chain: **1**
- `Bridge3` has been retired to an inert legacy stub and removed from the
  active theorem path.

### Erdos647ConditionalFiniteWindow.lean

| Theorem | Axioms |
|---------|--------|
| `windowGood_of_primeCofactors` | propext, Classical.choice, Quot.sound |
| `windowGood80_of_primeCofactors` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |
| `residue_zero_mod_M_for_K20` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |

- Sorry count: **0**
- Role: separate positive-direction theorem package; **not** part of the
  Stage-1 no-solution frontier
- `windowGood_of_primeCofactors` proves the full-value deterministic
  implication from prime-cofactor hypotheses to a finite-window divisor
  bound.
- `windowGood80_of_primeCofactors` adds the finite arithmetic bound
  `2 * τ(k) ≤ k + 2` for `k ≤ 80` via `native_decide`.
- `residue_zero_mod_M_for_K20` records the arithmetic placement fact
  `L_20 / 2520 = 2 * 46189`, so the `K = 20` construction lies in
  residue `0 mod M`.

### Bridge2.lean

| Theorem | Axioms |
|---------|--------|
| `Bridge2.bridge_isErdos647_to_sieve` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |
| `Bridge2.tau_ge_large_noncoprime` | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |
| All helper lemmas (`extract_extra_prime`, `p_dvd_n_from_not_coprime`, `n_eq_pa_qb`, `tau_kn_bound_pa_qb`, ...) | propext, Classical.choice, Quot.sound, Lean.ofReduceBool |

- Sorry count: **0**
- Uses `native_decide`: yes (48-cell bound table in `tau_kn_at_a_min`;
  24-cell threshold in `a_min_characterization`; finite check
  `all_pairs_check`)
- Namespace-wrapped as `Bridge2` to avoid collision with
  `Erdos647SieveCertificate` / `Erdos647BridgeV1` analogues.
- The `tau_ge_large_noncoprime` sub-lemma was hand-closed across all
  6 hard coefficient values via the documented proof sketch.
- Trusted core: **yes**
- Role on the active chain: supplies the theorem-grade sieve reduction
  used by `Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1`.

---

## Legacy wrapper

### Erdos647Main.lean

| Item | Axioms | Status |
|------|--------|--------|
| `candidate_false_finite` | propext, Lean.ofReduceBool | proved (25 ≤ n ≤ 84 by `native_decide`) |
| Stage-1 note | n/a | file-level docs updated to point at `Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1` and `Erdos647Stage1Axiom.erdos647_with_stage1_axiom` |

- Sorry count: **0**
- Proof-critical axiom count in this file: **0**

---

## Consolidated open content

| Open item | Location | Scope |
|-----------|----------|-------|
| `openResiduesStage1_no_solution` | `Erdos647Stage1Axiom.lean` | the current proof-critical open set (`41` residues in Stage 1) |

The remaining mathematical frontier is now carried by the open-set axiom
only. The old Bridge-3 proof-engineering debt is no longer on the active
theorem path.

---

## Note on native_decide

All finite-computational claims are discharged via Lean's
`native_decide`, which extends the trusted base by the correctness
of Lean's native-code compiler (`Lean.ofReduceBool`). This is
standard practice in formal verification and is used throughout
Mathlib. The `propext` axiom (propositional extensionality) is a
standard foundational axiom of Lean's type theory.
