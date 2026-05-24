# Theorem map

This map is organized by the **current** Stage-1 proof surface first.
Historical atlas / hard-5 results are retained below as supporting or
superseded material, not as the active frontier.

## Active Stage-1 core

| Statement | Lean theorem / object | File | Status |
|-----------|------------------------|------|--------|
| 96 surviving residues mod 46189 | `surviving_card` | `lean/Erdos647SieveCertificate.lean` | proved |
| 42 single-overlap closures | `no_erdos647_of_mem_singleOverlapResidues42` | `lean/Erdos647SingleOverlapClosure.lean` | proved |
| 13 direct full-value closures | `no_erdos647_of_mem_directFullValueResidues13` | `lean/Erdos647DirectFullValueClosure.lean` | proved |
| Proof-critical Stage-1 closed set | `closedResiduesStage1` | `lean/Erdos647ResiduePartitionStage1.lean` | defined |
| Proof-critical Stage-1 open set | `openResiduesStage1` | `lean/Erdos647ResiduePartitionStage1.lean` | defined by complement |
| Closed-set cardinality | `closedResiduesStage1_card` | `lean/Erdos647ResiduePartitionStage1.lean` | proved (`55`) |
| Open-set cardinality | `openResiduesStage1_card` | `lean/Erdos647ResiduePartitionStage1.lean` | proved (`41`) |
| Survivor partition | `surviving_eq_closed_union_open` | `lean/Erdos647ResiduePartitionStage1.lean` | proved |
| Conditional reduction theorem | `erdos647_conditional_on_openResiduesStage1` | `lean/Erdos647ReductionChain.lean` | proved |
| Large-`N` conditional reduction theorem | `erdos647_conditional_on_openResiduesStage1_large` | `lean/Erdos647ReductionChain.lean` | proved |
| Stage-1 axiom wrapper | `erdos647_with_stage1_axiom` | `lean/Erdos647Stage1Axiom.lean` | proved from 1 axiom |
| Single intentional Stage-1 axiom | `openResiduesStage1_no_solution` | `lean/Erdos647Stage1Axiom.lean` | **axiom** (`41` residues) |

Current honest boundary:

* theorem-grade closed residues: `55`
* open residues: `41`
* diagnostic split: `27` non-`ble1`, `14` genuinely hard

## Separate conditional theorem

| Statement | Lean theorem / object | File | Status |
|-----------|------------------------|------|--------|
| Prefix least common multiple | `prefixLcm` | `lean/Erdos647ConditionalFiniteWindow.lean` | defined |
| Prime-cofactor hypothesis | `PrimeCofactorHyp` | `lean/Erdos647ConditionalFiniteWindow.lean` | defined |
| Generic deterministic window theorem | `windowGood_of_primeCofactors` | `lean/Erdos647ConditionalFiniteWindow.lean` | proved |
| Concrete `K = 20` corollary | `windowGood20_of_primeCofactors` | `lean/Erdos647ConditionalFiniteWindow.lean` | proved |
| Concrete `K = 80` corollary | `windowGood80_of_primeCofactors` | `lean/Erdos647ConditionalFiniteWindow.lean` | proved |
| `K = 20` residue-0 placement | `residue_zero_mod_M_for_K20` | `lean/Erdos647ConditionalFiniteWindow.lean` | proved |

This finite-window package is **not** part of the Stage-1 no-solution
frontier. It is a separate positive-direction theorem under explicit
prime-cofactor hypotheses.

## Structural theorem-design support

| Statement | Lean theorem / object | File | Status |
|-----------|------------------------|------|--------|
| Mod-529 sub-AP decomposition | `NSubAP_decompose` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved |
| k=1 shifted-prime channel | `F1_prime_of_isErdos647` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved |
| Fixed-window shifted-prime tail target | `ShiftedPrimeOpenSubAPCloses` | `lean/Erdos647ShiftedPrimeChannel.lean` | target predicate |
| Pointwise shifted-prime tail target | `ShiftedPrimeOpenSubAPClosesBy` | `lean/Erdos647ShiftedPrimeChannel.lean` | target predicate |
| Fixed target as pointwise special case | `shiftedPrimeOpenSubAPClosesBy_const` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved |
| Large open-residue wrapper | `large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPCloses` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved from target predicate |
| Large pointwise open-residue wrapper | `large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPClosesBy` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved from target predicate |
| Conditional #647 from shifted-prime tail closure | `erdos647_conditional_on_shiftedPrimeOpenSubAPCloses` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved from target predicate |
| Conditional #647 from pointwise shifted-prime tail closure | `erdos647_conditional_on_shiftedPrimeOpenSubAPClosesBy` | `lean/Erdos647ShiftedPrimeChannel.lean` | proved from target predicate |

This package does not close the Stage-1 frontier by itself. It exposes
the exact theorem-design target needed to replace the open-residue axiom
by a shifted-prime divisor theorem. After the fixed-window B1 branch was
archived negative, the pointwise target is the preferred active surface;
the fixed-`K` predicate remains as a stronger special case.

## Supporting theorem-grade infrastructure

| Statement | Lean theorem / object | File | Status |
|-----------|------------------------|------|--------|
| Bridge 1: `Candidate → IsErdos647` | `bridge_candidate_to_isErdos647` | `lean/Erdos647ReductionChain.lean` | proved |
| Bridge 2: `IsErdos647 → sieve residue` | `Bridge2.bridge_isErdos647_to_sieve` | `lean/Bridge2.lean` | proved |
| 2520-divisibility | `erdos647_div_2520` | `lean/Erdos647BridgeV1.lean` | proved |
| Finite coverage `25 ≤ n ≤ 84` | `candidate_false_finite` | `lean/Erdos647Main.lean` | proved |

## Historical / superseded formal material

These files remain in the repo because they still carry useful data or
background results, but they are **not** the current proof-critical
frontier.

| Historical item | Lean theorem / object | File | Current role |
|-----------------|-----------------------|------|--------------|
| 92/2/2 partition | `partition_counts`, `hard_partition`, `closed_hard_partition` | `lean/Erdos647Closure92_Legacy.lean` | superseded historical partition |
| Exact-v2 atlas closures | `closed_residue_all_branches` + generated closures | `lean/Erdos647BranchForms.lean` / `lean/Erdos647ClosureData.lean` | ledger / routing data, not proof-critical |
| Closure mechanism abstractions | certificate theorems | `lean/Erdos647ClosureCerts.lean` | historical certificate framework |
| Historical hard-root admissibility program | admissibility theorems | `lean/Erdos647HardRootAdmissibility.lean` | supporting / historical |
| Barrier theorem | `barrier_statement_form` | `lean/Erdos647BarrierTheorem.lean` | supporting negative-result theorem |
| Historical b23 closure track | generic theorems | `lean/Erdos647B23Closure.lean` | supporting / historical |
| Bridge 3 legacy stub | legacy-disabled content | `lean/Bridge3.lean` | retired from active path |

## Computational artifacts

| Artifact | Location | Role |
|----------|----------|------|
| `survivors96` data | `data/survivors96.{json,csv}` | canonical 96-residue survivor set |
| Stage-1 open-set diagnostics | `docs/stage1_boundary.md` | current stop memo / frontier note |
| Conditional theorem note | `docs/conditional_finite_window.md` | scope note for the finite-window theorem |
| Historical atlas data | `data/closure_certificates_v2.json` and related scripts | legacy routing / negative-result record |
