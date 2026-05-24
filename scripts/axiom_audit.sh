#!/bin/bash
# Axiom audit for the active Erdos647 Lean surface.
#
# Keep this script aligned with the Stage-1 proof path. Obsolete Bridge-3
# names such as hard_residues_no_solution and candidate_false_large_via_chain
# are intentionally absent from the active audit.
set -e

cd "$(dirname "$0")/../lean"

TMP="$(mktemp -t erdos647_axiom_audit.XXXXXX.lean)"
trap 'rm -f "$TMP"' EXIT

echo "=== Axiom audit for active Erdos647 Lean files ==="

run_module() {
  local module="$1"
  shift

  echo ""
  echo "=== $module ==="
  printf 'import %s\n' "$module" > "$TMP"
  for thm in "$@"; do
    printf '#print axioms %s\n' "$thm" >> "$TMP"
  done

  lake env lean "$TMP" 2>&1 || {
    echo "(build required first; run 'cd lean && lake build $module')"
    return 1
  }
}

run_module Erdos647SieveCertificate \
  Erdos647SieveCertificate.surviving_card \
  Erdos647SieveCertificate.no_forced_prime_killer

run_module Erdos647HardRootAdmissibility \
  Erdos647HardRootAdmissibility.hard_root_r_zero_admissible_all \
  Erdos647HardRootAdmissibility.hard_root_r_24310_admissible_all \
  Erdos647HardRootAdmissibility.numForbiddenAt_le_length \
  Erdos647HardRootAdmissibility.admissibleAt_large \
  Erdos647HardRootAdmissibility.hard_root_r_0_full_admissible_all \
  Erdos647HardRootAdmissibility.hard_root_r_1716_full_admissible_all \
  Erdos647HardRootAdmissibility.hard_root_r_4862_full_admissible_all \
  Erdos647HardRootAdmissibility.hard_root_r_16302_full_admissible_all \
  Erdos647HardRootAdmissibility.hard_root_r_17160_full_admissible_all \
  Erdos647HardRootAdmissibility.numForbiddenAtFull_le_length \
  Erdos647HardRootAdmissibility.admissibleAtFull_large

run_module Erdos647Closure92_Legacy \
  Erdos647Closure92.partition_counts \
  Erdos647Closure92.closed_hard_partition

run_module Erdos647BarrierTheorem \
  Erdos647BarrierTheorem.one_prime_escape \
  Erdos647BarrierTheorem.one_prime_escape_list \
  Erdos647BarrierTheorem.barrier_statement_form

run_module Erdos647BridgeV1 \
  Erdos647BridgeV1.erdos647_div_2520 \
  Erdos647BridgeV1.not_sq_2520N_sub_one \
  Erdos647BridgeV1.explicit_candidate_fails

run_module Bridge2 \
  Bridge2.bridge_isErdos647_to_sieve

run_module Erdos647SingleOverlapClosure \
  Erdos647SingleOverlapClosure.singleOverlapResidues42_card \
  Erdos647SingleOverlapClosure.no_erdos647_of_mem_singleOverlapResidues42

run_module Erdos647DirectFullValueClosure \
  Erdos647DirectFullValueClosure.directFullValueResidues13_card \
  Erdos647DirectFullValueClosure.no_erdos647_of_mem_directFullValueResidues13

run_module Erdos647ResiduePartitionStage1 \
  Erdos647ResiduePartitionStage1.survivingResidues96_card \
  Erdos647ResiduePartitionStage1.closedResiduesStage1_card \
  Erdos647ResiduePartitionStage1.openResiduesStage1_card \
  Erdos647ResiduePartitionStage1.surviving_eq_closed_union_open

run_module Erdos647ReductionChain \
  Erdos647ReductionChain.bridge_candidate_to_isErdos647 \
  Erdos647ReductionChain.bridge_isErdos647_to_sieve \
  Erdos647ReductionChain.candidate_false_large_conditional_on_openResiduesStage1 \
  Erdos647ReductionChain.candidate_false_large_conditional_on_openResiduesStage1_large \
  Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1 \
  Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1_large

run_module Erdos647Stage1Axiom \
  Erdos647Stage1Axiom.openResiduesStage1_no_solution \
  Erdos647Stage1Axiom.erdos647_with_stage1_axiom

run_module Erdos647ConditionalFiniteWindow \
  Erdos647ConditionalFiniteWindow.windowGood_of_primeCofactors \
  Erdos647ConditionalFiniteWindow.windowGood80_of_primeCofactors \
  Erdos647ConditionalFiniteWindow.residue_zero_mod_M_for_K20

run_module Erdos647Main \
  Erdos647Main.candidate_false_finite

if [[ -f Erdos647ShiftedPrimeChannel.lean ]]; then
  run_module Erdos647ShiftedPrimeChannel \
    Erdos647ShiftedPrimeChannel.F1_mod_eight \
    Erdos647ShiftedPrimeChannel.F1_prime_of_isErdos647 \
    Erdos647ShiftedPrimeChannel.large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPCloses
fi
