import Erdos647ReductionChain
import Erdos647ResiduePartitionStage1

/-!
# Stage-1 open-residue axiom wrapper

The proof-critical theorem is the conditional reduction in
`Erdos647ReductionChain`. This file contains the single intentional
Stage-1 axiom used to wrap that conditional theorem.
-/

namespace Erdos647Stage1Axiom

open Erdos647Main
open Erdos647ReductionChain
open Erdos647ResiduePartitionStage1
open Erdos647SieveCertificate
open Erdos647BridgeV1

axiom openResiduesStage1_no_solution :
    ∀ N, N % M ∈ openResiduesStage1 → ¬ IsErdos647 (2520 * N)

theorem erdos647_with_stage1_axiom :
    ∀ n, 24 < n → ¬ Candidate n :=
  erdos647_conditional_on_openResiduesStage1 openResiduesStage1_no_solution

end Erdos647Stage1Axiom
