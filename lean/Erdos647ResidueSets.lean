import Mathlib

/-!
# Shared residue-set literals for the current exact-v2 ledger

This file exists to avoid cycles between the reduction-chain statements
and generated closure/branch files.
-/

namespace Erdos647ResidueSets

/-- The 5 structurally hard residues from the historical 91/5 split. -/
def hardResidues5 : Finset ℕ := {0, 1716, 4862, 16302, 17160}

/-- Nine additional residues reopened by the exact-v2 promotion audit. -/
def reopenedResidues9 : Finset ℕ :=
  {2431, 9009, 9867, 17017, 21164, 24453, 29315, 31603, 38896}

/-- Current unresolved 14-residue ledger surface under exact-v2 semantics. -/
def openResidues14Literal : Finset ℕ :=
  {0, 1716, 2431, 4862, 9009, 9867, 16302, 17017, 17160,
   21164, 24453, 29315, 31603, 38896}

end Erdos647ResidueSets
