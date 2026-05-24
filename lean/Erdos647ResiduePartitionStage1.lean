import Mathlib
import Erdos647SieveCertificate
import Erdos647ResidueSets
import Erdos647SingleOverlapClosure
import Erdos647DirectFullValueClosure

/-!
# Stage-1 residue partition

Proof-critical sets are defined from theorem-grade closures only.

The Stage-1 formal core closes:

* `42` single-overlap closures
* `13` direct full-value closures
* `41` open residues, defined as the complement inside the `96` sieve
  survivors

The diagnostic decomposition of the open set is:

* `27` non-`ble1` residues
* `14` historically hard residues
-/

namespace Erdos647ResiduePartitionStage1

open Erdos647SieveCertificate
open Erdos647SingleOverlapClosure
open Erdos647DirectFullValueClosure

/-- Alias for the theorem-grade 96-residue sieve frontier. -/
def survivingResidues96 : Finset ℕ := Erdos647SieveCertificate.survivingResidues

/-- The theorem-grade closed residues already formalized in Stage 1A. -/
def closedResidues55 : Finset ℕ :=
  singleOverlapResidues42 ∪ directFullValueResidues13

/-- Placeholder for any post-green `23/29` promotions. Empty in Stage 1A. -/
def extraClosedResidues23_29 : Finset ℕ := ∅

/-- The proof-critical Stage-1 closed set. -/
def closedResiduesStage1 : Finset ℕ :=
  closedResidues55 ∪ extraClosedResidues23_29

/-- The proof-critical Stage-1 open set, defined by complement. -/
def openResiduesStage1 : Finset ℕ :=
  survivingResidues96 \ closedResiduesStage1

/-- Historical 14-residue hard bucket, retained as a diagnostic subset. -/
def openResiduesGenuineHard14 : Finset ℕ :=
  Erdos647ResidueSets.openResidues14Literal

/-- The remaining diagnostic bucket: open and non-hard. -/
def openResiduesNonBle1Stage1 : Finset ℕ :=
  openResiduesStage1 \ openResiduesGenuineHard14

theorem survivingResidues96_card : survivingResidues96.card = 96 := by
  simpa [survivingResidues96] using Erdos647SieveCertificate.surviving_card

theorem singleOverlap_direct_disjoint :
    Disjoint singleOverlapResidues42 directFullValueResidues13 := by
  native_decide

theorem closedResidues55_card : closedResidues55.card = 55 := by
  native_decide

theorem closedResiduesStage1_eq_closedResidues55 :
    closedResiduesStage1 = closedResidues55 := by
  simp [closedResiduesStage1, extraClosedResidues23_29]

theorem closedResiduesStage1_card : closedResiduesStage1.card = 55 := by
  simpa [closedResiduesStage1_eq_closedResidues55] using closedResidues55_card

theorem openResiduesGenuineHard14_card :
    openResiduesGenuineHard14.card = 14 := by
  native_decide

theorem openResiduesStage1_card : openResiduesStage1.card = 41 := by
  native_decide

theorem openResiduesNonBle1Stage1_card :
    openResiduesNonBle1Stage1.card = 27 := by
  native_decide

theorem closed_plus_open_card :
    closedResiduesStage1.card + openResiduesStage1.card = 96 := by
  rw [closedResiduesStage1_card, openResiduesStage1_card]

theorem closedResiduesStage1_subset_surviving :
    closedResiduesStage1 ⊆ survivingResidues96 := by
  native_decide

theorem openResiduesStage1_subset_surviving :
    openResiduesStage1 ⊆ survivingResidues96 := by
  native_decide

theorem closed_open_disjoint :
    Disjoint closedResiduesStage1 openResiduesStage1 := by
  native_decide

theorem surviving_eq_closed_union_open :
    survivingResidues96 = closedResiduesStage1 ∪ openResiduesStage1 := by
  native_decide

theorem mem_closedResiduesStage1_iff {r : ℕ} :
    r ∈ closedResiduesStage1 ↔
      r ∈ singleOverlapResidues42 ∨ r ∈ directFullValueResidues13 := by
  simp [closedResiduesStage1, closedResidues55, extraClosedResidues23_29]

theorem mem_openResiduesStage1_of_mem_surviving_not_mem_closed {r : ℕ}
    (hs : r ∈ survivingResidues96) (hc : r ∉ closedResiduesStage1) :
    r ∈ openResiduesStage1 := by
  simp [openResiduesStage1, hs, hc]

theorem open_nonBle1_disjoint_hard :
    Disjoint openResiduesNonBle1Stage1 openResiduesGenuineHard14 := by
  native_decide

theorem openResiduesStage1_eq_diagnostic_union :
    openResiduesStage1 =
      openResiduesNonBle1Stage1 ∪ openResiduesGenuineHard14 := by
  native_decide

end Erdos647ResiduePartitionStage1
