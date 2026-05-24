import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Erdos647SieveCertificate

/-!
# Partition of the 96 surviving residues into closure types

After the verified reduction (12-shape package + 96-residue sieve), the
session showed via recursive caveat refactorization that:

  * **92 residues** mod 46189 fully close via root + level-1 caveat
    refactorization (every caveat pattern is killed).
  * **2 residues** (r = 2574 and r = 24453) close via level-2
    caveat refactorization (q = 17 forced divisibility on a transformed
    primitive form on a specific sub-branch).
  * **2 residues** (r = 0 and r = 24310) resist all elementary methods;
    these are the two "hard" residues sharing the structural property
    `11 · 13 · 17 ∣ r` (and additionally `19 ∣ r` for `r = 0`).

This file Lean-checks (via `native_decide`) the partition:

  92 + 2 + 2 = 96

and that the 96-residue list of `Erdos647SieveCertificate` decomposes
exactly into these three classes. The mathematical content of "closure
by recursive refactorization" is not formalized here (it is the
multi-thousand-line computational result of the session); this file
records only the **partition** as a Lean-checked fact.
-/

namespace Erdos647Closure92

open Erdos647SieveCertificate

/-- The 4 hard residues mod 46189 that resist elementary recursive
    refactorization. The two truly hard residues {0, 24310} satisfy
    `11·13·17 ∣ r`; the level-2 residues {2574, 24453} satisfy
    `11·13 ∣ r` but not `17 ∣ r`. -/
def hardResidues : Finset ℕ := {0, 2574, 24310, 24453}

/-- The 2 residues that close via second-level caveat refactorization
    (i.e., not at root + level-1, but resolvable at level-2). -/
def levelTwoResidues : Finset ℕ := {2574, 24453}

/-- The 2 truly residual residues (resist all elementary methods). -/
def trulyHardResidues : Finset ℕ := {0, 24310}

/-- The 92 residues closable by root + level-1 caveat refactorization. -/
def fullyClosedResidues : Finset ℕ :=
  survivingResidues \ hardResidues

/-- **Partition count theorem.** The 96-residue survivor set decomposes
    as: 92 fully closed + 2 level-2 closable + 2 truly hard. -/
theorem partition_counts :
    fullyClosedResidues.card = 92 ∧
    levelTwoResidues.card = 2 ∧
    trulyHardResidues.card = 2 ∧
    survivingResidues.card = 96 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Disjoint union.** The level-2 and truly-hard residues partition
    the 4 hard residues (no overlap, complete cover). -/
theorem hard_partition :
    levelTwoResidues ∪ trulyHardResidues = hardResidues ∧
    levelTwoResidues ∩ trulyHardResidues = ∅ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Cover.** The fully-closed and hard residues partition all 96
    surviving residues. -/
theorem closed_hard_partition :
    fullyClosedResidues ∪ hardResidues = survivingResidues ∧
    fullyClosedResidues ∩ hardResidues = ∅ := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **Structural property of hard residues.** Every truly-hard residue
    is divisible by `11·13·17 = 2431`. -/
theorem hard_residues_divisible_by_2431 :
    ∀ r ∈ trulyHardResidues, 2431 ∣ r := by
  decide

/-- **Structural property: `11·13` divides every level-2 residue too.** -/
theorem level2_residues_divisible_by_143 :
    ∀ r ∈ levelTwoResidues, 143 ∣ r := by
  decide

/-- **r = 0 has the strongest divisibility:** `46189 = 11·13·17·19 ∣ 0`,
    trivially. This is the "deep zero" structural property that makes
    `r = 0` the most resistant under all elementary methods. -/
theorem r_zero_div_46189 : 46189 ∣ (0 : ℕ) := by decide

/-- **r = 24310 = 2·5·11·13·17.** Not divisible by `19`. -/
theorem r_24310_factorization : 24310 = 2 * 5 * 11 * 13 * 17 := by decide

end Erdos647Closure92
