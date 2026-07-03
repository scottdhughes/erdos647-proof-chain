import Erdos647TailKillTauFinitePrefixSemantic

/-!
# Open-residue table bridge for TailKill tau finite prefix

This module connects the active `openResiduesStage1` set to the 41-residue
table used by the distributed tau proof chunks.  It does not import production
chunks and does not prove the finite-prefix, eventual-u, local-layer,
shifted-prime, or global theorem surfaces.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Erdos647TailKillTauProofChunks
namespace FinitePrefixSemantic

def finitePrefixOpenResidues : Finset Nat :=
{
  0, 858, 1287, 1716, 2431, 2574, 4862, 5291, 6149, 8151, 9009, 9867, 10582,
  12155, 12584, 13013, 13442, 16302, 17017, 17160, 18733, 19877, 20306, 20735,
  21164, 24310, 24453, 25168, 27170, 28028, 28457, 29315, 29601, 31603, 32032,
  32461, 35321, 36608, 37752, 38896, 44187
}

theorem finitePrefixOpenResidues_card :
    finitePrefixOpenResidues.card = finitePrefixResidueCount := by
  decide

theorem finitePrefixOpenResidues_subset_stage1 :
    finitePrefixOpenResidues ⊆
      Erdos647ResiduePartitionStage1.openResiduesStage1 := by
  intro r h
  simp [finitePrefixOpenResidues] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]
  · subst r
    simp [
      Erdos647ResiduePartitionStage1.openResiduesStage1,
      Erdos647ResiduePartitionStage1.survivingResidues96,
      Erdos647ResiduePartitionStage1.closedResiduesStage1,
      Erdos647ResiduePartitionStage1.closedResidues55,
      Erdos647ResiduePartitionStage1.extraClosedResidues23_29,
      Erdos647SieveCertificate.survivingResidues,
      Erdos647SieveCertificate.M,
      Erdos647SieveCertificate.survives,
      Erdos647SieveCertificate.coeffs,
      Erdos647SieveCertificate.sievePrimes,
      Erdos647SingleOverlapClosure.singleOverlapResidues42,
      Erdos647SingleOverlapClosure.singleOverlapResidues40,
      Erdos647SingleOverlapClosure.residues26020,
      Erdos647SingleOverlapClosure.residues355311,
      Erdos647SingleOverlapClosure.residues4199_13,
      Erdos647SingleOverlapClosure.residues14535_45,
      Erdos647SingleOverlap_4199_13_draft.residues419913,
      Erdos647SingleOverlap_14535_45_draft.residues1453545,
      Erdos647DirectFullValueClosure.directFullValueResidues13,
      Erdos647DirectFullValueClosure.residues1729_7,
      Erdos647DirectFullValueClosure.residues2584_16,
      Erdos647DirectFullValueClosure.residues4522_14,
      Erdos647DirectFullValueClosure.residues4845_15,
      Erdos647DirectFullValueClosure.residues9690_30
    ]

theorem finitePrefixOpenResidues_eq_stage1 :
    finitePrefixOpenResidues =
      Erdos647ResiduePartitionStage1.openResiduesStage1 := by
  refine Finset.eq_of_subset_of_card_le finitePrefixOpenResidues_subset_stage1 ?_
  rw [Erdos647ResiduePartitionStage1.openResiduesStage1_card,
    finitePrefixOpenResidues_card]
  simp [finitePrefixResidueCount]

theorem residueIndex?_some_of_mem_finitePrefixOpenResidues {r : Nat}
    (h : r ∈ finitePrefixOpenResidues) :
    ∃ ri, ri < finitePrefixResidueCount ∧
      residueIndex? r = some ri ∧ openResidueAt ri = r := by
  simp [finitePrefixOpenResidues] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40
  · subst r
    exact ⟨0, by decide, rfl, rfl⟩
  · subst r
    exact ⟨1, by decide, rfl, rfl⟩
  · subst r
    exact ⟨2, by decide, rfl, rfl⟩
  · subst r
    exact ⟨3, by decide, rfl, rfl⟩
  · subst r
    exact ⟨4, by decide, rfl, rfl⟩
  · subst r
    exact ⟨5, by decide, rfl, rfl⟩
  · subst r
    exact ⟨6, by decide, rfl, rfl⟩
  · subst r
    exact ⟨7, by decide, rfl, rfl⟩
  · subst r
    exact ⟨8, by decide, rfl, rfl⟩
  · subst r
    exact ⟨9, by decide, rfl, rfl⟩
  · subst r
    exact ⟨10, by decide, rfl, rfl⟩
  · subst r
    exact ⟨11, by decide, rfl, rfl⟩
  · subst r
    exact ⟨12, by decide, rfl, rfl⟩
  · subst r
    exact ⟨13, by decide, rfl, rfl⟩
  · subst r
    exact ⟨14, by decide, rfl, rfl⟩
  · subst r
    exact ⟨15, by decide, rfl, rfl⟩
  · subst r
    exact ⟨16, by decide, rfl, rfl⟩
  · subst r
    exact ⟨17, by decide, rfl, rfl⟩
  · subst r
    exact ⟨18, by decide, rfl, rfl⟩
  · subst r
    exact ⟨19, by decide, rfl, rfl⟩
  · subst r
    exact ⟨20, by decide, rfl, rfl⟩
  · subst r
    exact ⟨21, by decide, rfl, rfl⟩
  · subst r
    exact ⟨22, by decide, rfl, rfl⟩
  · subst r
    exact ⟨23, by decide, rfl, rfl⟩
  · subst r
    exact ⟨24, by decide, rfl, rfl⟩
  · subst r
    exact ⟨25, by decide, rfl, rfl⟩
  · subst r
    exact ⟨26, by decide, rfl, rfl⟩
  · subst r
    exact ⟨27, by decide, rfl, rfl⟩
  · subst r
    exact ⟨28, by decide, rfl, rfl⟩
  · subst r
    exact ⟨29, by decide, rfl, rfl⟩
  · subst r
    exact ⟨30, by decide, rfl, rfl⟩
  · subst r
    exact ⟨31, by decide, rfl, rfl⟩
  · subst r
    exact ⟨32, by decide, rfl, rfl⟩
  · subst r
    exact ⟨33, by decide, rfl, rfl⟩
  · subst r
    exact ⟨34, by decide, rfl, rfl⟩
  · subst r
    exact ⟨35, by decide, rfl, rfl⟩
  · subst r
    exact ⟨36, by decide, rfl, rfl⟩
  · subst r
    exact ⟨37, by decide, rfl, rfl⟩
  · subst r
    exact ⟨38, by decide, rfl, rfl⟩
  · subst r
    exact ⟨39, by decide, rfl, rfl⟩
  · subst r
    exact ⟨40, by decide, rfl, rfl⟩

theorem residueIndex?_some_of_openResiduesStage1 {r : Nat}
    (h : r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1) :
    ∃ ri, ri < finitePrefixResidueCount ∧
      residueIndex? r = some ri ∧ openResidueAt ri = r := by
  apply residueIndex?_some_of_mem_finitePrefixOpenResidues
  simpa [finitePrefixOpenResidues_eq_stage1] using h

end FinitePrefixSemantic
end Erdos647TailKillTauProofChunks
