import Erdos647TailKillTauOpenResidueBridge
import Erdos647TailKillTauFinitePrefixGroup00
import Erdos647TailKillTauFinitePrefixGroup01
import Erdos647TailKillTauFinitePrefixGroup02
import Erdos647TailKillTauFinitePrefixGroup03
import Erdos647TailKillTauFinitePrefixGroup04
import Erdos647TailKillTauFinitePrefixGroup05
import Erdos647TailKillTauFinitePrefixGroup06
import Erdos647TailKillTauFinitePrefixGroup07
import Erdos647TailKillTauFinitePrefixGroup08
import Erdos647TailKillTauFinitePrefixGroup09
import Erdos647TailKillTauFinitePrefixGroup10
import Erdos647TailKillTauFinitePrefixGroup11
import Erdos647TailKillTauFinitePrefixGroup12
import Erdos647TailKillTauFinitePrefixGroup13
import Erdos647TailKillTauFinitePrefixGroup14
import Erdos647TailKillTauFinitePrefixGroup15
import Erdos647TailKillTauFinitePrefixGroup16
import Erdos647TailKillTauFinitePrefixGroup17
import Erdos647TailKillTauFinitePrefixGroup18
import Erdos647TailKillTauFinitePrefixGroup19
import Erdos647TailKillTauFinitePrefixGroup20
import Erdos647TailKillTauFinitePrefixGroup21

/-!
# TailKill tau finite-prefix semantic interface

This module composes the distributed tau proof chunks into the existing
`FinitePrefixMechanismVerifiedBy` interface for the finite prefix `u < 101`.

Certified scope only:
* the 2,190,589 finite-domain triples from 41 open residues, `s < 529`,
  and `u < 101`;
* `K := fun _ _ _ => 10`;
* the finite-prefix mechanism interface.

It intentionally does not prove or claim an eventual-u theorem, local-layer
theorem, shifted-prime theorem, global theorem, global `K`, mechanism-cover
closure, or removal of existing assumptions.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Erdos647TailKillTauProofChunks
namespace FinitePrefixMechanism

open FinitePrefixSemantic
open FinitePrefixChunkInterfaces
open Erdos647ShiftedPrimeChannel

def TailKillTauFinitePrefixCertificateAt (idx : Nat) : Prop :=
  ∃ row : CertRow,
    RowValid row ∧
      rowMatchesGlobalIndex row idx = true ∧
        (row.tag = 2 -> row.k ≤ finitePrefixWitnessBound)

theorem globalIndexOfResidueIndex_lt
    {ri s u : Nat}
    (hri : ri < finitePrefixResidueCount)
    (hs : s < finitePrefixSCount)
    (hu : u < finitePrefixUCount) :
    globalIndexOfResidueIndex ri s u < finitePrefixDomainSize := by
  simp [globalIndexOfResidueIndex, finitePrefixResidueCount, finitePrefixSCount,
    finitePrefixUCount, finitePrefixDomainSize] at hri hs hu ⊢
  omega

theorem expectedResidueIndexOfGlobal_globalIndex
    {ri s u : Nat}
    (_hri : ri < finitePrefixResidueCount)
    (hs : s < finitePrefixSCount)
    (hu : u < finitePrefixUCount) :
    expectedResidueIndexOfGlobal (globalIndexOfResidueIndex ri s u) = ri := by
  have hrem : s * finitePrefixUCount + u <
      finitePrefixSCount * finitePrefixUCount := by
    simp [finitePrefixSCount, finitePrefixUCount] at hs hu ⊢
    omega
  have hblock_pos : 0 < finitePrefixSCount * finitePrefixUCount := by
    simp [finitePrefixSCount, finitePrefixUCount]
  unfold expectedResidueIndexOfGlobal globalIndexOfResidueIndex
  rw [show ri * (finitePrefixSCount * finitePrefixUCount) +
        s * finitePrefixUCount + u =
      ri * (finitePrefixSCount * finitePrefixUCount) +
        (s * finitePrefixUCount + u) by omega]
  rw [Nat.mul_comm ri (finitePrefixSCount * finitePrefixUCount)]
  rw [Nat.mul_add_div hblock_pos]
  rw [Nat.div_eq_of_lt hrem]
  omega

theorem expectedSOfGlobal_globalIndex
    {ri s u : Nat}
    (_hri : ri < finitePrefixResidueCount)
    (hs : s < finitePrefixSCount)
    (hu : u < finitePrefixUCount) :
    expectedSOfGlobal (globalIndexOfResidueIndex ri s u) = s := by
  have hrem : s * finitePrefixUCount + u <
      finitePrefixSCount * finitePrefixUCount := by
    simp [finitePrefixSCount, finitePrefixUCount] at hs hu ⊢
    omega
  have hu_mod : u < finitePrefixUCount := hu
  have hu_pos : 0 < finitePrefixUCount := by
    simp [finitePrefixUCount]
  unfold expectedSOfGlobal globalIndexOfResidueIndex
  rw [show ri * (finitePrefixSCount * finitePrefixUCount) +
        s * finitePrefixUCount + u =
      ri * (finitePrefixSCount * finitePrefixUCount) +
        (s * finitePrefixUCount + u) by omega]
  rw [Nat.mul_comm ri (finitePrefixSCount * finitePrefixUCount)]
  rw [Nat.mul_add_mod]
  rw [Nat.mod_eq_of_lt hrem]
  rw [Nat.mul_comm s finitePrefixUCount]
  rw [Nat.mul_add_div hu_pos]
  rw [Nat.div_eq_of_lt hu_mod]
  omega

theorem expectedUOfGlobal_globalIndex
    {ri s u : Nat}
    (_hri : ri < finitePrefixResidueCount)
    (_hs : s < finitePrefixSCount)
    (hu : u < finitePrefixUCount) :
    expectedUOfGlobal (globalIndexOfResidueIndex ri s u) = u := by
  unfold expectedUOfGlobal globalIndexOfResidueIndex
  rw [show ri * (finitePrefixSCount * finitePrefixUCount) + s * finitePrefixUCount + u =
      (finitePrefixSCount * ri + s) * finitePrefixUCount + u by ring]
  rw [Nat.mul_comm (finitePrefixSCount * ri + s) finitePrefixUCount]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hu

theorem openResiduesStage1_subset_finitePrefixOpenResidues :
    Erdos647ResiduePartitionStage1.openResiduesStage1 ⊆ finitePrefixOpenResidues := by
  decide

theorem residueIndex?_some_of_openResiduesStage1_no_native {r : Nat}
    (h : r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1) :
    ∃ ri, ri < finitePrefixResidueCount ∧
      residueIndex? r = some ri ∧ openResidueAt ri = r :=
  residueIndex?_some_of_mem_finitePrefixOpenResidues
    (openResiduesStage1_subset_finitePrefixOpenResidues h)


theorem tailKillTauChunk0000_certificate_at
    (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 10000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 0
  have hlen : tailKillTauChunk0000Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0000Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0000Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0000_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0000_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0000Start + off = idx := by
      dsimp [off]
      change 0 + (idx - 0) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0000_witness_bound_at off hoff htag


theorem tailKillTauChunk0001_certificate_at
    (idx : Nat) (hlo : 10000 ≤ idx) (hhi : idx < 20000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 10000
  have hlen : tailKillTauChunk0001Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0001Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0001Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0001_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0001_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0001Start + off = idx := by
      dsimp [off]
      change 10000 + (idx - 10000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0001_witness_bound_at off hoff htag


theorem tailKillTauChunk0002_certificate_at
    (idx : Nat) (hlo : 20000 ≤ idx) (hhi : idx < 30000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 20000
  have hlen : tailKillTauChunk0002Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0002Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0002Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0002_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0002_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0002Start + off = idx := by
      dsimp [off]
      change 20000 + (idx - 20000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0002_witness_bound_at off hoff htag


theorem tailKillTauChunk0003_certificate_at
    (idx : Nat) (hlo : 30000 ≤ idx) (hhi : idx < 40000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 30000
  have hlen : tailKillTauChunk0003Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0003Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0003Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0003_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0003_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0003Start + off = idx := by
      dsimp [off]
      change 30000 + (idx - 30000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0003_witness_bound_at off hoff htag


theorem tailKillTauChunk0004_certificate_at
    (idx : Nat) (hlo : 40000 ≤ idx) (hhi : idx < 50000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 40000
  have hlen : tailKillTauChunk0004Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0004Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0004Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0004_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0004_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0004Start + off = idx := by
      dsimp [off]
      change 40000 + (idx - 40000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0004_witness_bound_at off hoff htag


theorem tailKillTauChunk0005_certificate_at
    (idx : Nat) (hlo : 50000 ≤ idx) (hhi : idx < 60000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 50000
  have hlen : tailKillTauChunk0005Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0005Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0005Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0005_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0005_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0005Start + off = idx := by
      dsimp [off]
      change 50000 + (idx - 50000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0005_witness_bound_at off hoff htag


theorem tailKillTauChunk0006_certificate_at
    (idx : Nat) (hlo : 60000 ≤ idx) (hhi : idx < 70000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 60000
  have hlen : tailKillTauChunk0006Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0006Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0006Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0006_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0006_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0006Start + off = idx := by
      dsimp [off]
      change 60000 + (idx - 60000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0006_witness_bound_at off hoff htag


theorem tailKillTauChunk0007_certificate_at
    (idx : Nat) (hlo : 70000 ≤ idx) (hhi : idx < 80000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 70000
  have hlen : tailKillTauChunk0007Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0007Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0007Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0007_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0007_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0007Start + off = idx := by
      dsimp [off]
      change 70000 + (idx - 70000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0007_witness_bound_at off hoff htag


theorem tailKillTauChunk0008_certificate_at
    (idx : Nat) (hlo : 80000 ≤ idx) (hhi : idx < 90000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 80000
  have hlen : tailKillTauChunk0008Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0008Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0008Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0008_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0008_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0008Start + off = idx := by
      dsimp [off]
      change 80000 + (idx - 80000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0008_witness_bound_at off hoff htag


theorem tailKillTauChunk0009_certificate_at
    (idx : Nat) (hlo : 90000 ≤ idx) (hhi : idx < 100000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 90000
  have hlen : tailKillTauChunk0009Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0009Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0009Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0009_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0009_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0009Start + off = idx := by
      dsimp [off]
      change 90000 + (idx - 90000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0009_witness_bound_at off hoff htag


theorem tailKillTauChunk0010_certificate_at
    (idx : Nat) (hlo : 100000 ≤ idx) (hhi : idx < 110000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 100000
  have hlen : tailKillTauChunk0010Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0010Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0010Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0010_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0010_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0010Start + off = idx := by
      dsimp [off]
      change 100000 + (idx - 100000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0010_witness_bound_at off hoff htag


theorem tailKillTauChunk0011_certificate_at
    (idx : Nat) (hlo : 110000 ≤ idx) (hhi : idx < 120000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 110000
  have hlen : tailKillTauChunk0011Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0011Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0011Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0011_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0011_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0011Start + off = idx := by
      dsimp [off]
      change 110000 + (idx - 110000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0011_witness_bound_at off hoff htag


theorem tailKillTauChunk0012_certificate_at
    (idx : Nat) (hlo : 120000 ≤ idx) (hhi : idx < 130000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 120000
  have hlen : tailKillTauChunk0012Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0012Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0012Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0012_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0012_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0012Start + off = idx := by
      dsimp [off]
      change 120000 + (idx - 120000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0012_witness_bound_at off hoff htag


theorem tailKillTauChunk0013_certificate_at
    (idx : Nat) (hlo : 130000 ≤ idx) (hhi : idx < 140000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 130000
  have hlen : tailKillTauChunk0013Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0013Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0013Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0013_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0013_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0013Start + off = idx := by
      dsimp [off]
      change 130000 + (idx - 130000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0013_witness_bound_at off hoff htag


theorem tailKillTauChunk0014_certificate_at
    (idx : Nat) (hlo : 140000 ≤ idx) (hhi : idx < 150000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 140000
  have hlen : tailKillTauChunk0014Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0014Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0014Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0014_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0014_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0014Start + off = idx := by
      dsimp [off]
      change 140000 + (idx - 140000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0014_witness_bound_at off hoff htag


theorem tailKillTauChunk0015_certificate_at
    (idx : Nat) (hlo : 150000 ≤ idx) (hhi : idx < 160000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 150000
  have hlen : tailKillTauChunk0015Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0015Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0015Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0015_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0015_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0015Start + off = idx := by
      dsimp [off]
      change 150000 + (idx - 150000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0015_witness_bound_at off hoff htag


theorem tailKillTauChunk0016_certificate_at
    (idx : Nat) (hlo : 160000 ≤ idx) (hhi : idx < 170000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 160000
  have hlen : tailKillTauChunk0016Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0016Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0016Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0016_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0016_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0016Start + off = idx := by
      dsimp [off]
      change 160000 + (idx - 160000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0016_witness_bound_at off hoff htag


theorem tailKillTauChunk0017_certificate_at
    (idx : Nat) (hlo : 170000 ≤ idx) (hhi : idx < 180000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 170000
  have hlen : tailKillTauChunk0017Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0017Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0017Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0017_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0017_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0017Start + off = idx := by
      dsimp [off]
      change 170000 + (idx - 170000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0017_witness_bound_at off hoff htag


theorem tailKillTauChunk0018_certificate_at
    (idx : Nat) (hlo : 180000 ≤ idx) (hhi : idx < 190000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 180000
  have hlen : tailKillTauChunk0018Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0018Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0018Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0018_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0018_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0018Start + off = idx := by
      dsimp [off]
      change 180000 + (idx - 180000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0018_witness_bound_at off hoff htag


theorem tailKillTauChunk0019_certificate_at
    (idx : Nat) (hlo : 190000 ≤ idx) (hhi : idx < 200000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 190000
  have hlen : tailKillTauChunk0019Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0019Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0019Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0019_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0019_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0019Start + off = idx := by
      dsimp [off]
      change 190000 + (idx - 190000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0019_witness_bound_at off hoff htag


theorem tailKillTauChunk0020_certificate_at
    (idx : Nat) (hlo : 200000 ≤ idx) (hhi : idx < 210000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 200000
  have hlen : tailKillTauChunk0020Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0020Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0020Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0020_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0020_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0020Start + off = idx := by
      dsimp [off]
      change 200000 + (idx - 200000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0020_witness_bound_at off hoff htag


theorem tailKillTauChunk0021_certificate_at
    (idx : Nat) (hlo : 210000 ≤ idx) (hhi : idx < 220000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 210000
  have hlen : tailKillTauChunk0021Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0021Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0021Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0021_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0021_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0021Start + off = idx := by
      dsimp [off]
      change 210000 + (idx - 210000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0021_witness_bound_at off hoff htag


theorem tailKillTauChunk0022_certificate_at
    (idx : Nat) (hlo : 220000 ≤ idx) (hhi : idx < 230000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 220000
  have hlen : tailKillTauChunk0022Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0022Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0022Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0022_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0022_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0022Start + off = idx := by
      dsimp [off]
      change 220000 + (idx - 220000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0022_witness_bound_at off hoff htag


theorem tailKillTauChunk0023_certificate_at
    (idx : Nat) (hlo : 230000 ≤ idx) (hhi : idx < 240000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 230000
  have hlen : tailKillTauChunk0023Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0023Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0023Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0023_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0023_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0023Start + off = idx := by
      dsimp [off]
      change 230000 + (idx - 230000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0023_witness_bound_at off hoff htag


theorem tailKillTauChunk0024_certificate_at
    (idx : Nat) (hlo : 240000 ≤ idx) (hhi : idx < 250000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 240000
  have hlen : tailKillTauChunk0024Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0024Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0024Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0024_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0024_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0024Start + off = idx := by
      dsimp [off]
      change 240000 + (idx - 240000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0024_witness_bound_at off hoff htag


theorem tailKillTauChunk0025_certificate_at
    (idx : Nat) (hlo : 250000 ≤ idx) (hhi : idx < 260000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 250000
  have hlen : tailKillTauChunk0025Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0025Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0025Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0025_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0025_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0025Start + off = idx := by
      dsimp [off]
      change 250000 + (idx - 250000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0025_witness_bound_at off hoff htag


theorem tailKillTauChunk0026_certificate_at
    (idx : Nat) (hlo : 260000 ≤ idx) (hhi : idx < 270000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 260000
  have hlen : tailKillTauChunk0026Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0026Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0026Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0026_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0026_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0026Start + off = idx := by
      dsimp [off]
      change 260000 + (idx - 260000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0026_witness_bound_at off hoff htag


theorem tailKillTauChunk0027_certificate_at
    (idx : Nat) (hlo : 270000 ≤ idx) (hhi : idx < 280000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 270000
  have hlen : tailKillTauChunk0027Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0027Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0027Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0027_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0027_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0027Start + off = idx := by
      dsimp [off]
      change 270000 + (idx - 270000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0027_witness_bound_at off hoff htag


theorem tailKillTauChunk0028_certificate_at
    (idx : Nat) (hlo : 280000 ≤ idx) (hhi : idx < 290000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 280000
  have hlen : tailKillTauChunk0028Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0028Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0028Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0028_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0028_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0028Start + off = idx := by
      dsimp [off]
      change 280000 + (idx - 280000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0028_witness_bound_at off hoff htag


theorem tailKillTauChunk0029_certificate_at
    (idx : Nat) (hlo : 290000 ≤ idx) (hhi : idx < 300000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 290000
  have hlen : tailKillTauChunk0029Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0029Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0029Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0029_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0029_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0029Start + off = idx := by
      dsimp [off]
      change 290000 + (idx - 290000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0029_witness_bound_at off hoff htag


theorem tailKillTauChunk0030_certificate_at
    (idx : Nat) (hlo : 300000 ≤ idx) (hhi : idx < 310000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 300000
  have hlen : tailKillTauChunk0030Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0030Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0030Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0030_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0030_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0030Start + off = idx := by
      dsimp [off]
      change 300000 + (idx - 300000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0030_witness_bound_at off hoff htag


theorem tailKillTauChunk0031_certificate_at
    (idx : Nat) (hlo : 310000 ≤ idx) (hhi : idx < 320000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 310000
  have hlen : tailKillTauChunk0031Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0031Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0031Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0031_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0031_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0031Start + off = idx := by
      dsimp [off]
      change 310000 + (idx - 310000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0031_witness_bound_at off hoff htag


theorem tailKillTauChunk0032_certificate_at
    (idx : Nat) (hlo : 320000 ≤ idx) (hhi : idx < 330000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 320000
  have hlen : tailKillTauChunk0032Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0032Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0032Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0032_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0032_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0032Start + off = idx := by
      dsimp [off]
      change 320000 + (idx - 320000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0032_witness_bound_at off hoff htag


theorem tailKillTauChunk0033_certificate_at
    (idx : Nat) (hlo : 330000 ≤ idx) (hhi : idx < 340000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 330000
  have hlen : tailKillTauChunk0033Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0033Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0033Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0033_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0033_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0033Start + off = idx := by
      dsimp [off]
      change 330000 + (idx - 330000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0033_witness_bound_at off hoff htag


theorem tailKillTauChunk0034_certificate_at
    (idx : Nat) (hlo : 340000 ≤ idx) (hhi : idx < 350000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 340000
  have hlen : tailKillTauChunk0034Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0034Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0034Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0034_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0034_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0034Start + off = idx := by
      dsimp [off]
      change 340000 + (idx - 340000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0034_witness_bound_at off hoff htag


theorem tailKillTauChunk0035_certificate_at
    (idx : Nat) (hlo : 350000 ≤ idx) (hhi : idx < 360000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 350000
  have hlen : tailKillTauChunk0035Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0035Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0035Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0035_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0035_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0035Start + off = idx := by
      dsimp [off]
      change 350000 + (idx - 350000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0035_witness_bound_at off hoff htag


theorem tailKillTauChunk0036_certificate_at
    (idx : Nat) (hlo : 360000 ≤ idx) (hhi : idx < 370000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 360000
  have hlen : tailKillTauChunk0036Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0036Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0036Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0036_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0036_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0036Start + off = idx := by
      dsimp [off]
      change 360000 + (idx - 360000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0036_witness_bound_at off hoff htag


theorem tailKillTauChunk0037_certificate_at
    (idx : Nat) (hlo : 370000 ≤ idx) (hhi : idx < 380000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 370000
  have hlen : tailKillTauChunk0037Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0037Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0037Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0037_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0037_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0037Start + off = idx := by
      dsimp [off]
      change 370000 + (idx - 370000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0037_witness_bound_at off hoff htag


theorem tailKillTauChunk0038_certificate_at
    (idx : Nat) (hlo : 380000 ≤ idx) (hhi : idx < 390000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 380000
  have hlen : tailKillTauChunk0038Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0038Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0038Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0038_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0038_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0038Start + off = idx := by
      dsimp [off]
      change 380000 + (idx - 380000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0038_witness_bound_at off hoff htag


theorem tailKillTauChunk0039_certificate_at
    (idx : Nat) (hlo : 390000 ≤ idx) (hhi : idx < 400000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 390000
  have hlen : tailKillTauChunk0039Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0039Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0039Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0039_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0039_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0039Start + off = idx := by
      dsimp [off]
      change 390000 + (idx - 390000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0039_witness_bound_at off hoff htag


theorem tailKillTauChunk0040_certificate_at
    (idx : Nat) (hlo : 400000 ≤ idx) (hhi : idx < 410000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 400000
  have hlen : tailKillTauChunk0040Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0040Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0040Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0040_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0040_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0040Start + off = idx := by
      dsimp [off]
      change 400000 + (idx - 400000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0040_witness_bound_at off hoff htag


theorem tailKillTauChunk0041_certificate_at
    (idx : Nat) (hlo : 410000 ≤ idx) (hhi : idx < 420000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 410000
  have hlen : tailKillTauChunk0041Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0041Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0041Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0041_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0041_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0041Start + off = idx := by
      dsimp [off]
      change 410000 + (idx - 410000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0041_witness_bound_at off hoff htag


theorem tailKillTauChunk0042_certificate_at
    (idx : Nat) (hlo : 420000 ≤ idx) (hhi : idx < 430000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 420000
  have hlen : tailKillTauChunk0042Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0042Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0042Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0042_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0042_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0042Start + off = idx := by
      dsimp [off]
      change 420000 + (idx - 420000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0042_witness_bound_at off hoff htag


theorem tailKillTauChunk0043_certificate_at
    (idx : Nat) (hlo : 430000 ≤ idx) (hhi : idx < 440000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 430000
  have hlen : tailKillTauChunk0043Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0043Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0043Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0043_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0043_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0043Start + off = idx := by
      dsimp [off]
      change 430000 + (idx - 430000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0043_witness_bound_at off hoff htag


theorem tailKillTauChunk0044_certificate_at
    (idx : Nat) (hlo : 440000 ≤ idx) (hhi : idx < 450000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 440000
  have hlen : tailKillTauChunk0044Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0044Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0044Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0044_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0044_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0044Start + off = idx := by
      dsimp [off]
      change 440000 + (idx - 440000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0044_witness_bound_at off hoff htag


theorem tailKillTauChunk0045_certificate_at
    (idx : Nat) (hlo : 450000 ≤ idx) (hhi : idx < 460000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 450000
  have hlen : tailKillTauChunk0045Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0045Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0045Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0045_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0045_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0045Start + off = idx := by
      dsimp [off]
      change 450000 + (idx - 450000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0045_witness_bound_at off hoff htag


theorem tailKillTauChunk0046_certificate_at
    (idx : Nat) (hlo : 460000 ≤ idx) (hhi : idx < 470000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 460000
  have hlen : tailKillTauChunk0046Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0046Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0046Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0046_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0046_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0046Start + off = idx := by
      dsimp [off]
      change 460000 + (idx - 460000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0046_witness_bound_at off hoff htag


theorem tailKillTauChunk0047_certificate_at
    (idx : Nat) (hlo : 470000 ≤ idx) (hhi : idx < 480000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 470000
  have hlen : tailKillTauChunk0047Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0047Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0047Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0047_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0047_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0047Start + off = idx := by
      dsimp [off]
      change 470000 + (idx - 470000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0047_witness_bound_at off hoff htag


theorem tailKillTauChunk0048_certificate_at
    (idx : Nat) (hlo : 480000 ≤ idx) (hhi : idx < 490000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 480000
  have hlen : tailKillTauChunk0048Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0048Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0048Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0048_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0048_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0048Start + off = idx := by
      dsimp [off]
      change 480000 + (idx - 480000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0048_witness_bound_at off hoff htag


theorem tailKillTauChunk0049_certificate_at
    (idx : Nat) (hlo : 490000 ≤ idx) (hhi : idx < 500000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 490000
  have hlen : tailKillTauChunk0049Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0049Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0049Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0049_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0049_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0049Start + off = idx := by
      dsimp [off]
      change 490000 + (idx - 490000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0049_witness_bound_at off hoff htag


theorem tailKillTauChunk0050_certificate_at
    (idx : Nat) (hlo : 500000 ≤ idx) (hhi : idx < 510000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 500000
  have hlen : tailKillTauChunk0050Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0050Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0050Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0050_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0050_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0050Start + off = idx := by
      dsimp [off]
      change 500000 + (idx - 500000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0050_witness_bound_at off hoff htag


theorem tailKillTauChunk0051_certificate_at
    (idx : Nat) (hlo : 510000 ≤ idx) (hhi : idx < 520000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 510000
  have hlen : tailKillTauChunk0051Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0051Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0051Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0051_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0051_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0051Start + off = idx := by
      dsimp [off]
      change 510000 + (idx - 510000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0051_witness_bound_at off hoff htag


theorem tailKillTauChunk0052_certificate_at
    (idx : Nat) (hlo : 520000 ≤ idx) (hhi : idx < 530000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 520000
  have hlen : tailKillTauChunk0052Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0052Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0052Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0052_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0052_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0052Start + off = idx := by
      dsimp [off]
      change 520000 + (idx - 520000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0052_witness_bound_at off hoff htag


theorem tailKillTauChunk0053_certificate_at
    (idx : Nat) (hlo : 530000 ≤ idx) (hhi : idx < 540000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 530000
  have hlen : tailKillTauChunk0053Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0053Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0053Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0053_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0053_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0053Start + off = idx := by
      dsimp [off]
      change 530000 + (idx - 530000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0053_witness_bound_at off hoff htag


theorem tailKillTauChunk0054_certificate_at
    (idx : Nat) (hlo : 540000 ≤ idx) (hhi : idx < 550000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 540000
  have hlen : tailKillTauChunk0054Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0054Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0054Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0054_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0054_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0054Start + off = idx := by
      dsimp [off]
      change 540000 + (idx - 540000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0054_witness_bound_at off hoff htag


theorem tailKillTauChunk0055_certificate_at
    (idx : Nat) (hlo : 550000 ≤ idx) (hhi : idx < 560000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 550000
  have hlen : tailKillTauChunk0055Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0055Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0055Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0055_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0055_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0055Start + off = idx := by
      dsimp [off]
      change 550000 + (idx - 550000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0055_witness_bound_at off hoff htag


theorem tailKillTauChunk0056_certificate_at
    (idx : Nat) (hlo : 560000 ≤ idx) (hhi : idx < 570000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 560000
  have hlen : tailKillTauChunk0056Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0056Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0056Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0056_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0056_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0056Start + off = idx := by
      dsimp [off]
      change 560000 + (idx - 560000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0056_witness_bound_at off hoff htag


theorem tailKillTauChunk0057_certificate_at
    (idx : Nat) (hlo : 570000 ≤ idx) (hhi : idx < 580000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 570000
  have hlen : tailKillTauChunk0057Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0057Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0057Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0057_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0057_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0057Start + off = idx := by
      dsimp [off]
      change 570000 + (idx - 570000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0057_witness_bound_at off hoff htag


theorem tailKillTauChunk0058_certificate_at
    (idx : Nat) (hlo : 580000 ≤ idx) (hhi : idx < 590000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 580000
  have hlen : tailKillTauChunk0058Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0058Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0058Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0058_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0058_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0058Start + off = idx := by
      dsimp [off]
      change 580000 + (idx - 580000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0058_witness_bound_at off hoff htag


theorem tailKillTauChunk0059_certificate_at
    (idx : Nat) (hlo : 590000 ≤ idx) (hhi : idx < 600000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 590000
  have hlen : tailKillTauChunk0059Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0059Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0059Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0059_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0059_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0059Start + off = idx := by
      dsimp [off]
      change 590000 + (idx - 590000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0059_witness_bound_at off hoff htag


theorem tailKillTauChunk0060_certificate_at
    (idx : Nat) (hlo : 600000 ≤ idx) (hhi : idx < 610000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 600000
  have hlen : tailKillTauChunk0060Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0060Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0060Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0060_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0060_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0060Start + off = idx := by
      dsimp [off]
      change 600000 + (idx - 600000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0060_witness_bound_at off hoff htag


theorem tailKillTauChunk0061_certificate_at
    (idx : Nat) (hlo : 610000 ≤ idx) (hhi : idx < 620000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 610000
  have hlen : tailKillTauChunk0061Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0061Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0061Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0061_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0061_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0061Start + off = idx := by
      dsimp [off]
      change 610000 + (idx - 610000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0061_witness_bound_at off hoff htag


theorem tailKillTauChunk0062_certificate_at
    (idx : Nat) (hlo : 620000 ≤ idx) (hhi : idx < 630000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 620000
  have hlen : tailKillTauChunk0062Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0062Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0062Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0062_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0062_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0062Start + off = idx := by
      dsimp [off]
      change 620000 + (idx - 620000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0062_witness_bound_at off hoff htag


theorem tailKillTauChunk0063_certificate_at
    (idx : Nat) (hlo : 630000 ≤ idx) (hhi : idx < 640000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 630000
  have hlen : tailKillTauChunk0063Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0063Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0063Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0063_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0063_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0063Start + off = idx := by
      dsimp [off]
      change 630000 + (idx - 630000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0063_witness_bound_at off hoff htag


theorem tailKillTauChunk0064_certificate_at
    (idx : Nat) (hlo : 640000 ≤ idx) (hhi : idx < 650000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 640000
  have hlen : tailKillTauChunk0064Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0064Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0064Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0064_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0064_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0064Start + off = idx := by
      dsimp [off]
      change 640000 + (idx - 640000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0064_witness_bound_at off hoff htag


theorem tailKillTauChunk0065_certificate_at
    (idx : Nat) (hlo : 650000 ≤ idx) (hhi : idx < 660000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 650000
  have hlen : tailKillTauChunk0065Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0065Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0065Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0065_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0065_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0065Start + off = idx := by
      dsimp [off]
      change 650000 + (idx - 650000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0065_witness_bound_at off hoff htag


theorem tailKillTauChunk0066_certificate_at
    (idx : Nat) (hlo : 660000 ≤ idx) (hhi : idx < 670000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 660000
  have hlen : tailKillTauChunk0066Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0066Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0066Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0066_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0066_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0066Start + off = idx := by
      dsimp [off]
      change 660000 + (idx - 660000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0066_witness_bound_at off hoff htag


theorem tailKillTauChunk0067_certificate_at
    (idx : Nat) (hlo : 670000 ≤ idx) (hhi : idx < 680000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 670000
  have hlen : tailKillTauChunk0067Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0067Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0067Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0067_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0067_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0067Start + off = idx := by
      dsimp [off]
      change 670000 + (idx - 670000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0067_witness_bound_at off hoff htag


theorem tailKillTauChunk0068_certificate_at
    (idx : Nat) (hlo : 680000 ≤ idx) (hhi : idx < 690000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 680000
  have hlen : tailKillTauChunk0068Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0068Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0068Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0068_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0068_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0068Start + off = idx := by
      dsimp [off]
      change 680000 + (idx - 680000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0068_witness_bound_at off hoff htag


theorem tailKillTauChunk0069_certificate_at
    (idx : Nat) (hlo : 690000 ≤ idx) (hhi : idx < 700000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 690000
  have hlen : tailKillTauChunk0069Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0069Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0069Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0069_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0069_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0069Start + off = idx := by
      dsimp [off]
      change 690000 + (idx - 690000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0069_witness_bound_at off hoff htag


theorem tailKillTauChunk0070_certificate_at
    (idx : Nat) (hlo : 700000 ≤ idx) (hhi : idx < 710000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 700000
  have hlen : tailKillTauChunk0070Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0070Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0070Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0070_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0070_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0070Start + off = idx := by
      dsimp [off]
      change 700000 + (idx - 700000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0070_witness_bound_at off hoff htag


theorem tailKillTauChunk0071_certificate_at
    (idx : Nat) (hlo : 710000 ≤ idx) (hhi : idx < 720000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 710000
  have hlen : tailKillTauChunk0071Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0071Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0071Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0071_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0071_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0071Start + off = idx := by
      dsimp [off]
      change 710000 + (idx - 710000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0071_witness_bound_at off hoff htag


theorem tailKillTauChunk0072_certificate_at
    (idx : Nat) (hlo : 720000 ≤ idx) (hhi : idx < 730000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 720000
  have hlen : tailKillTauChunk0072Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0072Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0072Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0072_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0072_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0072Start + off = idx := by
      dsimp [off]
      change 720000 + (idx - 720000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0072_witness_bound_at off hoff htag


theorem tailKillTauChunk0073_certificate_at
    (idx : Nat) (hlo : 730000 ≤ idx) (hhi : idx < 740000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 730000
  have hlen : tailKillTauChunk0073Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0073Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0073Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0073_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0073_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0073Start + off = idx := by
      dsimp [off]
      change 730000 + (idx - 730000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0073_witness_bound_at off hoff htag


theorem tailKillTauChunk0074_certificate_at
    (idx : Nat) (hlo : 740000 ≤ idx) (hhi : idx < 750000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 740000
  have hlen : tailKillTauChunk0074Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0074Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0074Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0074_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0074_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0074Start + off = idx := by
      dsimp [off]
      change 740000 + (idx - 740000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0074_witness_bound_at off hoff htag


theorem tailKillTauChunk0075_certificate_at
    (idx : Nat) (hlo : 750000 ≤ idx) (hhi : idx < 760000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 750000
  have hlen : tailKillTauChunk0075Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0075Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0075Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0075_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0075_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0075Start + off = idx := by
      dsimp [off]
      change 750000 + (idx - 750000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0075_witness_bound_at off hoff htag


theorem tailKillTauChunk0076_certificate_at
    (idx : Nat) (hlo : 760000 ≤ idx) (hhi : idx < 770000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 760000
  have hlen : tailKillTauChunk0076Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0076Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0076Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0076_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0076_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0076Start + off = idx := by
      dsimp [off]
      change 760000 + (idx - 760000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0076_witness_bound_at off hoff htag


theorem tailKillTauChunk0077_certificate_at
    (idx : Nat) (hlo : 770000 ≤ idx) (hhi : idx < 780000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 770000
  have hlen : tailKillTauChunk0077Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0077Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0077Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0077_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0077_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0077Start + off = idx := by
      dsimp [off]
      change 770000 + (idx - 770000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0077_witness_bound_at off hoff htag


theorem tailKillTauChunk0078_certificate_at
    (idx : Nat) (hlo : 780000 ≤ idx) (hhi : idx < 790000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 780000
  have hlen : tailKillTauChunk0078Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0078Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0078Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0078_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0078_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0078Start + off = idx := by
      dsimp [off]
      change 780000 + (idx - 780000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0078_witness_bound_at off hoff htag


theorem tailKillTauChunk0079_certificate_at
    (idx : Nat) (hlo : 790000 ≤ idx) (hhi : idx < 800000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 790000
  have hlen : tailKillTauChunk0079Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0079Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0079Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0079_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0079_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0079Start + off = idx := by
      dsimp [off]
      change 790000 + (idx - 790000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0079_witness_bound_at off hoff htag


theorem tailKillTauChunk0080_certificate_at
    (idx : Nat) (hlo : 800000 ≤ idx) (hhi : idx < 810000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 800000
  have hlen : tailKillTauChunk0080Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0080Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0080Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0080_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0080_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0080Start + off = idx := by
      dsimp [off]
      change 800000 + (idx - 800000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0080_witness_bound_at off hoff htag


theorem tailKillTauChunk0081_certificate_at
    (idx : Nat) (hlo : 810000 ≤ idx) (hhi : idx < 820000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 810000
  have hlen : tailKillTauChunk0081Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0081Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0081Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0081_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0081_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0081Start + off = idx := by
      dsimp [off]
      change 810000 + (idx - 810000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0081_witness_bound_at off hoff htag


theorem tailKillTauChunk0082_certificate_at
    (idx : Nat) (hlo : 820000 ≤ idx) (hhi : idx < 830000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 820000
  have hlen : tailKillTauChunk0082Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0082Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0082Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0082_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0082_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0082Start + off = idx := by
      dsimp [off]
      change 820000 + (idx - 820000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0082_witness_bound_at off hoff htag


theorem tailKillTauChunk0083_certificate_at
    (idx : Nat) (hlo : 830000 ≤ idx) (hhi : idx < 840000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 830000
  have hlen : tailKillTauChunk0083Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0083Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0083Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0083_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0083_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0083Start + off = idx := by
      dsimp [off]
      change 830000 + (idx - 830000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0083_witness_bound_at off hoff htag


theorem tailKillTauChunk0084_certificate_at
    (idx : Nat) (hlo : 840000 ≤ idx) (hhi : idx < 850000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 840000
  have hlen : tailKillTauChunk0084Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0084Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0084Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0084_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0084_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0084Start + off = idx := by
      dsimp [off]
      change 840000 + (idx - 840000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0084_witness_bound_at off hoff htag


theorem tailKillTauChunk0085_certificate_at
    (idx : Nat) (hlo : 850000 ≤ idx) (hhi : idx < 860000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 850000
  have hlen : tailKillTauChunk0085Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0085Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0085Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0085_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0085_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0085Start + off = idx := by
      dsimp [off]
      change 850000 + (idx - 850000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0085_witness_bound_at off hoff htag


theorem tailKillTauChunk0086_certificate_at
    (idx : Nat) (hlo : 860000 ≤ idx) (hhi : idx < 870000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 860000
  have hlen : tailKillTauChunk0086Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0086Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0086Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0086_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0086_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0086Start + off = idx := by
      dsimp [off]
      change 860000 + (idx - 860000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0086_witness_bound_at off hoff htag


theorem tailKillTauChunk0087_certificate_at
    (idx : Nat) (hlo : 870000 ≤ idx) (hhi : idx < 880000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 870000
  have hlen : tailKillTauChunk0087Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0087Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0087Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0087_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0087_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0087Start + off = idx := by
      dsimp [off]
      change 870000 + (idx - 870000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0087_witness_bound_at off hoff htag


theorem tailKillTauChunk0088_certificate_at
    (idx : Nat) (hlo : 880000 ≤ idx) (hhi : idx < 890000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 880000
  have hlen : tailKillTauChunk0088Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0088Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0088Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0088_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0088_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0088Start + off = idx := by
      dsimp [off]
      change 880000 + (idx - 880000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0088_witness_bound_at off hoff htag


theorem tailKillTauChunk0089_certificate_at
    (idx : Nat) (hlo : 890000 ≤ idx) (hhi : idx < 900000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 890000
  have hlen : tailKillTauChunk0089Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0089Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0089Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0089_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0089_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0089Start + off = idx := by
      dsimp [off]
      change 890000 + (idx - 890000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0089_witness_bound_at off hoff htag


theorem tailKillTauChunk0090_certificate_at
    (idx : Nat) (hlo : 900000 ≤ idx) (hhi : idx < 910000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 900000
  have hlen : tailKillTauChunk0090Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0090Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0090Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0090_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0090_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0090Start + off = idx := by
      dsimp [off]
      change 900000 + (idx - 900000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0090_witness_bound_at off hoff htag


theorem tailKillTauChunk0091_certificate_at
    (idx : Nat) (hlo : 910000 ≤ idx) (hhi : idx < 920000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 910000
  have hlen : tailKillTauChunk0091Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0091Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0091Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0091_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0091_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0091Start + off = idx := by
      dsimp [off]
      change 910000 + (idx - 910000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0091_witness_bound_at off hoff htag


theorem tailKillTauChunk0092_certificate_at
    (idx : Nat) (hlo : 920000 ≤ idx) (hhi : idx < 930000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 920000
  have hlen : tailKillTauChunk0092Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0092Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0092Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0092_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0092_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0092Start + off = idx := by
      dsimp [off]
      change 920000 + (idx - 920000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0092_witness_bound_at off hoff htag


theorem tailKillTauChunk0093_certificate_at
    (idx : Nat) (hlo : 930000 ≤ idx) (hhi : idx < 940000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 930000
  have hlen : tailKillTauChunk0093Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0093Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0093Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0093_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0093_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0093Start + off = idx := by
      dsimp [off]
      change 930000 + (idx - 930000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0093_witness_bound_at off hoff htag


theorem tailKillTauChunk0094_certificate_at
    (idx : Nat) (hlo : 940000 ≤ idx) (hhi : idx < 950000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 940000
  have hlen : tailKillTauChunk0094Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0094Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0094Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0094_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0094_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0094Start + off = idx := by
      dsimp [off]
      change 940000 + (idx - 940000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0094_witness_bound_at off hoff htag


theorem tailKillTauChunk0095_certificate_at
    (idx : Nat) (hlo : 950000 ≤ idx) (hhi : idx < 960000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 950000
  have hlen : tailKillTauChunk0095Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0095Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0095Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0095_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0095_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0095Start + off = idx := by
      dsimp [off]
      change 950000 + (idx - 950000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0095_witness_bound_at off hoff htag


theorem tailKillTauChunk0096_certificate_at
    (idx : Nat) (hlo : 960000 ≤ idx) (hhi : idx < 970000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 960000
  have hlen : tailKillTauChunk0096Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0096Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0096Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0096_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0096_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0096Start + off = idx := by
      dsimp [off]
      change 960000 + (idx - 960000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0096_witness_bound_at off hoff htag


theorem tailKillTauChunk0097_certificate_at
    (idx : Nat) (hlo : 970000 ≤ idx) (hhi : idx < 980000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 970000
  have hlen : tailKillTauChunk0097Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0097Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0097Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0097_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0097_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0097Start + off = idx := by
      dsimp [off]
      change 970000 + (idx - 970000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0097_witness_bound_at off hoff htag


theorem tailKillTauChunk0098_certificate_at
    (idx : Nat) (hlo : 980000 ≤ idx) (hhi : idx < 990000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 980000
  have hlen : tailKillTauChunk0098Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0098Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0098Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0098_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0098_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0098Start + off = idx := by
      dsimp [off]
      change 980000 + (idx - 980000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0098_witness_bound_at off hoff htag


theorem tailKillTauChunk0099_certificate_at
    (idx : Nat) (hlo : 990000 ≤ idx) (hhi : idx < 1000000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 990000
  have hlen : tailKillTauChunk0099Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0099Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0099Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0099_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0099_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0099Start + off = idx := by
      dsimp [off]
      change 990000 + (idx - 990000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0099_witness_bound_at off hoff htag


theorem tailKillTauChunk0100_certificate_at
    (idx : Nat) (hlo : 1000000 ≤ idx) (hhi : idx < 1010000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1000000
  have hlen : tailKillTauChunk0100Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0100Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0100Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0100_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0100_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0100Start + off = idx := by
      dsimp [off]
      change 1000000 + (idx - 1000000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0100_witness_bound_at off hoff htag


theorem tailKillTauChunk0101_certificate_at
    (idx : Nat) (hlo : 1010000 ≤ idx) (hhi : idx < 1020000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1010000
  have hlen : tailKillTauChunk0101Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0101Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0101Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0101_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0101_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0101Start + off = idx := by
      dsimp [off]
      change 1010000 + (idx - 1010000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0101_witness_bound_at off hoff htag


theorem tailKillTauChunk0102_certificate_at
    (idx : Nat) (hlo : 1020000 ≤ idx) (hhi : idx < 1030000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1020000
  have hlen : tailKillTauChunk0102Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0102Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0102Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0102_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0102_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0102Start + off = idx := by
      dsimp [off]
      change 1020000 + (idx - 1020000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0102_witness_bound_at off hoff htag


theorem tailKillTauChunk0103_certificate_at
    (idx : Nat) (hlo : 1030000 ≤ idx) (hhi : idx < 1040000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1030000
  have hlen : tailKillTauChunk0103Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0103Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0103Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0103_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0103_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0103Start + off = idx := by
      dsimp [off]
      change 1030000 + (idx - 1030000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0103_witness_bound_at off hoff htag


theorem tailKillTauChunk0104_certificate_at
    (idx : Nat) (hlo : 1040000 ≤ idx) (hhi : idx < 1050000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1040000
  have hlen : tailKillTauChunk0104Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0104Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0104Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0104_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0104_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0104Start + off = idx := by
      dsimp [off]
      change 1040000 + (idx - 1040000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0104_witness_bound_at off hoff htag


theorem tailKillTauChunk0105_certificate_at
    (idx : Nat) (hlo : 1050000 ≤ idx) (hhi : idx < 1060000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1050000
  have hlen : tailKillTauChunk0105Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0105Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0105Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0105_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0105_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0105Start + off = idx := by
      dsimp [off]
      change 1050000 + (idx - 1050000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0105_witness_bound_at off hoff htag


theorem tailKillTauChunk0106_certificate_at
    (idx : Nat) (hlo : 1060000 ≤ idx) (hhi : idx < 1070000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1060000
  have hlen : tailKillTauChunk0106Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0106Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0106Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0106_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0106_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0106Start + off = idx := by
      dsimp [off]
      change 1060000 + (idx - 1060000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0106_witness_bound_at off hoff htag


theorem tailKillTauChunk0107_certificate_at
    (idx : Nat) (hlo : 1070000 ≤ idx) (hhi : idx < 1080000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1070000
  have hlen : tailKillTauChunk0107Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0107Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0107Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0107_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0107_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0107Start + off = idx := by
      dsimp [off]
      change 1070000 + (idx - 1070000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0107_witness_bound_at off hoff htag


theorem tailKillTauChunk0108_certificate_at
    (idx : Nat) (hlo : 1080000 ≤ idx) (hhi : idx < 1090000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1080000
  have hlen : tailKillTauChunk0108Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0108Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0108Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0108_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0108_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0108Start + off = idx := by
      dsimp [off]
      change 1080000 + (idx - 1080000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0108_witness_bound_at off hoff htag


theorem tailKillTauChunk0109_certificate_at
    (idx : Nat) (hlo : 1090000 ≤ idx) (hhi : idx < 1100000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1090000
  have hlen : tailKillTauChunk0109Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0109Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0109Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0109_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0109_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0109Start + off = idx := by
      dsimp [off]
      change 1090000 + (idx - 1090000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0109_witness_bound_at off hoff htag


theorem tailKillTauChunk0110_certificate_at
    (idx : Nat) (hlo : 1100000 ≤ idx) (hhi : idx < 1110000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1100000
  have hlen : tailKillTauChunk0110Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0110Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0110Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0110_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0110_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0110Start + off = idx := by
      dsimp [off]
      change 1100000 + (idx - 1100000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0110_witness_bound_at off hoff htag


theorem tailKillTauChunk0111_certificate_at
    (idx : Nat) (hlo : 1110000 ≤ idx) (hhi : idx < 1120000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1110000
  have hlen : tailKillTauChunk0111Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0111Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0111Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0111_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0111_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0111Start + off = idx := by
      dsimp [off]
      change 1110000 + (idx - 1110000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0111_witness_bound_at off hoff htag


theorem tailKillTauChunk0112_certificate_at
    (idx : Nat) (hlo : 1120000 ≤ idx) (hhi : idx < 1130000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1120000
  have hlen : tailKillTauChunk0112Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0112Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0112Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0112_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0112_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0112Start + off = idx := by
      dsimp [off]
      change 1120000 + (idx - 1120000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0112_witness_bound_at off hoff htag


theorem tailKillTauChunk0113_certificate_at
    (idx : Nat) (hlo : 1130000 ≤ idx) (hhi : idx < 1140000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1130000
  have hlen : tailKillTauChunk0113Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0113Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0113Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0113_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0113_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0113Start + off = idx := by
      dsimp [off]
      change 1130000 + (idx - 1130000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0113_witness_bound_at off hoff htag


theorem tailKillTauChunk0114_certificate_at
    (idx : Nat) (hlo : 1140000 ≤ idx) (hhi : idx < 1150000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1140000
  have hlen : tailKillTauChunk0114Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0114Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0114Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0114_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0114_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0114Start + off = idx := by
      dsimp [off]
      change 1140000 + (idx - 1140000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0114_witness_bound_at off hoff htag


theorem tailKillTauChunk0115_certificate_at
    (idx : Nat) (hlo : 1150000 ≤ idx) (hhi : idx < 1160000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1150000
  have hlen : tailKillTauChunk0115Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0115Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0115Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0115_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0115_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0115Start + off = idx := by
      dsimp [off]
      change 1150000 + (idx - 1150000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0115_witness_bound_at off hoff htag


theorem tailKillTauChunk0116_certificate_at
    (idx : Nat) (hlo : 1160000 ≤ idx) (hhi : idx < 1170000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1160000
  have hlen : tailKillTauChunk0116Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0116Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0116Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0116_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0116_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0116Start + off = idx := by
      dsimp [off]
      change 1160000 + (idx - 1160000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0116_witness_bound_at off hoff htag


theorem tailKillTauChunk0117_certificate_at
    (idx : Nat) (hlo : 1170000 ≤ idx) (hhi : idx < 1180000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1170000
  have hlen : tailKillTauChunk0117Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0117Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0117Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0117_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0117_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0117Start + off = idx := by
      dsimp [off]
      change 1170000 + (idx - 1170000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0117_witness_bound_at off hoff htag


theorem tailKillTauChunk0118_certificate_at
    (idx : Nat) (hlo : 1180000 ≤ idx) (hhi : idx < 1190000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1180000
  have hlen : tailKillTauChunk0118Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0118Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0118Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0118_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0118_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0118Start + off = idx := by
      dsimp [off]
      change 1180000 + (idx - 1180000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0118_witness_bound_at off hoff htag


theorem tailKillTauChunk0119_certificate_at
    (idx : Nat) (hlo : 1190000 ≤ idx) (hhi : idx < 1200000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1190000
  have hlen : tailKillTauChunk0119Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0119Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0119Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0119_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0119_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0119Start + off = idx := by
      dsimp [off]
      change 1190000 + (idx - 1190000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0119_witness_bound_at off hoff htag


theorem tailKillTauChunk0120_certificate_at
    (idx : Nat) (hlo : 1200000 ≤ idx) (hhi : idx < 1210000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1200000
  have hlen : tailKillTauChunk0120Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0120Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0120Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0120_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0120_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0120Start + off = idx := by
      dsimp [off]
      change 1200000 + (idx - 1200000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0120_witness_bound_at off hoff htag


theorem tailKillTauChunk0121_certificate_at
    (idx : Nat) (hlo : 1210000 ≤ idx) (hhi : idx < 1220000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1210000
  have hlen : tailKillTauChunk0121Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0121Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0121Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0121_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0121_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0121Start + off = idx := by
      dsimp [off]
      change 1210000 + (idx - 1210000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0121_witness_bound_at off hoff htag


theorem tailKillTauChunk0122_certificate_at
    (idx : Nat) (hlo : 1220000 ≤ idx) (hhi : idx < 1230000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1220000
  have hlen : tailKillTauChunk0122Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0122Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0122Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0122_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0122_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0122Start + off = idx := by
      dsimp [off]
      change 1220000 + (idx - 1220000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0122_witness_bound_at off hoff htag


theorem tailKillTauChunk0123_certificate_at
    (idx : Nat) (hlo : 1230000 ≤ idx) (hhi : idx < 1240000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1230000
  have hlen : tailKillTauChunk0123Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0123Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0123Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0123_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0123_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0123Start + off = idx := by
      dsimp [off]
      change 1230000 + (idx - 1230000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0123_witness_bound_at off hoff htag


theorem tailKillTauChunk0124_certificate_at
    (idx : Nat) (hlo : 1240000 ≤ idx) (hhi : idx < 1250000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1240000
  have hlen : tailKillTauChunk0124Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0124Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0124Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0124_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0124_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0124Start + off = idx := by
      dsimp [off]
      change 1240000 + (idx - 1240000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0124_witness_bound_at off hoff htag


theorem tailKillTauChunk0125_certificate_at
    (idx : Nat) (hlo : 1250000 ≤ idx) (hhi : idx < 1260000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1250000
  have hlen : tailKillTauChunk0125Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0125Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0125Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0125_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0125_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0125Start + off = idx := by
      dsimp [off]
      change 1250000 + (idx - 1250000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0125_witness_bound_at off hoff htag


theorem tailKillTauChunk0126_certificate_at
    (idx : Nat) (hlo : 1260000 ≤ idx) (hhi : idx < 1270000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1260000
  have hlen : tailKillTauChunk0126Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0126Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0126Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0126_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0126_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0126Start + off = idx := by
      dsimp [off]
      change 1260000 + (idx - 1260000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0126_witness_bound_at off hoff htag


theorem tailKillTauChunk0127_certificate_at
    (idx : Nat) (hlo : 1270000 ≤ idx) (hhi : idx < 1280000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1270000
  have hlen : tailKillTauChunk0127Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0127Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0127Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0127_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0127_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0127Start + off = idx := by
      dsimp [off]
      change 1270000 + (idx - 1270000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0127_witness_bound_at off hoff htag


theorem tailKillTauChunk0128_certificate_at
    (idx : Nat) (hlo : 1280000 ≤ idx) (hhi : idx < 1290000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1280000
  have hlen : tailKillTauChunk0128Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0128Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0128Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0128_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0128_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0128Start + off = idx := by
      dsimp [off]
      change 1280000 + (idx - 1280000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0128_witness_bound_at off hoff htag


theorem tailKillTauChunk0129_certificate_at
    (idx : Nat) (hlo : 1290000 ≤ idx) (hhi : idx < 1300000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1290000
  have hlen : tailKillTauChunk0129Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0129Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0129Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0129_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0129_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0129Start + off = idx := by
      dsimp [off]
      change 1290000 + (idx - 1290000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0129_witness_bound_at off hoff htag


theorem tailKillTauChunk0130_certificate_at
    (idx : Nat) (hlo : 1300000 ≤ idx) (hhi : idx < 1310000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1300000
  have hlen : tailKillTauChunk0130Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0130Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0130Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0130_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0130_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0130Start + off = idx := by
      dsimp [off]
      change 1300000 + (idx - 1300000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0130_witness_bound_at off hoff htag


theorem tailKillTauChunk0131_certificate_at
    (idx : Nat) (hlo : 1310000 ≤ idx) (hhi : idx < 1320000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1310000
  have hlen : tailKillTauChunk0131Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0131Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0131Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0131_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0131_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0131Start + off = idx := by
      dsimp [off]
      change 1310000 + (idx - 1310000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0131_witness_bound_at off hoff htag


theorem tailKillTauChunk0132_certificate_at
    (idx : Nat) (hlo : 1320000 ≤ idx) (hhi : idx < 1330000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1320000
  have hlen : tailKillTauChunk0132Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0132Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0132Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0132_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0132_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0132Start + off = idx := by
      dsimp [off]
      change 1320000 + (idx - 1320000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0132_witness_bound_at off hoff htag


theorem tailKillTauChunk0133_certificate_at
    (idx : Nat) (hlo : 1330000 ≤ idx) (hhi : idx < 1340000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1330000
  have hlen : tailKillTauChunk0133Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0133Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0133Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0133_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0133_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0133Start + off = idx := by
      dsimp [off]
      change 1330000 + (idx - 1330000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0133_witness_bound_at off hoff htag


theorem tailKillTauChunk0134_certificate_at
    (idx : Nat) (hlo : 1340000 ≤ idx) (hhi : idx < 1350000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1340000
  have hlen : tailKillTauChunk0134Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0134Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0134Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0134_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0134_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0134Start + off = idx := by
      dsimp [off]
      change 1340000 + (idx - 1340000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0134_witness_bound_at off hoff htag


theorem tailKillTauChunk0135_certificate_at
    (idx : Nat) (hlo : 1350000 ≤ idx) (hhi : idx < 1360000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1350000
  have hlen : tailKillTauChunk0135Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0135Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0135Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0135_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0135_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0135Start + off = idx := by
      dsimp [off]
      change 1350000 + (idx - 1350000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0135_witness_bound_at off hoff htag


theorem tailKillTauChunk0136_certificate_at
    (idx : Nat) (hlo : 1360000 ≤ idx) (hhi : idx < 1370000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1360000
  have hlen : tailKillTauChunk0136Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0136Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0136Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0136_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0136_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0136Start + off = idx := by
      dsimp [off]
      change 1360000 + (idx - 1360000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0136_witness_bound_at off hoff htag


theorem tailKillTauChunk0137_certificate_at
    (idx : Nat) (hlo : 1370000 ≤ idx) (hhi : idx < 1380000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1370000
  have hlen : tailKillTauChunk0137Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0137Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0137Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0137_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0137_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0137Start + off = idx := by
      dsimp [off]
      change 1370000 + (idx - 1370000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0137_witness_bound_at off hoff htag


theorem tailKillTauChunk0138_certificate_at
    (idx : Nat) (hlo : 1380000 ≤ idx) (hhi : idx < 1390000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1380000
  have hlen : tailKillTauChunk0138Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0138Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0138Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0138_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0138_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0138Start + off = idx := by
      dsimp [off]
      change 1380000 + (idx - 1380000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0138_witness_bound_at off hoff htag


theorem tailKillTauChunk0139_certificate_at
    (idx : Nat) (hlo : 1390000 ≤ idx) (hhi : idx < 1400000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1390000
  have hlen : tailKillTauChunk0139Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0139Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0139Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0139_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0139_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0139Start + off = idx := by
      dsimp [off]
      change 1390000 + (idx - 1390000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0139_witness_bound_at off hoff htag


theorem tailKillTauChunk0140_certificate_at
    (idx : Nat) (hlo : 1400000 ≤ idx) (hhi : idx < 1410000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1400000
  have hlen : tailKillTauChunk0140Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0140Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0140Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0140_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0140_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0140Start + off = idx := by
      dsimp [off]
      change 1400000 + (idx - 1400000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0140_witness_bound_at off hoff htag


theorem tailKillTauChunk0141_certificate_at
    (idx : Nat) (hlo : 1410000 ≤ idx) (hhi : idx < 1420000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1410000
  have hlen : tailKillTauChunk0141Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0141Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0141Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0141_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0141_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0141Start + off = idx := by
      dsimp [off]
      change 1410000 + (idx - 1410000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0141_witness_bound_at off hoff htag


theorem tailKillTauChunk0142_certificate_at
    (idx : Nat) (hlo : 1420000 ≤ idx) (hhi : idx < 1430000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1420000
  have hlen : tailKillTauChunk0142Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0142Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0142Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0142_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0142_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0142Start + off = idx := by
      dsimp [off]
      change 1420000 + (idx - 1420000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0142_witness_bound_at off hoff htag


theorem tailKillTauChunk0143_certificate_at
    (idx : Nat) (hlo : 1430000 ≤ idx) (hhi : idx < 1440000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1430000
  have hlen : tailKillTauChunk0143Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0143Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0143Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0143_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0143_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0143Start + off = idx := by
      dsimp [off]
      change 1430000 + (idx - 1430000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0143_witness_bound_at off hoff htag


theorem tailKillTauChunk0144_certificate_at
    (idx : Nat) (hlo : 1440000 ≤ idx) (hhi : idx < 1450000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1440000
  have hlen : tailKillTauChunk0144Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0144Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0144Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0144_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0144_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0144Start + off = idx := by
      dsimp [off]
      change 1440000 + (idx - 1440000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0144_witness_bound_at off hoff htag


theorem tailKillTauChunk0145_certificate_at
    (idx : Nat) (hlo : 1450000 ≤ idx) (hhi : idx < 1460000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1450000
  have hlen : tailKillTauChunk0145Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0145Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0145Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0145_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0145_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0145Start + off = idx := by
      dsimp [off]
      change 1450000 + (idx - 1450000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0145_witness_bound_at off hoff htag


theorem tailKillTauChunk0146_certificate_at
    (idx : Nat) (hlo : 1460000 ≤ idx) (hhi : idx < 1470000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1460000
  have hlen : tailKillTauChunk0146Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0146Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0146Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0146_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0146_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0146Start + off = idx := by
      dsimp [off]
      change 1460000 + (idx - 1460000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0146_witness_bound_at off hoff htag


theorem tailKillTauChunk0147_certificate_at
    (idx : Nat) (hlo : 1470000 ≤ idx) (hhi : idx < 1480000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1470000
  have hlen : tailKillTauChunk0147Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0147Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0147Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0147_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0147_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0147Start + off = idx := by
      dsimp [off]
      change 1470000 + (idx - 1470000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0147_witness_bound_at off hoff htag


theorem tailKillTauChunk0148_certificate_at
    (idx : Nat) (hlo : 1480000 ≤ idx) (hhi : idx < 1490000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1480000
  have hlen : tailKillTauChunk0148Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0148Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0148Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0148_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0148_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0148Start + off = idx := by
      dsimp [off]
      change 1480000 + (idx - 1480000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0148_witness_bound_at off hoff htag


theorem tailKillTauChunk0149_certificate_at
    (idx : Nat) (hlo : 1490000 ≤ idx) (hhi : idx < 1500000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1490000
  have hlen : tailKillTauChunk0149Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0149Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0149Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0149_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0149_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0149Start + off = idx := by
      dsimp [off]
      change 1490000 + (idx - 1490000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0149_witness_bound_at off hoff htag


theorem tailKillTauChunk0150_certificate_at
    (idx : Nat) (hlo : 1500000 ≤ idx) (hhi : idx < 1510000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1500000
  have hlen : tailKillTauChunk0150Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0150Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0150Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0150_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0150_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0150Start + off = idx := by
      dsimp [off]
      change 1500000 + (idx - 1500000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0150_witness_bound_at off hoff htag


theorem tailKillTauChunk0151_certificate_at
    (idx : Nat) (hlo : 1510000 ≤ idx) (hhi : idx < 1520000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1510000
  have hlen : tailKillTauChunk0151Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0151Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0151Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0151_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0151_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0151Start + off = idx := by
      dsimp [off]
      change 1510000 + (idx - 1510000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0151_witness_bound_at off hoff htag


theorem tailKillTauChunk0152_certificate_at
    (idx : Nat) (hlo : 1520000 ≤ idx) (hhi : idx < 1530000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1520000
  have hlen : tailKillTauChunk0152Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0152Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0152Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0152_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0152_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0152Start + off = idx := by
      dsimp [off]
      change 1520000 + (idx - 1520000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0152_witness_bound_at off hoff htag


theorem tailKillTauChunk0153_certificate_at
    (idx : Nat) (hlo : 1530000 ≤ idx) (hhi : idx < 1540000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1530000
  have hlen : tailKillTauChunk0153Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0153Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0153Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0153_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0153_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0153Start + off = idx := by
      dsimp [off]
      change 1530000 + (idx - 1530000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0153_witness_bound_at off hoff htag


theorem tailKillTauChunk0154_certificate_at
    (idx : Nat) (hlo : 1540000 ≤ idx) (hhi : idx < 1550000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1540000
  have hlen : tailKillTauChunk0154Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0154Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0154Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0154_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0154_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0154Start + off = idx := by
      dsimp [off]
      change 1540000 + (idx - 1540000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0154_witness_bound_at off hoff htag


theorem tailKillTauChunk0155_certificate_at
    (idx : Nat) (hlo : 1550000 ≤ idx) (hhi : idx < 1560000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1550000
  have hlen : tailKillTauChunk0155Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0155Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0155Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0155_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0155_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0155Start + off = idx := by
      dsimp [off]
      change 1550000 + (idx - 1550000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0155_witness_bound_at off hoff htag


theorem tailKillTauChunk0156_certificate_at
    (idx : Nat) (hlo : 1560000 ≤ idx) (hhi : idx < 1570000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1560000
  have hlen : tailKillTauChunk0156Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0156Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0156Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0156_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0156_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0156Start + off = idx := by
      dsimp [off]
      change 1560000 + (idx - 1560000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0156_witness_bound_at off hoff htag


theorem tailKillTauChunk0157_certificate_at
    (idx : Nat) (hlo : 1570000 ≤ idx) (hhi : idx < 1580000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1570000
  have hlen : tailKillTauChunk0157Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0157Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0157Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0157_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0157_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0157Start + off = idx := by
      dsimp [off]
      change 1570000 + (idx - 1570000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0157_witness_bound_at off hoff htag


theorem tailKillTauChunk0158_certificate_at
    (idx : Nat) (hlo : 1580000 ≤ idx) (hhi : idx < 1590000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1580000
  have hlen : tailKillTauChunk0158Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0158Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0158Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0158_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0158_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0158Start + off = idx := by
      dsimp [off]
      change 1580000 + (idx - 1580000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0158_witness_bound_at off hoff htag


theorem tailKillTauChunk0159_certificate_at
    (idx : Nat) (hlo : 1590000 ≤ idx) (hhi : idx < 1600000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1590000
  have hlen : tailKillTauChunk0159Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0159Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0159Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0159_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0159_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0159Start + off = idx := by
      dsimp [off]
      change 1590000 + (idx - 1590000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0159_witness_bound_at off hoff htag


theorem tailKillTauChunk0160_certificate_at
    (idx : Nat) (hlo : 1600000 ≤ idx) (hhi : idx < 1610000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1600000
  have hlen : tailKillTauChunk0160Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0160Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0160Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0160_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0160_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0160Start + off = idx := by
      dsimp [off]
      change 1600000 + (idx - 1600000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0160_witness_bound_at off hoff htag


theorem tailKillTauChunk0161_certificate_at
    (idx : Nat) (hlo : 1610000 ≤ idx) (hhi : idx < 1620000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1610000
  have hlen : tailKillTauChunk0161Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0161Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0161Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0161_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0161_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0161Start + off = idx := by
      dsimp [off]
      change 1610000 + (idx - 1610000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0161_witness_bound_at off hoff htag


theorem tailKillTauChunk0162_certificate_at
    (idx : Nat) (hlo : 1620000 ≤ idx) (hhi : idx < 1630000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1620000
  have hlen : tailKillTauChunk0162Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0162Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0162Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0162_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0162_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0162Start + off = idx := by
      dsimp [off]
      change 1620000 + (idx - 1620000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0162_witness_bound_at off hoff htag


theorem tailKillTauChunk0163_certificate_at
    (idx : Nat) (hlo : 1630000 ≤ idx) (hhi : idx < 1640000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1630000
  have hlen : tailKillTauChunk0163Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0163Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0163Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0163_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0163_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0163Start + off = idx := by
      dsimp [off]
      change 1630000 + (idx - 1630000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0163_witness_bound_at off hoff htag


theorem tailKillTauChunk0164_certificate_at
    (idx : Nat) (hlo : 1640000 ≤ idx) (hhi : idx < 1650000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1640000
  have hlen : tailKillTauChunk0164Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0164Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0164Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0164_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0164_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0164Start + off = idx := by
      dsimp [off]
      change 1640000 + (idx - 1640000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0164_witness_bound_at off hoff htag


theorem tailKillTauChunk0165_certificate_at
    (idx : Nat) (hlo : 1650000 ≤ idx) (hhi : idx < 1660000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1650000
  have hlen : tailKillTauChunk0165Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0165Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0165Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0165_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0165_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0165Start + off = idx := by
      dsimp [off]
      change 1650000 + (idx - 1650000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0165_witness_bound_at off hoff htag


theorem tailKillTauChunk0166_certificate_at
    (idx : Nat) (hlo : 1660000 ≤ idx) (hhi : idx < 1670000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1660000
  have hlen : tailKillTauChunk0166Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0166Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0166Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0166_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0166_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0166Start + off = idx := by
      dsimp [off]
      change 1660000 + (idx - 1660000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0166_witness_bound_at off hoff htag


theorem tailKillTauChunk0167_certificate_at
    (idx : Nat) (hlo : 1670000 ≤ idx) (hhi : idx < 1680000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1670000
  have hlen : tailKillTauChunk0167Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0167Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0167Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0167_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0167_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0167Start + off = idx := by
      dsimp [off]
      change 1670000 + (idx - 1670000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0167_witness_bound_at off hoff htag


theorem tailKillTauChunk0168_certificate_at
    (idx : Nat) (hlo : 1680000 ≤ idx) (hhi : idx < 1690000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1680000
  have hlen : tailKillTauChunk0168Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0168Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0168Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0168_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0168_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0168Start + off = idx := by
      dsimp [off]
      change 1680000 + (idx - 1680000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0168_witness_bound_at off hoff htag


theorem tailKillTauChunk0169_certificate_at
    (idx : Nat) (hlo : 1690000 ≤ idx) (hhi : idx < 1700000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1690000
  have hlen : tailKillTauChunk0169Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0169Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0169Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0169_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0169_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0169Start + off = idx := by
      dsimp [off]
      change 1690000 + (idx - 1690000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0169_witness_bound_at off hoff htag


theorem tailKillTauChunk0170_certificate_at
    (idx : Nat) (hlo : 1700000 ≤ idx) (hhi : idx < 1710000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1700000
  have hlen : tailKillTauChunk0170Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0170Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0170Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0170_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0170_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0170Start + off = idx := by
      dsimp [off]
      change 1700000 + (idx - 1700000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0170_witness_bound_at off hoff htag


theorem tailKillTauChunk0171_certificate_at
    (idx : Nat) (hlo : 1710000 ≤ idx) (hhi : idx < 1720000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1710000
  have hlen : tailKillTauChunk0171Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0171Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0171Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0171_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0171_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0171Start + off = idx := by
      dsimp [off]
      change 1710000 + (idx - 1710000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0171_witness_bound_at off hoff htag


theorem tailKillTauChunk0172_certificate_at
    (idx : Nat) (hlo : 1720000 ≤ idx) (hhi : idx < 1730000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1720000
  have hlen : tailKillTauChunk0172Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0172Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0172Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0172_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0172_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0172Start + off = idx := by
      dsimp [off]
      change 1720000 + (idx - 1720000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0172_witness_bound_at off hoff htag


theorem tailKillTauChunk0173_certificate_at
    (idx : Nat) (hlo : 1730000 ≤ idx) (hhi : idx < 1740000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1730000
  have hlen : tailKillTauChunk0173Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0173Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0173Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0173_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0173_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0173Start + off = idx := by
      dsimp [off]
      change 1730000 + (idx - 1730000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0173_witness_bound_at off hoff htag


theorem tailKillTauChunk0174_certificate_at
    (idx : Nat) (hlo : 1740000 ≤ idx) (hhi : idx < 1750000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1740000
  have hlen : tailKillTauChunk0174Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0174Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0174Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0174_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0174_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0174Start + off = idx := by
      dsimp [off]
      change 1740000 + (idx - 1740000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0174_witness_bound_at off hoff htag


theorem tailKillTauChunk0175_certificate_at
    (idx : Nat) (hlo : 1750000 ≤ idx) (hhi : idx < 1760000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1750000
  have hlen : tailKillTauChunk0175Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0175Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0175Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0175_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0175_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0175Start + off = idx := by
      dsimp [off]
      change 1750000 + (idx - 1750000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0175_witness_bound_at off hoff htag


theorem tailKillTauChunk0176_certificate_at
    (idx : Nat) (hlo : 1760000 ≤ idx) (hhi : idx < 1770000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1760000
  have hlen : tailKillTauChunk0176Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0176Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0176Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0176_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0176_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0176Start + off = idx := by
      dsimp [off]
      change 1760000 + (idx - 1760000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0176_witness_bound_at off hoff htag


theorem tailKillTauChunk0177_certificate_at
    (idx : Nat) (hlo : 1770000 ≤ idx) (hhi : idx < 1780000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1770000
  have hlen : tailKillTauChunk0177Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0177Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0177Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0177_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0177_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0177Start + off = idx := by
      dsimp [off]
      change 1770000 + (idx - 1770000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0177_witness_bound_at off hoff htag


theorem tailKillTauChunk0178_certificate_at
    (idx : Nat) (hlo : 1780000 ≤ idx) (hhi : idx < 1790000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1780000
  have hlen : tailKillTauChunk0178Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0178Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0178Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0178_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0178_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0178Start + off = idx := by
      dsimp [off]
      change 1780000 + (idx - 1780000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0178_witness_bound_at off hoff htag


theorem tailKillTauChunk0179_certificate_at
    (idx : Nat) (hlo : 1790000 ≤ idx) (hhi : idx < 1800000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1790000
  have hlen : tailKillTauChunk0179Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0179Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0179Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0179_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0179_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0179Start + off = idx := by
      dsimp [off]
      change 1790000 + (idx - 1790000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0179_witness_bound_at off hoff htag


theorem tailKillTauChunk0180_certificate_at
    (idx : Nat) (hlo : 1800000 ≤ idx) (hhi : idx < 1810000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1800000
  have hlen : tailKillTauChunk0180Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0180Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0180Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0180_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0180_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0180Start + off = idx := by
      dsimp [off]
      change 1800000 + (idx - 1800000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0180_witness_bound_at off hoff htag


theorem tailKillTauChunk0181_certificate_at
    (idx : Nat) (hlo : 1810000 ≤ idx) (hhi : idx < 1820000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1810000
  have hlen : tailKillTauChunk0181Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0181Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0181Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0181_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0181_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0181Start + off = idx := by
      dsimp [off]
      change 1810000 + (idx - 1810000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0181_witness_bound_at off hoff htag


theorem tailKillTauChunk0182_certificate_at
    (idx : Nat) (hlo : 1820000 ≤ idx) (hhi : idx < 1830000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1820000
  have hlen : tailKillTauChunk0182Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0182Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0182Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0182_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0182_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0182Start + off = idx := by
      dsimp [off]
      change 1820000 + (idx - 1820000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0182_witness_bound_at off hoff htag


theorem tailKillTauChunk0183_certificate_at
    (idx : Nat) (hlo : 1830000 ≤ idx) (hhi : idx < 1840000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1830000
  have hlen : tailKillTauChunk0183Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0183Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0183Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0183_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0183_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0183Start + off = idx := by
      dsimp [off]
      change 1830000 + (idx - 1830000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0183_witness_bound_at off hoff htag


theorem tailKillTauChunk0184_certificate_at
    (idx : Nat) (hlo : 1840000 ≤ idx) (hhi : idx < 1850000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1840000
  have hlen : tailKillTauChunk0184Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0184Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0184Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0184_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0184_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0184Start + off = idx := by
      dsimp [off]
      change 1840000 + (idx - 1840000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0184_witness_bound_at off hoff htag


theorem tailKillTauChunk0185_certificate_at
    (idx : Nat) (hlo : 1850000 ≤ idx) (hhi : idx < 1860000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1850000
  have hlen : tailKillTauChunk0185Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0185Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0185Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0185_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0185_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0185Start + off = idx := by
      dsimp [off]
      change 1850000 + (idx - 1850000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0185_witness_bound_at off hoff htag


theorem tailKillTauChunk0186_certificate_at
    (idx : Nat) (hlo : 1860000 ≤ idx) (hhi : idx < 1870000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1860000
  have hlen : tailKillTauChunk0186Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0186Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0186Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0186_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0186_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0186Start + off = idx := by
      dsimp [off]
      change 1860000 + (idx - 1860000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0186_witness_bound_at off hoff htag


theorem tailKillTauChunk0187_certificate_at
    (idx : Nat) (hlo : 1870000 ≤ idx) (hhi : idx < 1880000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1870000
  have hlen : tailKillTauChunk0187Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0187Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0187Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0187_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0187_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0187Start + off = idx := by
      dsimp [off]
      change 1870000 + (idx - 1870000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0187_witness_bound_at off hoff htag


theorem tailKillTauChunk0188_certificate_at
    (idx : Nat) (hlo : 1880000 ≤ idx) (hhi : idx < 1890000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1880000
  have hlen : tailKillTauChunk0188Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0188Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0188Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0188_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0188_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0188Start + off = idx := by
      dsimp [off]
      change 1880000 + (idx - 1880000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0188_witness_bound_at off hoff htag


theorem tailKillTauChunk0189_certificate_at
    (idx : Nat) (hlo : 1890000 ≤ idx) (hhi : idx < 1900000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1890000
  have hlen : tailKillTauChunk0189Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0189Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0189Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0189_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0189_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0189Start + off = idx := by
      dsimp [off]
      change 1890000 + (idx - 1890000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0189_witness_bound_at off hoff htag


theorem tailKillTauChunk0190_certificate_at
    (idx : Nat) (hlo : 1900000 ≤ idx) (hhi : idx < 1910000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1900000
  have hlen : tailKillTauChunk0190Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0190Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0190Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0190_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0190_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0190Start + off = idx := by
      dsimp [off]
      change 1900000 + (idx - 1900000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0190_witness_bound_at off hoff htag


theorem tailKillTauChunk0191_certificate_at
    (idx : Nat) (hlo : 1910000 ≤ idx) (hhi : idx < 1920000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1910000
  have hlen : tailKillTauChunk0191Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0191Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0191Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0191_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0191_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0191Start + off = idx := by
      dsimp [off]
      change 1910000 + (idx - 1910000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0191_witness_bound_at off hoff htag


theorem tailKillTauChunk0192_certificate_at
    (idx : Nat) (hlo : 1920000 ≤ idx) (hhi : idx < 1930000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1920000
  have hlen : tailKillTauChunk0192Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0192Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0192Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0192_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0192_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0192Start + off = idx := by
      dsimp [off]
      change 1920000 + (idx - 1920000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0192_witness_bound_at off hoff htag


theorem tailKillTauChunk0193_certificate_at
    (idx : Nat) (hlo : 1930000 ≤ idx) (hhi : idx < 1940000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1930000
  have hlen : tailKillTauChunk0193Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0193Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0193Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0193_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0193_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0193Start + off = idx := by
      dsimp [off]
      change 1930000 + (idx - 1930000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0193_witness_bound_at off hoff htag


theorem tailKillTauChunk0194_certificate_at
    (idx : Nat) (hlo : 1940000 ≤ idx) (hhi : idx < 1950000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1940000
  have hlen : tailKillTauChunk0194Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0194Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0194Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0194_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0194_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0194Start + off = idx := by
      dsimp [off]
      change 1940000 + (idx - 1940000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0194_witness_bound_at off hoff htag


theorem tailKillTauChunk0195_certificate_at
    (idx : Nat) (hlo : 1950000 ≤ idx) (hhi : idx < 1960000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1950000
  have hlen : tailKillTauChunk0195Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0195Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0195Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0195_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0195_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0195Start + off = idx := by
      dsimp [off]
      change 1950000 + (idx - 1950000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0195_witness_bound_at off hoff htag


theorem tailKillTauChunk0196_certificate_at
    (idx : Nat) (hlo : 1960000 ≤ idx) (hhi : idx < 1970000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1960000
  have hlen : tailKillTauChunk0196Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0196Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0196Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0196_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0196_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0196Start + off = idx := by
      dsimp [off]
      change 1960000 + (idx - 1960000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0196_witness_bound_at off hoff htag


theorem tailKillTauChunk0197_certificate_at
    (idx : Nat) (hlo : 1970000 ≤ idx) (hhi : idx < 1980000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1970000
  have hlen : tailKillTauChunk0197Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0197Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0197Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0197_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0197_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0197Start + off = idx := by
      dsimp [off]
      change 1970000 + (idx - 1970000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0197_witness_bound_at off hoff htag


theorem tailKillTauChunk0198_certificate_at
    (idx : Nat) (hlo : 1980000 ≤ idx) (hhi : idx < 1990000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1980000
  have hlen : tailKillTauChunk0198Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0198Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0198Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0198_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0198_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0198Start + off = idx := by
      dsimp [off]
      change 1980000 + (idx - 1980000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0198_witness_bound_at off hoff htag


theorem tailKillTauChunk0199_certificate_at
    (idx : Nat) (hlo : 1990000 ≤ idx) (hhi : idx < 2000000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 1990000
  have hlen : tailKillTauChunk0199Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0199Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0199Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0199_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0199_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0199Start + off = idx := by
      dsimp [off]
      change 1990000 + (idx - 1990000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0199_witness_bound_at off hoff htag


theorem tailKillTauChunk0200_certificate_at
    (idx : Nat) (hlo : 2000000 ≤ idx) (hhi : idx < 2010000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2000000
  have hlen : tailKillTauChunk0200Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0200Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0200Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0200_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0200_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0200Start + off = idx := by
      dsimp [off]
      change 2000000 + (idx - 2000000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0200_witness_bound_at off hoff htag


theorem tailKillTauChunk0201_certificate_at
    (idx : Nat) (hlo : 2010000 ≤ idx) (hhi : idx < 2020000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2010000
  have hlen : tailKillTauChunk0201Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0201Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0201Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0201_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0201_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0201Start + off = idx := by
      dsimp [off]
      change 2010000 + (idx - 2010000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0201_witness_bound_at off hoff htag


theorem tailKillTauChunk0202_certificate_at
    (idx : Nat) (hlo : 2020000 ≤ idx) (hhi : idx < 2030000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2020000
  have hlen : tailKillTauChunk0202Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0202Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0202Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0202_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0202_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0202Start + off = idx := by
      dsimp [off]
      change 2020000 + (idx - 2020000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0202_witness_bound_at off hoff htag


theorem tailKillTauChunk0203_certificate_at
    (idx : Nat) (hlo : 2030000 ≤ idx) (hhi : idx < 2040000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2030000
  have hlen : tailKillTauChunk0203Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0203Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0203Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0203_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0203_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0203Start + off = idx := by
      dsimp [off]
      change 2030000 + (idx - 2030000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0203_witness_bound_at off hoff htag


theorem tailKillTauChunk0204_certificate_at
    (idx : Nat) (hlo : 2040000 ≤ idx) (hhi : idx < 2050000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2040000
  have hlen : tailKillTauChunk0204Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0204Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0204Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0204_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0204_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0204Start + off = idx := by
      dsimp [off]
      change 2040000 + (idx - 2040000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0204_witness_bound_at off hoff htag


theorem tailKillTauChunk0205_certificate_at
    (idx : Nat) (hlo : 2050000 ≤ idx) (hhi : idx < 2060000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2050000
  have hlen : tailKillTauChunk0205Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0205Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0205Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0205_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0205_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0205Start + off = idx := by
      dsimp [off]
      change 2050000 + (idx - 2050000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0205_witness_bound_at off hoff htag


theorem tailKillTauChunk0206_certificate_at
    (idx : Nat) (hlo : 2060000 ≤ idx) (hhi : idx < 2070000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2060000
  have hlen : tailKillTauChunk0206Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0206Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0206Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0206_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0206_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0206Start + off = idx := by
      dsimp [off]
      change 2060000 + (idx - 2060000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0206_witness_bound_at off hoff htag


theorem tailKillTauChunk0207_certificate_at
    (idx : Nat) (hlo : 2070000 ≤ idx) (hhi : idx < 2080000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2070000
  have hlen : tailKillTauChunk0207Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0207Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0207Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0207_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0207_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0207Start + off = idx := by
      dsimp [off]
      change 2070000 + (idx - 2070000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0207_witness_bound_at off hoff htag


theorem tailKillTauChunk0208_certificate_at
    (idx : Nat) (hlo : 2080000 ≤ idx) (hhi : idx < 2090000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2080000
  have hlen : tailKillTauChunk0208Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0208Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0208Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0208_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0208_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0208Start + off = idx := by
      dsimp [off]
      change 2080000 + (idx - 2080000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0208_witness_bound_at off hoff htag


theorem tailKillTauChunk0209_certificate_at
    (idx : Nat) (hlo : 2090000 ≤ idx) (hhi : idx < 2100000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2090000
  have hlen : tailKillTauChunk0209Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0209Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0209Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0209_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0209_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0209Start + off = idx := by
      dsimp [off]
      change 2090000 + (idx - 2090000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0209_witness_bound_at off hoff htag


theorem tailKillTauChunk0210_certificate_at
    (idx : Nat) (hlo : 2100000 ≤ idx) (hhi : idx < 2110000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2100000
  have hlen : tailKillTauChunk0210Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0210Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0210Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0210_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0210_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0210Start + off = idx := by
      dsimp [off]
      change 2100000 + (idx - 2100000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0210_witness_bound_at off hoff htag


theorem tailKillTauChunk0211_certificate_at
    (idx : Nat) (hlo : 2110000 ≤ idx) (hhi : idx < 2120000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2110000
  have hlen : tailKillTauChunk0211Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0211Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0211Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0211_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0211_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0211Start + off = idx := by
      dsimp [off]
      change 2110000 + (idx - 2110000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0211_witness_bound_at off hoff htag


theorem tailKillTauChunk0212_certificate_at
    (idx : Nat) (hlo : 2120000 ≤ idx) (hhi : idx < 2130000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2120000
  have hlen : tailKillTauChunk0212Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0212Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0212Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0212_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0212_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0212Start + off = idx := by
      dsimp [off]
      change 2120000 + (idx - 2120000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0212_witness_bound_at off hoff htag


theorem tailKillTauChunk0213_certificate_at
    (idx : Nat) (hlo : 2130000 ≤ idx) (hhi : idx < 2140000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2130000
  have hlen : tailKillTauChunk0213Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0213Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0213Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0213_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0213_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0213Start + off = idx := by
      dsimp [off]
      change 2130000 + (idx - 2130000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0213_witness_bound_at off hoff htag


theorem tailKillTauChunk0214_certificate_at
    (idx : Nat) (hlo : 2140000 ≤ idx) (hhi : idx < 2150000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2140000
  have hlen : tailKillTauChunk0214Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0214Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0214Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0214_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0214_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0214Start + off = idx := by
      dsimp [off]
      change 2140000 + (idx - 2140000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0214_witness_bound_at off hoff htag


theorem tailKillTauChunk0215_certificate_at
    (idx : Nat) (hlo : 2150000 ≤ idx) (hhi : idx < 2160000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2150000
  have hlen : tailKillTauChunk0215Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0215Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0215Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0215_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0215_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0215Start + off = idx := by
      dsimp [off]
      change 2150000 + (idx - 2150000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0215_witness_bound_at off hoff htag


theorem tailKillTauChunk0216_certificate_at
    (idx : Nat) (hlo : 2160000 ≤ idx) (hhi : idx < 2170000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2160000
  have hlen : tailKillTauChunk0216Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0216Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0216Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0216_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0216_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0216Start + off = idx := by
      dsimp [off]
      change 2160000 + (idx - 2160000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0216_witness_bound_at off hoff htag


theorem tailKillTauChunk0217_certificate_at
    (idx : Nat) (hlo : 2170000 ≤ idx) (hhi : idx < 2180000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2170000
  have hlen : tailKillTauChunk0217Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0217Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0217Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0217_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0217_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0217Start + off = idx := by
      dsimp [off]
      change 2170000 + (idx - 2170000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0217_witness_bound_at off hoff htag


theorem tailKillTauChunk0218_certificate_at
    (idx : Nat) (hlo : 2180000 ≤ idx) (hhi : idx < 2190000) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2180000
  have hlen : tailKillTauChunk0218Rows.length = 10000 := by
    decide
  have hoff : off < tailKillTauChunk0218Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0218Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0218_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0218_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0218Start + off = idx := by
      dsimp [off]
      change 2180000 + (idx - 2180000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0218_witness_bound_at off hoff htag


theorem tailKillTauChunk0219_certificate_at
    (idx : Nat) (hlo : 2190000 ≤ idx) (hhi : idx < 2190589) :
    TailKillTauFinitePrefixCertificateAt idx := by
  let off := idx - 2190000
  have hlen : tailKillTauChunk0219Rows.length = 589 := by
    decide
  have hoff : off < tailKillTauChunk0219Rows.length := by
    dsimp [off]
    rw [hlen]
    omega
  refine ⟨tailKillTauChunk0219Rows[off], ?_, ?_, ?_⟩
  · exact tailKillTauChunk0219_row_valid_at off hoff
  · have hmatch := tailKillTauChunk0219_row_matches_at off hoff
    have hidxeq : tailKillTauChunk0219Start + off = idx := by
      dsimp [off]
      change 2190000 + (idx - 2190000) = idx
      omega
    simpa [hidxeq] using hmatch
  · intro htag
    exact tailKillTauChunk0219_witness_bound_at off hoff htag


theorem tailKillTauFinitePrefix_certificate_at
    (idx : Nat) (hidx : idx < finitePrefixDomainSize) :
    TailKillTauFinitePrefixCertificateAt idx := by
  have hdomain : idx < 2190589 := by
    simpa [finitePrefixDomainSize] using hidx
  by_cases h0000 : idx < 10000
  · exact tailKillTauChunk0000_certificate_at idx (by omega) h0000
  ·
    by_cases h0001 : idx < 20000
    · exact tailKillTauChunk0001_certificate_at idx (by omega) h0001
    ·
      by_cases h0002 : idx < 30000
      · exact tailKillTauChunk0002_certificate_at idx (by omega) h0002
      ·
        by_cases h0003 : idx < 40000
        · exact tailKillTauChunk0003_certificate_at idx (by omega) h0003
        ·
          by_cases h0004 : idx < 50000
          · exact tailKillTauChunk0004_certificate_at idx (by omega) h0004
          ·
            by_cases h0005 : idx < 60000
            · exact tailKillTauChunk0005_certificate_at idx (by omega) h0005
            ·
              by_cases h0006 : idx < 70000
              · exact tailKillTauChunk0006_certificate_at idx (by omega) h0006
              ·
                by_cases h0007 : idx < 80000
                · exact tailKillTauChunk0007_certificate_at idx (by omega) h0007
                ·
                  by_cases h0008 : idx < 90000
                  · exact tailKillTauChunk0008_certificate_at idx (by omega) h0008
                  ·
                    by_cases h0009 : idx < 100000
                    · exact tailKillTauChunk0009_certificate_at idx (by omega) h0009
                    ·
                      by_cases h0010 : idx < 110000
                      · exact tailKillTauChunk0010_certificate_at idx (by omega) h0010
                      ·
                        by_cases h0011 : idx < 120000
                        · exact tailKillTauChunk0011_certificate_at idx (by omega) h0011
                        ·
                          by_cases h0012 : idx < 130000
                          · exact tailKillTauChunk0012_certificate_at idx (by omega) h0012
                          ·
                            by_cases h0013 : idx < 140000
                            · exact tailKillTauChunk0013_certificate_at idx (by omega) h0013
                            ·
                              by_cases h0014 : idx < 150000
                              · exact tailKillTauChunk0014_certificate_at idx (by omega) h0014
                              ·
                                by_cases h0015 : idx < 160000
                                · exact tailKillTauChunk0015_certificate_at idx (by omega) h0015
                                ·
                                  by_cases h0016 : idx < 170000
                                  · exact tailKillTauChunk0016_certificate_at idx (by omega) h0016
                                  ·
                                    by_cases h0017 : idx < 180000
                                    · exact tailKillTauChunk0017_certificate_at idx (by omega) h0017
                                    ·
                                      by_cases h0018 : idx < 190000
                                      · exact tailKillTauChunk0018_certificate_at idx (by omega) h0018
                                      ·
                                        by_cases h0019 : idx < 200000
                                        · exact tailKillTauChunk0019_certificate_at idx (by omega) h0019
                                        ·
                                          by_cases h0020 : idx < 210000
                                          · exact tailKillTauChunk0020_certificate_at idx (by omega) h0020
                                          ·
                                            by_cases h0021 : idx < 220000
                                            · exact tailKillTauChunk0021_certificate_at idx (by omega) h0021
                                            ·
                                              by_cases h0022 : idx < 230000
                                              · exact tailKillTauChunk0022_certificate_at idx (by omega) h0022
                                              ·
                                                by_cases h0023 : idx < 240000
                                                · exact tailKillTauChunk0023_certificate_at idx (by omega) h0023
                                                ·
                                                  by_cases h0024 : idx < 250000
                                                  · exact tailKillTauChunk0024_certificate_at idx (by omega) h0024
                                                  ·
                                                    by_cases h0025 : idx < 260000
                                                    · exact tailKillTauChunk0025_certificate_at idx (by omega) h0025
                                                    ·
                                                      by_cases h0026 : idx < 270000
                                                      · exact tailKillTauChunk0026_certificate_at idx (by omega) h0026
                                                      ·
                                                        by_cases h0027 : idx < 280000
                                                        · exact tailKillTauChunk0027_certificate_at idx (by omega) h0027
                                                        ·
                                                          by_cases h0028 : idx < 290000
                                                          · exact tailKillTauChunk0028_certificate_at idx (by omega) h0028
                                                          ·
                                                            by_cases h0029 : idx < 300000
                                                            · exact tailKillTauChunk0029_certificate_at idx (by omega) h0029
                                                            ·
                                                              by_cases h0030 : idx < 310000
                                                              · exact tailKillTauChunk0030_certificate_at idx (by omega) h0030
                                                              ·
                                                                by_cases h0031 : idx < 320000
                                                                · exact tailKillTauChunk0031_certificate_at idx (by omega) h0031
                                                                ·
                                                                  by_cases h0032 : idx < 330000
                                                                  · exact tailKillTauChunk0032_certificate_at idx (by omega) h0032
                                                                  ·
                                                                    by_cases h0033 : idx < 340000
                                                                    · exact tailKillTauChunk0033_certificate_at idx (by omega) h0033
                                                                    ·
                                                                      by_cases h0034 : idx < 350000
                                                                      · exact tailKillTauChunk0034_certificate_at idx (by omega) h0034
                                                                      ·
                                                                        by_cases h0035 : idx < 360000
                                                                        · exact tailKillTauChunk0035_certificate_at idx (by omega) h0035
                                                                        ·
                                                                          by_cases h0036 : idx < 370000
                                                                          · exact tailKillTauChunk0036_certificate_at idx (by omega) h0036
                                                                          ·
                                                                            by_cases h0037 : idx < 380000
                                                                            · exact tailKillTauChunk0037_certificate_at idx (by omega) h0037
                                                                            ·
                                                                              by_cases h0038 : idx < 390000
                                                                              · exact tailKillTauChunk0038_certificate_at idx (by omega) h0038
                                                                              ·
                                                                                by_cases h0039 : idx < 400000
                                                                                · exact tailKillTauChunk0039_certificate_at idx (by omega) h0039
                                                                                ·
                                                                                  by_cases h0040 : idx < 410000
                                                                                  · exact tailKillTauChunk0040_certificate_at idx (by omega) h0040
                                                                                  ·
                                                                                    by_cases h0041 : idx < 420000
                                                                                    · exact tailKillTauChunk0041_certificate_at idx (by omega) h0041
                                                                                    ·
                                                                                      by_cases h0042 : idx < 430000
                                                                                      · exact tailKillTauChunk0042_certificate_at idx (by omega) h0042
                                                                                      ·
                                                                                        by_cases h0043 : idx < 440000
                                                                                        · exact tailKillTauChunk0043_certificate_at idx (by omega) h0043
                                                                                        ·
                                                                                          by_cases h0044 : idx < 450000
                                                                                          · exact tailKillTauChunk0044_certificate_at idx (by omega) h0044
                                                                                          ·
                                                                                            by_cases h0045 : idx < 460000
                                                                                            · exact tailKillTauChunk0045_certificate_at idx (by omega) h0045
                                                                                            ·
                                                                                              by_cases h0046 : idx < 470000
                                                                                              · exact tailKillTauChunk0046_certificate_at idx (by omega) h0046
                                                                                              ·
                                                                                                by_cases h0047 : idx < 480000
                                                                                                · exact tailKillTauChunk0047_certificate_at idx (by omega) h0047
                                                                                                ·
                                                                                                  by_cases h0048 : idx < 490000
                                                                                                  · exact tailKillTauChunk0048_certificate_at idx (by omega) h0048
                                                                                                  ·
                                                                                                    by_cases h0049 : idx < 500000
                                                                                                    · exact tailKillTauChunk0049_certificate_at idx (by omega) h0049
                                                                                                    ·
                                                                                                      by_cases h0050 : idx < 510000
                                                                                                      · exact tailKillTauChunk0050_certificate_at idx (by omega) h0050
                                                                                                      ·
                                                                                                        by_cases h0051 : idx < 520000
                                                                                                        · exact tailKillTauChunk0051_certificate_at idx (by omega) h0051
                                                                                                        ·
                                                                                                          by_cases h0052 : idx < 530000
                                                                                                          · exact tailKillTauChunk0052_certificate_at idx (by omega) h0052
                                                                                                          ·
                                                                                                            by_cases h0053 : idx < 540000
                                                                                                            · exact tailKillTauChunk0053_certificate_at idx (by omega) h0053
                                                                                                            ·
                                                                                                              by_cases h0054 : idx < 550000
                                                                                                              · exact tailKillTauChunk0054_certificate_at idx (by omega) h0054
                                                                                                              ·
                                                                                                                by_cases h0055 : idx < 560000
                                                                                                                · exact tailKillTauChunk0055_certificate_at idx (by omega) h0055
                                                                                                                ·
                                                                                                                  by_cases h0056 : idx < 570000
                                                                                                                  · exact tailKillTauChunk0056_certificate_at idx (by omega) h0056
                                                                                                                  ·
                                                                                                                    by_cases h0057 : idx < 580000
                                                                                                                    · exact tailKillTauChunk0057_certificate_at idx (by omega) h0057
                                                                                                                    ·
                                                                                                                      by_cases h0058 : idx < 590000
                                                                                                                      · exact tailKillTauChunk0058_certificate_at idx (by omega) h0058
                                                                                                                      ·
                                                                                                                        by_cases h0059 : idx < 600000
                                                                                                                        · exact tailKillTauChunk0059_certificate_at idx (by omega) h0059
                                                                                                                        ·
                                                                                                                          by_cases h0060 : idx < 610000
                                                                                                                          · exact tailKillTauChunk0060_certificate_at idx (by omega) h0060
                                                                                                                          ·
                                                                                                                            by_cases h0061 : idx < 620000
                                                                                                                            · exact tailKillTauChunk0061_certificate_at idx (by omega) h0061
                                                                                                                            ·
                                                                                                                              by_cases h0062 : idx < 630000
                                                                                                                              · exact tailKillTauChunk0062_certificate_at idx (by omega) h0062
                                                                                                                              ·
                                                                                                                                by_cases h0063 : idx < 640000
                                                                                                                                · exact tailKillTauChunk0063_certificate_at idx (by omega) h0063
                                                                                                                                ·
                                                                                                                                  by_cases h0064 : idx < 650000
                                                                                                                                  · exact tailKillTauChunk0064_certificate_at idx (by omega) h0064
                                                                                                                                  ·
                                                                                                                                    by_cases h0065 : idx < 660000
                                                                                                                                    · exact tailKillTauChunk0065_certificate_at idx (by omega) h0065
                                                                                                                                    ·
                                                                                                                                      by_cases h0066 : idx < 670000
                                                                                                                                      · exact tailKillTauChunk0066_certificate_at idx (by omega) h0066
                                                                                                                                      ·
                                                                                                                                        by_cases h0067 : idx < 680000
                                                                                                                                        · exact tailKillTauChunk0067_certificate_at idx (by omega) h0067
                                                                                                                                        ·
                                                                                                                                          by_cases h0068 : idx < 690000
                                                                                                                                          · exact tailKillTauChunk0068_certificate_at idx (by omega) h0068
                                                                                                                                          ·
                                                                                                                                            by_cases h0069 : idx < 700000
                                                                                                                                            · exact tailKillTauChunk0069_certificate_at idx (by omega) h0069
                                                                                                                                            ·
                                                                                                                                              by_cases h0070 : idx < 710000
                                                                                                                                              · exact tailKillTauChunk0070_certificate_at idx (by omega) h0070
                                                                                                                                              ·
                                                                                                                                                by_cases h0071 : idx < 720000
                                                                                                                                                · exact tailKillTauChunk0071_certificate_at idx (by omega) h0071
                                                                                                                                                ·
                                                                                                                                                  by_cases h0072 : idx < 730000
                                                                                                                                                  · exact tailKillTauChunk0072_certificate_at idx (by omega) h0072
                                                                                                                                                  ·
                                                                                                                                                    by_cases h0073 : idx < 740000
                                                                                                                                                    · exact tailKillTauChunk0073_certificate_at idx (by omega) h0073
                                                                                                                                                    ·
                                                                                                                                                      by_cases h0074 : idx < 750000
                                                                                                                                                      · exact tailKillTauChunk0074_certificate_at idx (by omega) h0074
                                                                                                                                                      ·
                                                                                                                                                        by_cases h0075 : idx < 760000
                                                                                                                                                        · exact tailKillTauChunk0075_certificate_at idx (by omega) h0075
                                                                                                                                                        ·
                                                                                                                                                          by_cases h0076 : idx < 770000
                                                                                                                                                          · exact tailKillTauChunk0076_certificate_at idx (by omega) h0076
                                                                                                                                                          ·
                                                                                                                                                            by_cases h0077 : idx < 780000
                                                                                                                                                            · exact tailKillTauChunk0077_certificate_at idx (by omega) h0077
                                                                                                                                                            ·
                                                                                                                                                              by_cases h0078 : idx < 790000
                                                                                                                                                              · exact tailKillTauChunk0078_certificate_at idx (by omega) h0078
                                                                                                                                                              ·
                                                                                                                                                                by_cases h0079 : idx < 800000
                                                                                                                                                                · exact tailKillTauChunk0079_certificate_at idx (by omega) h0079
                                                                                                                                                                ·
                                                                                                                                                                  by_cases h0080 : idx < 810000
                                                                                                                                                                  · exact tailKillTauChunk0080_certificate_at idx (by omega) h0080
                                                                                                                                                                  ·
                                                                                                                                                                    by_cases h0081 : idx < 820000
                                                                                                                                                                    · exact tailKillTauChunk0081_certificate_at idx (by omega) h0081
                                                                                                                                                                    ·
                                                                                                                                                                      by_cases h0082 : idx < 830000
                                                                                                                                                                      · exact tailKillTauChunk0082_certificate_at idx (by omega) h0082
                                                                                                                                                                      ·
                                                                                                                                                                        by_cases h0083 : idx < 840000
                                                                                                                                                                        · exact tailKillTauChunk0083_certificate_at idx (by omega) h0083
                                                                                                                                                                        ·
                                                                                                                                                                          by_cases h0084 : idx < 850000
                                                                                                                                                                          · exact tailKillTauChunk0084_certificate_at idx (by omega) h0084
                                                                                                                                                                          ·
                                                                                                                                                                            by_cases h0085 : idx < 860000
                                                                                                                                                                            · exact tailKillTauChunk0085_certificate_at idx (by omega) h0085
                                                                                                                                                                            ·
                                                                                                                                                                              by_cases h0086 : idx < 870000
                                                                                                                                                                              · exact tailKillTauChunk0086_certificate_at idx (by omega) h0086
                                                                                                                                                                              ·
                                                                                                                                                                                by_cases h0087 : idx < 880000
                                                                                                                                                                                · exact tailKillTauChunk0087_certificate_at idx (by omega) h0087
                                                                                                                                                                                ·
                                                                                                                                                                                  by_cases h0088 : idx < 890000
                                                                                                                                                                                  · exact tailKillTauChunk0088_certificate_at idx (by omega) h0088
                                                                                                                                                                                  ·
                                                                                                                                                                                    by_cases h0089 : idx < 900000
                                                                                                                                                                                    · exact tailKillTauChunk0089_certificate_at idx (by omega) h0089
                                                                                                                                                                                    ·
                                                                                                                                                                                      by_cases h0090 : idx < 910000
                                                                                                                                                                                      · exact tailKillTauChunk0090_certificate_at idx (by omega) h0090
                                                                                                                                                                                      ·
                                                                                                                                                                                        by_cases h0091 : idx < 920000
                                                                                                                                                                                        · exact tailKillTauChunk0091_certificate_at idx (by omega) h0091
                                                                                                                                                                                        ·
                                                                                                                                                                                          by_cases h0092 : idx < 930000
                                                                                                                                                                                          · exact tailKillTauChunk0092_certificate_at idx (by omega) h0092
                                                                                                                                                                                          ·
                                                                                                                                                                                            by_cases h0093 : idx < 940000
                                                                                                                                                                                            · exact tailKillTauChunk0093_certificate_at idx (by omega) h0093
                                                                                                                                                                                            ·
                                                                                                                                                                                              by_cases h0094 : idx < 950000
                                                                                                                                                                                              · exact tailKillTauChunk0094_certificate_at idx (by omega) h0094
                                                                                                                                                                                              ·
                                                                                                                                                                                                by_cases h0095 : idx < 960000
                                                                                                                                                                                                · exact tailKillTauChunk0095_certificate_at idx (by omega) h0095
                                                                                                                                                                                                ·
                                                                                                                                                                                                  by_cases h0096 : idx < 970000
                                                                                                                                                                                                  · exact tailKillTauChunk0096_certificate_at idx (by omega) h0096
                                                                                                                                                                                                  ·
                                                                                                                                                                                                    by_cases h0097 : idx < 980000
                                                                                                                                                                                                    · exact tailKillTauChunk0097_certificate_at idx (by omega) h0097
                                                                                                                                                                                                    ·
                                                                                                                                                                                                      by_cases h0098 : idx < 990000
                                                                                                                                                                                                      · exact tailKillTauChunk0098_certificate_at idx (by omega) h0098
                                                                                                                                                                                                      ·
                                                                                                                                                                                                        by_cases h0099 : idx < 1000000
                                                                                                                                                                                                        · exact tailKillTauChunk0099_certificate_at idx (by omega) h0099
                                                                                                                                                                                                        ·
                                                                                                                                                                                                          by_cases h0100 : idx < 1010000
                                                                                                                                                                                                          · exact tailKillTauChunk0100_certificate_at idx (by omega) h0100
                                                                                                                                                                                                          ·
                                                                                                                                                                                                            by_cases h0101 : idx < 1020000
                                                                                                                                                                                                            · exact tailKillTauChunk0101_certificate_at idx (by omega) h0101
                                                                                                                                                                                                            ·
                                                                                                                                                                                                              by_cases h0102 : idx < 1030000
                                                                                                                                                                                                              · exact tailKillTauChunk0102_certificate_at idx (by omega) h0102
                                                                                                                                                                                                              ·
                                                                                                                                                                                                                by_cases h0103 : idx < 1040000
                                                                                                                                                                                                                · exact tailKillTauChunk0103_certificate_at idx (by omega) h0103
                                                                                                                                                                                                                ·
                                                                                                                                                                                                                  by_cases h0104 : idx < 1050000
                                                                                                                                                                                                                  · exact tailKillTauChunk0104_certificate_at idx (by omega) h0104
                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                    by_cases h0105 : idx < 1060000
                                                                                                                                                                                                                    · exact tailKillTauChunk0105_certificate_at idx (by omega) h0105
                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                      by_cases h0106 : idx < 1070000
                                                                                                                                                                                                                      · exact tailKillTauChunk0106_certificate_at idx (by omega) h0106
                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                        by_cases h0107 : idx < 1080000
                                                                                                                                                                                                                        · exact tailKillTauChunk0107_certificate_at idx (by omega) h0107
                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                          by_cases h0108 : idx < 1090000
                                                                                                                                                                                                                          · exact tailKillTauChunk0108_certificate_at idx (by omega) h0108
                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                            by_cases h0109 : idx < 1100000
                                                                                                                                                                                                                            · exact tailKillTauChunk0109_certificate_at idx (by omega) h0109
                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                              by_cases h0110 : idx < 1110000
                                                                                                                                                                                                                              · exact tailKillTauChunk0110_certificate_at idx (by omega) h0110
                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                by_cases h0111 : idx < 1120000
                                                                                                                                                                                                                                · exact tailKillTauChunk0111_certificate_at idx (by omega) h0111
                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                  by_cases h0112 : idx < 1130000
                                                                                                                                                                                                                                  · exact tailKillTauChunk0112_certificate_at idx (by omega) h0112
                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                    by_cases h0113 : idx < 1140000
                                                                                                                                                                                                                                    · exact tailKillTauChunk0113_certificate_at idx (by omega) h0113
                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                      by_cases h0114 : idx < 1150000
                                                                                                                                                                                                                                      · exact tailKillTauChunk0114_certificate_at idx (by omega) h0114
                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                        by_cases h0115 : idx < 1160000
                                                                                                                                                                                                                                        · exact tailKillTauChunk0115_certificate_at idx (by omega) h0115
                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                          by_cases h0116 : idx < 1170000
                                                                                                                                                                                                                                          · exact tailKillTauChunk0116_certificate_at idx (by omega) h0116
                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                            by_cases h0117 : idx < 1180000
                                                                                                                                                                                                                                            · exact tailKillTauChunk0117_certificate_at idx (by omega) h0117
                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                              by_cases h0118 : idx < 1190000
                                                                                                                                                                                                                                              · exact tailKillTauChunk0118_certificate_at idx (by omega) h0118
                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                by_cases h0119 : idx < 1200000
                                                                                                                                                                                                                                                · exact tailKillTauChunk0119_certificate_at idx (by omega) h0119
                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                  by_cases h0120 : idx < 1210000
                                                                                                                                                                                                                                                  · exact tailKillTauChunk0120_certificate_at idx (by omega) h0120
                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                    by_cases h0121 : idx < 1220000
                                                                                                                                                                                                                                                    · exact tailKillTauChunk0121_certificate_at idx (by omega) h0121
                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                      by_cases h0122 : idx < 1230000
                                                                                                                                                                                                                                                      · exact tailKillTauChunk0122_certificate_at idx (by omega) h0122
                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                        by_cases h0123 : idx < 1240000
                                                                                                                                                                                                                                                        · exact tailKillTauChunk0123_certificate_at idx (by omega) h0123
                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                          by_cases h0124 : idx < 1250000
                                                                                                                                                                                                                                                          · exact tailKillTauChunk0124_certificate_at idx (by omega) h0124
                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                            by_cases h0125 : idx < 1260000
                                                                                                                                                                                                                                                            · exact tailKillTauChunk0125_certificate_at idx (by omega) h0125
                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                              by_cases h0126 : idx < 1270000
                                                                                                                                                                                                                                                              · exact tailKillTauChunk0126_certificate_at idx (by omega) h0126
                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                by_cases h0127 : idx < 1280000
                                                                                                                                                                                                                                                                · exact tailKillTauChunk0127_certificate_at idx (by omega) h0127
                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                  by_cases h0128 : idx < 1290000
                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0128_certificate_at idx (by omega) h0128
                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                    by_cases h0129 : idx < 1300000
                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0129_certificate_at idx (by omega) h0129
                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                      by_cases h0130 : idx < 1310000
                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0130_certificate_at idx (by omega) h0130
                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                        by_cases h0131 : idx < 1320000
                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0131_certificate_at idx (by omega) h0131
                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                          by_cases h0132 : idx < 1330000
                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0132_certificate_at idx (by omega) h0132
                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                            by_cases h0133 : idx < 1340000
                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0133_certificate_at idx (by omega) h0133
                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                              by_cases h0134 : idx < 1350000
                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0134_certificate_at idx (by omega) h0134
                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                by_cases h0135 : idx < 1360000
                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0135_certificate_at idx (by omega) h0135
                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                  by_cases h0136 : idx < 1370000
                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0136_certificate_at idx (by omega) h0136
                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                    by_cases h0137 : idx < 1380000
                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0137_certificate_at idx (by omega) h0137
                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                      by_cases h0138 : idx < 1390000
                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0138_certificate_at idx (by omega) h0138
                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                        by_cases h0139 : idx < 1400000
                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0139_certificate_at idx (by omega) h0139
                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                          by_cases h0140 : idx < 1410000
                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0140_certificate_at idx (by omega) h0140
                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                            by_cases h0141 : idx < 1420000
                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0141_certificate_at idx (by omega) h0141
                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                              by_cases h0142 : idx < 1430000
                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0142_certificate_at idx (by omega) h0142
                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                by_cases h0143 : idx < 1440000
                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0143_certificate_at idx (by omega) h0143
                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                  by_cases h0144 : idx < 1450000
                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0144_certificate_at idx (by omega) h0144
                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                    by_cases h0145 : idx < 1460000
                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0145_certificate_at idx (by omega) h0145
                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                      by_cases h0146 : idx < 1470000
                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0146_certificate_at idx (by omega) h0146
                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                        by_cases h0147 : idx < 1480000
                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0147_certificate_at idx (by omega) h0147
                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                          by_cases h0148 : idx < 1490000
                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0148_certificate_at idx (by omega) h0148
                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                            by_cases h0149 : idx < 1500000
                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0149_certificate_at idx (by omega) h0149
                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                              by_cases h0150 : idx < 1510000
                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0150_certificate_at idx (by omega) h0150
                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                by_cases h0151 : idx < 1520000
                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0151_certificate_at idx (by omega) h0151
                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                  by_cases h0152 : idx < 1530000
                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0152_certificate_at idx (by omega) h0152
                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                    by_cases h0153 : idx < 1540000
                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0153_certificate_at idx (by omega) h0153
                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                      by_cases h0154 : idx < 1550000
                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0154_certificate_at idx (by omega) h0154
                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                        by_cases h0155 : idx < 1560000
                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0155_certificate_at idx (by omega) h0155
                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                          by_cases h0156 : idx < 1570000
                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0156_certificate_at idx (by omega) h0156
                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                            by_cases h0157 : idx < 1580000
                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0157_certificate_at idx (by omega) h0157
                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                              by_cases h0158 : idx < 1590000
                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0158_certificate_at idx (by omega) h0158
                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                by_cases h0159 : idx < 1600000
                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0159_certificate_at idx (by omega) h0159
                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                  by_cases h0160 : idx < 1610000
                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0160_certificate_at idx (by omega) h0160
                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                    by_cases h0161 : idx < 1620000
                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0161_certificate_at idx (by omega) h0161
                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                      by_cases h0162 : idx < 1630000
                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0162_certificate_at idx (by omega) h0162
                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                        by_cases h0163 : idx < 1640000
                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0163_certificate_at idx (by omega) h0163
                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                          by_cases h0164 : idx < 1650000
                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0164_certificate_at idx (by omega) h0164
                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                            by_cases h0165 : idx < 1660000
                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0165_certificate_at idx (by omega) h0165
                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                              by_cases h0166 : idx < 1670000
                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0166_certificate_at idx (by omega) h0166
                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                by_cases h0167 : idx < 1680000
                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0167_certificate_at idx (by omega) h0167
                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                  by_cases h0168 : idx < 1690000
                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0168_certificate_at idx (by omega) h0168
                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                    by_cases h0169 : idx < 1700000
                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0169_certificate_at idx (by omega) h0169
                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                      by_cases h0170 : idx < 1710000
                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0170_certificate_at idx (by omega) h0170
                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                        by_cases h0171 : idx < 1720000
                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0171_certificate_at idx (by omega) h0171
                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                          by_cases h0172 : idx < 1730000
                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0172_certificate_at idx (by omega) h0172
                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                            by_cases h0173 : idx < 1740000
                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0173_certificate_at idx (by omega) h0173
                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                              by_cases h0174 : idx < 1750000
                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0174_certificate_at idx (by omega) h0174
                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                by_cases h0175 : idx < 1760000
                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0175_certificate_at idx (by omega) h0175
                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                  by_cases h0176 : idx < 1770000
                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0176_certificate_at idx (by omega) h0176
                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                    by_cases h0177 : idx < 1780000
                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0177_certificate_at idx (by omega) h0177
                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                      by_cases h0178 : idx < 1790000
                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0178_certificate_at idx (by omega) h0178
                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                        by_cases h0179 : idx < 1800000
                                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0179_certificate_at idx (by omega) h0179
                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                          by_cases h0180 : idx < 1810000
                                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0180_certificate_at idx (by omega) h0180
                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                            by_cases h0181 : idx < 1820000
                                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0181_certificate_at idx (by omega) h0181
                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                              by_cases h0182 : idx < 1830000
                                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0182_certificate_at idx (by omega) h0182
                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                by_cases h0183 : idx < 1840000
                                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0183_certificate_at idx (by omega) h0183
                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                  by_cases h0184 : idx < 1850000
                                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0184_certificate_at idx (by omega) h0184
                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                    by_cases h0185 : idx < 1860000
                                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0185_certificate_at idx (by omega) h0185
                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                      by_cases h0186 : idx < 1870000
                                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0186_certificate_at idx (by omega) h0186
                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                        by_cases h0187 : idx < 1880000
                                                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0187_certificate_at idx (by omega) h0187
                                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                                          by_cases h0188 : idx < 1890000
                                                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0188_certificate_at idx (by omega) h0188
                                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                                            by_cases h0189 : idx < 1900000
                                                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0189_certificate_at idx (by omega) h0189
                                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                                              by_cases h0190 : idx < 1910000
                                                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0190_certificate_at idx (by omega) h0190
                                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                                by_cases h0191 : idx < 1920000
                                                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0191_certificate_at idx (by omega) h0191
                                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                                  by_cases h0192 : idx < 1930000
                                                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0192_certificate_at idx (by omega) h0192
                                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                                    by_cases h0193 : idx < 1940000
                                                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0193_certificate_at idx (by omega) h0193
                                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                                      by_cases h0194 : idx < 1950000
                                                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0194_certificate_at idx (by omega) h0194
                                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                                        by_cases h0195 : idx < 1960000
                                                                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0195_certificate_at idx (by omega) h0195
                                                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                                                          by_cases h0196 : idx < 1970000
                                                                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0196_certificate_at idx (by omega) h0196
                                                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                                                            by_cases h0197 : idx < 1980000
                                                                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0197_certificate_at idx (by omega) h0197
                                                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                                                              by_cases h0198 : idx < 1990000
                                                                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0198_certificate_at idx (by omega) h0198
                                                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                                                by_cases h0199 : idx < 2000000
                                                                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0199_certificate_at idx (by omega) h0199
                                                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                                                  by_cases h0200 : idx < 2010000
                                                                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0200_certificate_at idx (by omega) h0200
                                                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                                                    by_cases h0201 : idx < 2020000
                                                                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0201_certificate_at idx (by omega) h0201
                                                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                                                      by_cases h0202 : idx < 2030000
                                                                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0202_certificate_at idx (by omega) h0202
                                                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                                                        by_cases h0203 : idx < 2040000
                                                                                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0203_certificate_at idx (by omega) h0203
                                                                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                                                                          by_cases h0204 : idx < 2050000
                                                                                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0204_certificate_at idx (by omega) h0204
                                                                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                                                                            by_cases h0205 : idx < 2060000
                                                                                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0205_certificate_at idx (by omega) h0205
                                                                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                                                                              by_cases h0206 : idx < 2070000
                                                                                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0206_certificate_at idx (by omega) h0206
                                                                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                                                                by_cases h0207 : idx < 2080000
                                                                                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0207_certificate_at idx (by omega) h0207
                                                                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                                                                  by_cases h0208 : idx < 2090000
                                                                                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0208_certificate_at idx (by omega) h0208
                                                                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                                                                    by_cases h0209 : idx < 2100000
                                                                                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0209_certificate_at idx (by omega) h0209
                                                                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                                                                      by_cases h0210 : idx < 2110000
                                                                                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0210_certificate_at idx (by omega) h0210
                                                                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                                                                        by_cases h0211 : idx < 2120000
                                                                                                                                                                                                                                                                                                                                                                                                                                        · exact tailKillTauChunk0211_certificate_at idx (by omega) h0211
                                                                                                                                                                                                                                                                                                                                                                                                                                        ·
                                                                                                                                                                                                                                                                                                                                                                                                                                          by_cases h0212 : idx < 2130000
                                                                                                                                                                                                                                                                                                                                                                                                                                          · exact tailKillTauChunk0212_certificate_at idx (by omega) h0212
                                                                                                                                                                                                                                                                                                                                                                                                                                          ·
                                                                                                                                                                                                                                                                                                                                                                                                                                            by_cases h0213 : idx < 2140000
                                                                                                                                                                                                                                                                                                                                                                                                                                            · exact tailKillTauChunk0213_certificate_at idx (by omega) h0213
                                                                                                                                                                                                                                                                                                                                                                                                                                            ·
                                                                                                                                                                                                                                                                                                                                                                                                                                              by_cases h0214 : idx < 2150000
                                                                                                                                                                                                                                                                                                                                                                                                                                              · exact tailKillTauChunk0214_certificate_at idx (by omega) h0214
                                                                                                                                                                                                                                                                                                                                                                                                                                              ·
                                                                                                                                                                                                                                                                                                                                                                                                                                                by_cases h0215 : idx < 2160000
                                                                                                                                                                                                                                                                                                                                                                                                                                                · exact tailKillTauChunk0215_certificate_at idx (by omega) h0215
                                                                                                                                                                                                                                                                                                                                                                                                                                                ·
                                                                                                                                                                                                                                                                                                                                                                                                                                                  by_cases h0216 : idx < 2170000
                                                                                                                                                                                                                                                                                                                                                                                                                                                  · exact tailKillTauChunk0216_certificate_at idx (by omega) h0216
                                                                                                                                                                                                                                                                                                                                                                                                                                                  ·
                                                                                                                                                                                                                                                                                                                                                                                                                                                    by_cases h0217 : idx < 2180000
                                                                                                                                                                                                                                                                                                                                                                                                                                                    · exact tailKillTauChunk0217_certificate_at idx (by omega) h0217
                                                                                                                                                                                                                                                                                                                                                                                                                                                    ·
                                                                                                                                                                                                                                                                                                                                                                                                                                                      by_cases h0218 : idx < 2190000
                                                                                                                                                                                                                                                                                                                                                                                                                                                      · exact tailKillTauChunk0218_certificate_at idx (by omega) h0218
                                                                                                                                                                                                                                                                                                                                                                                                                                                      ·
                                                                                                                                                                                                                                                                                                                                                                                                                                                        exact tailKillTauChunk0219_certificate_at idx (by omega) hdomain

theorem tailKillFinitePrefix_prime_implies_mechanismWitness
    {r s u : Nat}
    (hOpen : r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1)
    (hs : s < Erdos647ShiftedPrimeChannel.subAPMod)
    (hu : u < finitePrefixUCount)
    (hPrime : Nat.Prime (Erdos647ShiftedPrimeChannel.F1 r s u)) :
    ShiftedPrimeMechanismWitness
      (fun _ _ _ => finitePrefixWitnessBound) ⟨r, s⟩ u := by
  rcases residueIndex?_some_of_openResiduesStage1_no_native hOpen with
    ⟨ri, hri, _hri_lookup, hri_value⟩
  have hsPrefix : s < finitePrefixSCount := by
    simpa [finitePrefixSCount, Erdos647ShiftedPrimeChannel.subAPMod] using hs
  let idx := globalIndexOfResidueIndex ri s u
  have hidx : idx < finitePrefixDomainSize :=
    globalIndexOfResidueIndex_lt hri hsPrefix hu
  rcases tailKillTauFinitePrefix_certificate_at idx hidx with
    ⟨row, hvalid, hmatch, hbound⟩
  rcases rowMatchesGlobalIndex_true hmatch with ⟨hr0, hs0, hu0⟩
  have heri :
      expectedResidueIndexOfGlobal idx = ri := by
    dsimp [idx]
    exact expectedResidueIndexOfGlobal_globalIndex hri hsPrefix hu
  have hes :
      expectedSOfGlobal idx = s := by
    dsimp [idx]
    exact expectedSOfGlobal_globalIndex hri hsPrefix hu
  have heu :
      expectedUOfGlobal idx = u := by
    dsimp [idx]
    exact expectedUOfGlobal_globalIndex hri hsPrefix hu
  have hr : row.r = r := by
    calc
      row.r = openResidueAt (expectedResidueIndexOfGlobal idx) := hr0
      _ = openResidueAt ri := by rw [heri]
      _ = r := hri_value
  have hsrow : row.s = s := by
    calc
      row.s = expectedSOfGlobal idx := hs0
      _ = s := hes
  have hurow : row.u = u := by
    calc
      row.u = expectedUOfGlobal idx := hu0
      _ = u := heu
  exact row_valid_prime_mechanismWitness hvalid hr hsrow hurow hbound hPrime

theorem tailKillFinitePrefixMechanismVerified :
    FinitePrefixMechanismVerifiedBy
      (fun _ _ _ => finitePrefixWitnessBound)
      (fun _ _ => finitePrefixUCount) := by
  intro r s u hOpen hs _hlarge hu hPrime
  exact tailKillFinitePrefix_prime_implies_mechanismWitness hOpen hs hu hPrime

end FinitePrefixMechanism
end Erdos647TailKillTauProofChunks
