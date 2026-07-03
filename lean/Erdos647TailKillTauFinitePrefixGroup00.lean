import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0000
import Erdos647TailKillTauProofChunks.Chunk0001
import Erdos647TailKillTauProofChunks.Chunk0002
import Erdos647TailKillTauProofChunks.Chunk0003
import Erdos647TailKillTauProofChunks.Chunk0004
import Erdos647TailKillTauProofChunks.Chunk0005
import Erdos647TailKillTauProofChunks.Chunk0006
import Erdos647TailKillTauProofChunks.Chunk0007
import Erdos647TailKillTauProofChunks.Chunk0008
import Erdos647TailKillTauProofChunks.Chunk0009

/-!
# TailKill tau finite-prefix chunk interfaces, group 00

This module proves per-production-chunk row-order and witness-bound facts for
the finite-prefix semantic composition layer.  It does not prove the
finite-prefix, eventual-u, local-layer, shifted-prime, or global theorem
surfaces.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace Erdos647TailKillTauProofChunks
namespace FinitePrefixChunkInterfaces

open FinitePrefixSemantic

def tailKillTauChunk0000RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0000Start tailKillTauChunk0000Rows

theorem tailKillTauChunk0000_rows_match :
    tailKillTauChunk0000RowsMatch = true := by
  decide

def tailKillTauChunk0000WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0000Rows

theorem tailKillTauChunk0000_witness_bound_ok :
    tailKillTauChunk0000WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0000_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0000Rows.length) :
    RowValid tailKillTauChunk0000Rows[off] :=
  tailKillTauChunk0000_row_valid tailKillTauChunk0000Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0000_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0000Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0000Rows[off] (tailKillTauChunk0000Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0000_rows_match off hoff

theorem tailKillTauChunk0000_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0000Rows.length)
    (htag : tailKillTauChunk0000Rows[off].tag = 2) :
    tailKillTauChunk0000Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0000_witness_bound_ok off hoff htag


def tailKillTauChunk0001RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0001Start tailKillTauChunk0001Rows

theorem tailKillTauChunk0001_rows_match :
    tailKillTauChunk0001RowsMatch = true := by
  decide

def tailKillTauChunk0001WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0001Rows

theorem tailKillTauChunk0001_witness_bound_ok :
    tailKillTauChunk0001WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0001_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0001Rows.length) :
    RowValid tailKillTauChunk0001Rows[off] :=
  tailKillTauChunk0001_row_valid tailKillTauChunk0001Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0001_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0001Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0001Rows[off] (tailKillTauChunk0001Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0001_rows_match off hoff

theorem tailKillTauChunk0001_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0001Rows.length)
    (htag : tailKillTauChunk0001Rows[off].tag = 2) :
    tailKillTauChunk0001Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0001_witness_bound_ok off hoff htag


def tailKillTauChunk0002RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0002Start tailKillTauChunk0002Rows

theorem tailKillTauChunk0002_rows_match :
    tailKillTauChunk0002RowsMatch = true := by
  decide

def tailKillTauChunk0002WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0002Rows

theorem tailKillTauChunk0002_witness_bound_ok :
    tailKillTauChunk0002WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0002_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0002Rows.length) :
    RowValid tailKillTauChunk0002Rows[off] :=
  tailKillTauChunk0002_row_valid tailKillTauChunk0002Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0002_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0002Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0002Rows[off] (tailKillTauChunk0002Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0002_rows_match off hoff

theorem tailKillTauChunk0002_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0002Rows.length)
    (htag : tailKillTauChunk0002Rows[off].tag = 2) :
    tailKillTauChunk0002Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0002_witness_bound_ok off hoff htag


def tailKillTauChunk0003RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0003Start tailKillTauChunk0003Rows

theorem tailKillTauChunk0003_rows_match :
    tailKillTauChunk0003RowsMatch = true := by
  decide

def tailKillTauChunk0003WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0003Rows

theorem tailKillTauChunk0003_witness_bound_ok :
    tailKillTauChunk0003WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0003_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0003Rows.length) :
    RowValid tailKillTauChunk0003Rows[off] :=
  tailKillTauChunk0003_row_valid tailKillTauChunk0003Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0003_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0003Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0003Rows[off] (tailKillTauChunk0003Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0003_rows_match off hoff

theorem tailKillTauChunk0003_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0003Rows.length)
    (htag : tailKillTauChunk0003Rows[off].tag = 2) :
    tailKillTauChunk0003Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0003_witness_bound_ok off hoff htag


def tailKillTauChunk0004RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0004Start tailKillTauChunk0004Rows

theorem tailKillTauChunk0004_rows_match :
    tailKillTauChunk0004RowsMatch = true := by
  decide

def tailKillTauChunk0004WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0004Rows

theorem tailKillTauChunk0004_witness_bound_ok :
    tailKillTauChunk0004WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0004_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0004Rows.length) :
    RowValid tailKillTauChunk0004Rows[off] :=
  tailKillTauChunk0004_row_valid tailKillTauChunk0004Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0004_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0004Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0004Rows[off] (tailKillTauChunk0004Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0004_rows_match off hoff

theorem tailKillTauChunk0004_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0004Rows.length)
    (htag : tailKillTauChunk0004Rows[off].tag = 2) :
    tailKillTauChunk0004Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0004_witness_bound_ok off hoff htag


def tailKillTauChunk0005RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0005Start tailKillTauChunk0005Rows

theorem tailKillTauChunk0005_rows_match :
    tailKillTauChunk0005RowsMatch = true := by
  decide

def tailKillTauChunk0005WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0005Rows

theorem tailKillTauChunk0005_witness_bound_ok :
    tailKillTauChunk0005WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0005_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0005Rows.length) :
    RowValid tailKillTauChunk0005Rows[off] :=
  tailKillTauChunk0005_row_valid tailKillTauChunk0005Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0005_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0005Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0005Rows[off] (tailKillTauChunk0005Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0005_rows_match off hoff

theorem tailKillTauChunk0005_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0005Rows.length)
    (htag : tailKillTauChunk0005Rows[off].tag = 2) :
    tailKillTauChunk0005Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0005_witness_bound_ok off hoff htag


def tailKillTauChunk0006RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0006Start tailKillTauChunk0006Rows

theorem tailKillTauChunk0006_rows_match :
    tailKillTauChunk0006RowsMatch = true := by
  decide

def tailKillTauChunk0006WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0006Rows

theorem tailKillTauChunk0006_witness_bound_ok :
    tailKillTauChunk0006WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0006_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0006Rows.length) :
    RowValid tailKillTauChunk0006Rows[off] :=
  tailKillTauChunk0006_row_valid tailKillTauChunk0006Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0006_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0006Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0006Rows[off] (tailKillTauChunk0006Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0006_rows_match off hoff

theorem tailKillTauChunk0006_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0006Rows.length)
    (htag : tailKillTauChunk0006Rows[off].tag = 2) :
    tailKillTauChunk0006Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0006_witness_bound_ok off hoff htag


def tailKillTauChunk0007RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0007Start tailKillTauChunk0007Rows

theorem tailKillTauChunk0007_rows_match :
    tailKillTauChunk0007RowsMatch = true := by
  decide

def tailKillTauChunk0007WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0007Rows

theorem tailKillTauChunk0007_witness_bound_ok :
    tailKillTauChunk0007WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0007_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0007Rows.length) :
    RowValid tailKillTauChunk0007Rows[off] :=
  tailKillTauChunk0007_row_valid tailKillTauChunk0007Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0007_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0007Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0007Rows[off] (tailKillTauChunk0007Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0007_rows_match off hoff

theorem tailKillTauChunk0007_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0007Rows.length)
    (htag : tailKillTauChunk0007Rows[off].tag = 2) :
    tailKillTauChunk0007Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0007_witness_bound_ok off hoff htag


def tailKillTauChunk0008RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0008Start tailKillTauChunk0008Rows

theorem tailKillTauChunk0008_rows_match :
    tailKillTauChunk0008RowsMatch = true := by
  decide

def tailKillTauChunk0008WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0008Rows

theorem tailKillTauChunk0008_witness_bound_ok :
    tailKillTauChunk0008WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0008_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0008Rows.length) :
    RowValid tailKillTauChunk0008Rows[off] :=
  tailKillTauChunk0008_row_valid tailKillTauChunk0008Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0008_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0008Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0008Rows[off] (tailKillTauChunk0008Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0008_rows_match off hoff

theorem tailKillTauChunk0008_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0008Rows.length)
    (htag : tailKillTauChunk0008Rows[off].tag = 2) :
    tailKillTauChunk0008Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0008_witness_bound_ok off hoff htag


def tailKillTauChunk0009RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0009Start tailKillTauChunk0009Rows

theorem tailKillTauChunk0009_rows_match :
    tailKillTauChunk0009RowsMatch = true := by
  decide

def tailKillTauChunk0009WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0009Rows

theorem tailKillTauChunk0009_witness_bound_ok :
    tailKillTauChunk0009WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0009_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0009Rows.length) :
    RowValid tailKillTauChunk0009Rows[off] :=
  tailKillTauChunk0009_row_valid tailKillTauChunk0009Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0009_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0009Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0009Rows[off] (tailKillTauChunk0009Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0009_rows_match off hoff

theorem tailKillTauChunk0009_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0009Rows.length)
    (htag : tailKillTauChunk0009Rows[off].tag = 2) :
    tailKillTauChunk0009Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0009_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
