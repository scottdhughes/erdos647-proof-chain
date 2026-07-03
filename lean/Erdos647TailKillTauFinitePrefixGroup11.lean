import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0110
import Erdos647TailKillTauProofChunks.Chunk0111
import Erdos647TailKillTauProofChunks.Chunk0112
import Erdos647TailKillTauProofChunks.Chunk0113
import Erdos647TailKillTauProofChunks.Chunk0114
import Erdos647TailKillTauProofChunks.Chunk0115
import Erdos647TailKillTauProofChunks.Chunk0116
import Erdos647TailKillTauProofChunks.Chunk0117
import Erdos647TailKillTauProofChunks.Chunk0118
import Erdos647TailKillTauProofChunks.Chunk0119

/-!
# TailKill tau finite-prefix chunk interfaces, group 11

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

def tailKillTauChunk0110RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0110Start tailKillTauChunk0110Rows

theorem tailKillTauChunk0110_rows_match :
    tailKillTauChunk0110RowsMatch = true := by
  decide

def tailKillTauChunk0110WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0110Rows

theorem tailKillTauChunk0110_witness_bound_ok :
    tailKillTauChunk0110WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0110_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0110Rows.length) :
    RowValid tailKillTauChunk0110Rows[off] :=
  tailKillTauChunk0110_row_valid tailKillTauChunk0110Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0110_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0110Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0110Rows[off] (tailKillTauChunk0110Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0110_rows_match off hoff

theorem tailKillTauChunk0110_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0110Rows.length)
    (htag : tailKillTauChunk0110Rows[off].tag = 2) :
    tailKillTauChunk0110Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0110_witness_bound_ok off hoff htag


def tailKillTauChunk0111RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0111Start tailKillTauChunk0111Rows

theorem tailKillTauChunk0111_rows_match :
    tailKillTauChunk0111RowsMatch = true := by
  decide

def tailKillTauChunk0111WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0111Rows

theorem tailKillTauChunk0111_witness_bound_ok :
    tailKillTauChunk0111WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0111_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0111Rows.length) :
    RowValid tailKillTauChunk0111Rows[off] :=
  tailKillTauChunk0111_row_valid tailKillTauChunk0111Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0111_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0111Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0111Rows[off] (tailKillTauChunk0111Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0111_rows_match off hoff

theorem tailKillTauChunk0111_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0111Rows.length)
    (htag : tailKillTauChunk0111Rows[off].tag = 2) :
    tailKillTauChunk0111Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0111_witness_bound_ok off hoff htag


def tailKillTauChunk0112RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0112Start tailKillTauChunk0112Rows

theorem tailKillTauChunk0112_rows_match :
    tailKillTauChunk0112RowsMatch = true := by
  decide

def tailKillTauChunk0112WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0112Rows

theorem tailKillTauChunk0112_witness_bound_ok :
    tailKillTauChunk0112WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0112_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0112Rows.length) :
    RowValid tailKillTauChunk0112Rows[off] :=
  tailKillTauChunk0112_row_valid tailKillTauChunk0112Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0112_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0112Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0112Rows[off] (tailKillTauChunk0112Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0112_rows_match off hoff

theorem tailKillTauChunk0112_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0112Rows.length)
    (htag : tailKillTauChunk0112Rows[off].tag = 2) :
    tailKillTauChunk0112Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0112_witness_bound_ok off hoff htag


def tailKillTauChunk0113RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0113Start tailKillTauChunk0113Rows

theorem tailKillTauChunk0113_rows_match :
    tailKillTauChunk0113RowsMatch = true := by
  decide

def tailKillTauChunk0113WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0113Rows

theorem tailKillTauChunk0113_witness_bound_ok :
    tailKillTauChunk0113WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0113_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0113Rows.length) :
    RowValid tailKillTauChunk0113Rows[off] :=
  tailKillTauChunk0113_row_valid tailKillTauChunk0113Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0113_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0113Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0113Rows[off] (tailKillTauChunk0113Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0113_rows_match off hoff

theorem tailKillTauChunk0113_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0113Rows.length)
    (htag : tailKillTauChunk0113Rows[off].tag = 2) :
    tailKillTauChunk0113Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0113_witness_bound_ok off hoff htag


def tailKillTauChunk0114RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0114Start tailKillTauChunk0114Rows

theorem tailKillTauChunk0114_rows_match :
    tailKillTauChunk0114RowsMatch = true := by
  decide

def tailKillTauChunk0114WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0114Rows

theorem tailKillTauChunk0114_witness_bound_ok :
    tailKillTauChunk0114WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0114_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0114Rows.length) :
    RowValid tailKillTauChunk0114Rows[off] :=
  tailKillTauChunk0114_row_valid tailKillTauChunk0114Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0114_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0114Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0114Rows[off] (tailKillTauChunk0114Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0114_rows_match off hoff

theorem tailKillTauChunk0114_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0114Rows.length)
    (htag : tailKillTauChunk0114Rows[off].tag = 2) :
    tailKillTauChunk0114Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0114_witness_bound_ok off hoff htag


def tailKillTauChunk0115RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0115Start tailKillTauChunk0115Rows

theorem tailKillTauChunk0115_rows_match :
    tailKillTauChunk0115RowsMatch = true := by
  decide

def tailKillTauChunk0115WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0115Rows

theorem tailKillTauChunk0115_witness_bound_ok :
    tailKillTauChunk0115WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0115_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0115Rows.length) :
    RowValid tailKillTauChunk0115Rows[off] :=
  tailKillTauChunk0115_row_valid tailKillTauChunk0115Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0115_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0115Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0115Rows[off] (tailKillTauChunk0115Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0115_rows_match off hoff

theorem tailKillTauChunk0115_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0115Rows.length)
    (htag : tailKillTauChunk0115Rows[off].tag = 2) :
    tailKillTauChunk0115Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0115_witness_bound_ok off hoff htag


def tailKillTauChunk0116RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0116Start tailKillTauChunk0116Rows

theorem tailKillTauChunk0116_rows_match :
    tailKillTauChunk0116RowsMatch = true := by
  decide

def tailKillTauChunk0116WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0116Rows

theorem tailKillTauChunk0116_witness_bound_ok :
    tailKillTauChunk0116WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0116_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0116Rows.length) :
    RowValid tailKillTauChunk0116Rows[off] :=
  tailKillTauChunk0116_row_valid tailKillTauChunk0116Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0116_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0116Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0116Rows[off] (tailKillTauChunk0116Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0116_rows_match off hoff

theorem tailKillTauChunk0116_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0116Rows.length)
    (htag : tailKillTauChunk0116Rows[off].tag = 2) :
    tailKillTauChunk0116Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0116_witness_bound_ok off hoff htag


def tailKillTauChunk0117RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0117Start tailKillTauChunk0117Rows

theorem tailKillTauChunk0117_rows_match :
    tailKillTauChunk0117RowsMatch = true := by
  decide

def tailKillTauChunk0117WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0117Rows

theorem tailKillTauChunk0117_witness_bound_ok :
    tailKillTauChunk0117WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0117_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0117Rows.length) :
    RowValid tailKillTauChunk0117Rows[off] :=
  tailKillTauChunk0117_row_valid tailKillTauChunk0117Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0117_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0117Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0117Rows[off] (tailKillTauChunk0117Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0117_rows_match off hoff

theorem tailKillTauChunk0117_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0117Rows.length)
    (htag : tailKillTauChunk0117Rows[off].tag = 2) :
    tailKillTauChunk0117Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0117_witness_bound_ok off hoff htag


def tailKillTauChunk0118RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0118Start tailKillTauChunk0118Rows

theorem tailKillTauChunk0118_rows_match :
    tailKillTauChunk0118RowsMatch = true := by
  decide

def tailKillTauChunk0118WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0118Rows

theorem tailKillTauChunk0118_witness_bound_ok :
    tailKillTauChunk0118WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0118_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0118Rows.length) :
    RowValid tailKillTauChunk0118Rows[off] :=
  tailKillTauChunk0118_row_valid tailKillTauChunk0118Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0118_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0118Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0118Rows[off] (tailKillTauChunk0118Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0118_rows_match off hoff

theorem tailKillTauChunk0118_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0118Rows.length)
    (htag : tailKillTauChunk0118Rows[off].tag = 2) :
    tailKillTauChunk0118Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0118_witness_bound_ok off hoff htag


def tailKillTauChunk0119RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0119Start tailKillTauChunk0119Rows

theorem tailKillTauChunk0119_rows_match :
    tailKillTauChunk0119RowsMatch = true := by
  decide

def tailKillTauChunk0119WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0119Rows

theorem tailKillTauChunk0119_witness_bound_ok :
    tailKillTauChunk0119WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0119_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0119Rows.length) :
    RowValid tailKillTauChunk0119Rows[off] :=
  tailKillTauChunk0119_row_valid tailKillTauChunk0119Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0119_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0119Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0119Rows[off] (tailKillTauChunk0119Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0119_rows_match off hoff

theorem tailKillTauChunk0119_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0119Rows.length)
    (htag : tailKillTauChunk0119Rows[off].tag = 2) :
    tailKillTauChunk0119Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0119_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
