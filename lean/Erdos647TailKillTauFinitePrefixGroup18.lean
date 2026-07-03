import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0180
import Erdos647TailKillTauProofChunks.Chunk0181
import Erdos647TailKillTauProofChunks.Chunk0182
import Erdos647TailKillTauProofChunks.Chunk0183
import Erdos647TailKillTauProofChunks.Chunk0184
import Erdos647TailKillTauProofChunks.Chunk0185
import Erdos647TailKillTauProofChunks.Chunk0186
import Erdos647TailKillTauProofChunks.Chunk0187
import Erdos647TailKillTauProofChunks.Chunk0188
import Erdos647TailKillTauProofChunks.Chunk0189

/-!
# TailKill tau finite-prefix chunk interfaces, group 18

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

def tailKillTauChunk0180RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0180Start tailKillTauChunk0180Rows

theorem tailKillTauChunk0180_rows_match :
    tailKillTauChunk0180RowsMatch = true := by
  decide

def tailKillTauChunk0180WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0180Rows

theorem tailKillTauChunk0180_witness_bound_ok :
    tailKillTauChunk0180WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0180_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0180Rows.length) :
    RowValid tailKillTauChunk0180Rows[off] :=
  tailKillTauChunk0180_row_valid tailKillTauChunk0180Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0180_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0180Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0180Rows[off] (tailKillTauChunk0180Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0180_rows_match off hoff

theorem tailKillTauChunk0180_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0180Rows.length)
    (htag : tailKillTauChunk0180Rows[off].tag = 2) :
    tailKillTauChunk0180Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0180_witness_bound_ok off hoff htag


def tailKillTauChunk0181RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0181Start tailKillTauChunk0181Rows

theorem tailKillTauChunk0181_rows_match :
    tailKillTauChunk0181RowsMatch = true := by
  decide

def tailKillTauChunk0181WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0181Rows

theorem tailKillTauChunk0181_witness_bound_ok :
    tailKillTauChunk0181WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0181_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0181Rows.length) :
    RowValid tailKillTauChunk0181Rows[off] :=
  tailKillTauChunk0181_row_valid tailKillTauChunk0181Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0181_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0181Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0181Rows[off] (tailKillTauChunk0181Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0181_rows_match off hoff

theorem tailKillTauChunk0181_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0181Rows.length)
    (htag : tailKillTauChunk0181Rows[off].tag = 2) :
    tailKillTauChunk0181Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0181_witness_bound_ok off hoff htag


def tailKillTauChunk0182RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0182Start tailKillTauChunk0182Rows

theorem tailKillTauChunk0182_rows_match :
    tailKillTauChunk0182RowsMatch = true := by
  decide

def tailKillTauChunk0182WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0182Rows

theorem tailKillTauChunk0182_witness_bound_ok :
    tailKillTauChunk0182WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0182_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0182Rows.length) :
    RowValid tailKillTauChunk0182Rows[off] :=
  tailKillTauChunk0182_row_valid tailKillTauChunk0182Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0182_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0182Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0182Rows[off] (tailKillTauChunk0182Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0182_rows_match off hoff

theorem tailKillTauChunk0182_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0182Rows.length)
    (htag : tailKillTauChunk0182Rows[off].tag = 2) :
    tailKillTauChunk0182Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0182_witness_bound_ok off hoff htag


def tailKillTauChunk0183RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0183Start tailKillTauChunk0183Rows

theorem tailKillTauChunk0183_rows_match :
    tailKillTauChunk0183RowsMatch = true := by
  decide

def tailKillTauChunk0183WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0183Rows

theorem tailKillTauChunk0183_witness_bound_ok :
    tailKillTauChunk0183WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0183_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0183Rows.length) :
    RowValid tailKillTauChunk0183Rows[off] :=
  tailKillTauChunk0183_row_valid tailKillTauChunk0183Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0183_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0183Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0183Rows[off] (tailKillTauChunk0183Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0183_rows_match off hoff

theorem tailKillTauChunk0183_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0183Rows.length)
    (htag : tailKillTauChunk0183Rows[off].tag = 2) :
    tailKillTauChunk0183Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0183_witness_bound_ok off hoff htag


def tailKillTauChunk0184RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0184Start tailKillTauChunk0184Rows

theorem tailKillTauChunk0184_rows_match :
    tailKillTauChunk0184RowsMatch = true := by
  decide

def tailKillTauChunk0184WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0184Rows

theorem tailKillTauChunk0184_witness_bound_ok :
    tailKillTauChunk0184WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0184_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0184Rows.length) :
    RowValid tailKillTauChunk0184Rows[off] :=
  tailKillTauChunk0184_row_valid tailKillTauChunk0184Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0184_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0184Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0184Rows[off] (tailKillTauChunk0184Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0184_rows_match off hoff

theorem tailKillTauChunk0184_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0184Rows.length)
    (htag : tailKillTauChunk0184Rows[off].tag = 2) :
    tailKillTauChunk0184Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0184_witness_bound_ok off hoff htag


def tailKillTauChunk0185RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0185Start tailKillTauChunk0185Rows

theorem tailKillTauChunk0185_rows_match :
    tailKillTauChunk0185RowsMatch = true := by
  decide

def tailKillTauChunk0185WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0185Rows

theorem tailKillTauChunk0185_witness_bound_ok :
    tailKillTauChunk0185WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0185_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0185Rows.length) :
    RowValid tailKillTauChunk0185Rows[off] :=
  tailKillTauChunk0185_row_valid tailKillTauChunk0185Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0185_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0185Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0185Rows[off] (tailKillTauChunk0185Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0185_rows_match off hoff

theorem tailKillTauChunk0185_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0185Rows.length)
    (htag : tailKillTauChunk0185Rows[off].tag = 2) :
    tailKillTauChunk0185Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0185_witness_bound_ok off hoff htag


def tailKillTauChunk0186RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0186Start tailKillTauChunk0186Rows

theorem tailKillTauChunk0186_rows_match :
    tailKillTauChunk0186RowsMatch = true := by
  decide

def tailKillTauChunk0186WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0186Rows

theorem tailKillTauChunk0186_witness_bound_ok :
    tailKillTauChunk0186WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0186_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0186Rows.length) :
    RowValid tailKillTauChunk0186Rows[off] :=
  tailKillTauChunk0186_row_valid tailKillTauChunk0186Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0186_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0186Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0186Rows[off] (tailKillTauChunk0186Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0186_rows_match off hoff

theorem tailKillTauChunk0186_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0186Rows.length)
    (htag : tailKillTauChunk0186Rows[off].tag = 2) :
    tailKillTauChunk0186Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0186_witness_bound_ok off hoff htag


def tailKillTauChunk0187RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0187Start tailKillTauChunk0187Rows

theorem tailKillTauChunk0187_rows_match :
    tailKillTauChunk0187RowsMatch = true := by
  decide

def tailKillTauChunk0187WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0187Rows

theorem tailKillTauChunk0187_witness_bound_ok :
    tailKillTauChunk0187WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0187_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0187Rows.length) :
    RowValid tailKillTauChunk0187Rows[off] :=
  tailKillTauChunk0187_row_valid tailKillTauChunk0187Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0187_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0187Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0187Rows[off] (tailKillTauChunk0187Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0187_rows_match off hoff

theorem tailKillTauChunk0187_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0187Rows.length)
    (htag : tailKillTauChunk0187Rows[off].tag = 2) :
    tailKillTauChunk0187Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0187_witness_bound_ok off hoff htag


def tailKillTauChunk0188RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0188Start tailKillTauChunk0188Rows

theorem tailKillTauChunk0188_rows_match :
    tailKillTauChunk0188RowsMatch = true := by
  decide

def tailKillTauChunk0188WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0188Rows

theorem tailKillTauChunk0188_witness_bound_ok :
    tailKillTauChunk0188WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0188_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0188Rows.length) :
    RowValid tailKillTauChunk0188Rows[off] :=
  tailKillTauChunk0188_row_valid tailKillTauChunk0188Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0188_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0188Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0188Rows[off] (tailKillTauChunk0188Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0188_rows_match off hoff

theorem tailKillTauChunk0188_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0188Rows.length)
    (htag : tailKillTauChunk0188Rows[off].tag = 2) :
    tailKillTauChunk0188Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0188_witness_bound_ok off hoff htag


def tailKillTauChunk0189RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0189Start tailKillTauChunk0189Rows

theorem tailKillTauChunk0189_rows_match :
    tailKillTauChunk0189RowsMatch = true := by
  decide

def tailKillTauChunk0189WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0189Rows

theorem tailKillTauChunk0189_witness_bound_ok :
    tailKillTauChunk0189WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0189_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0189Rows.length) :
    RowValid tailKillTauChunk0189Rows[off] :=
  tailKillTauChunk0189_row_valid tailKillTauChunk0189Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0189_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0189Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0189Rows[off] (tailKillTauChunk0189Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0189_rows_match off hoff

theorem tailKillTauChunk0189_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0189Rows.length)
    (htag : tailKillTauChunk0189Rows[off].tag = 2) :
    tailKillTauChunk0189Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0189_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
