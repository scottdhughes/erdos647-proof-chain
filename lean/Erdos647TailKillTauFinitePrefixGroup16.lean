import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0160
import Erdos647TailKillTauProofChunks.Chunk0161
import Erdos647TailKillTauProofChunks.Chunk0162
import Erdos647TailKillTauProofChunks.Chunk0163
import Erdos647TailKillTauProofChunks.Chunk0164
import Erdos647TailKillTauProofChunks.Chunk0165
import Erdos647TailKillTauProofChunks.Chunk0166
import Erdos647TailKillTauProofChunks.Chunk0167
import Erdos647TailKillTauProofChunks.Chunk0168
import Erdos647TailKillTauProofChunks.Chunk0169

/-!
# TailKill tau finite-prefix chunk interfaces, group 16

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

def tailKillTauChunk0160RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0160Start tailKillTauChunk0160Rows

theorem tailKillTauChunk0160_rows_match :
    tailKillTauChunk0160RowsMatch = true := by
  decide

def tailKillTauChunk0160WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0160Rows

theorem tailKillTauChunk0160_witness_bound_ok :
    tailKillTauChunk0160WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0160_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0160Rows.length) :
    RowValid tailKillTauChunk0160Rows[off] :=
  tailKillTauChunk0160_row_valid tailKillTauChunk0160Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0160_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0160Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0160Rows[off] (tailKillTauChunk0160Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0160_rows_match off hoff

theorem tailKillTauChunk0160_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0160Rows.length)
    (htag : tailKillTauChunk0160Rows[off].tag = 2) :
    tailKillTauChunk0160Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0160_witness_bound_ok off hoff htag


def tailKillTauChunk0161RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0161Start tailKillTauChunk0161Rows

theorem tailKillTauChunk0161_rows_match :
    tailKillTauChunk0161RowsMatch = true := by
  decide

def tailKillTauChunk0161WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0161Rows

theorem tailKillTauChunk0161_witness_bound_ok :
    tailKillTauChunk0161WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0161_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0161Rows.length) :
    RowValid tailKillTauChunk0161Rows[off] :=
  tailKillTauChunk0161_row_valid tailKillTauChunk0161Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0161_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0161Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0161Rows[off] (tailKillTauChunk0161Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0161_rows_match off hoff

theorem tailKillTauChunk0161_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0161Rows.length)
    (htag : tailKillTauChunk0161Rows[off].tag = 2) :
    tailKillTauChunk0161Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0161_witness_bound_ok off hoff htag


def tailKillTauChunk0162RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0162Start tailKillTauChunk0162Rows

theorem tailKillTauChunk0162_rows_match :
    tailKillTauChunk0162RowsMatch = true := by
  decide

def tailKillTauChunk0162WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0162Rows

theorem tailKillTauChunk0162_witness_bound_ok :
    tailKillTauChunk0162WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0162_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0162Rows.length) :
    RowValid tailKillTauChunk0162Rows[off] :=
  tailKillTauChunk0162_row_valid tailKillTauChunk0162Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0162_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0162Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0162Rows[off] (tailKillTauChunk0162Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0162_rows_match off hoff

theorem tailKillTauChunk0162_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0162Rows.length)
    (htag : tailKillTauChunk0162Rows[off].tag = 2) :
    tailKillTauChunk0162Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0162_witness_bound_ok off hoff htag


def tailKillTauChunk0163RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0163Start tailKillTauChunk0163Rows

theorem tailKillTauChunk0163_rows_match :
    tailKillTauChunk0163RowsMatch = true := by
  decide

def tailKillTauChunk0163WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0163Rows

theorem tailKillTauChunk0163_witness_bound_ok :
    tailKillTauChunk0163WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0163_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0163Rows.length) :
    RowValid tailKillTauChunk0163Rows[off] :=
  tailKillTauChunk0163_row_valid tailKillTauChunk0163Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0163_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0163Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0163Rows[off] (tailKillTauChunk0163Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0163_rows_match off hoff

theorem tailKillTauChunk0163_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0163Rows.length)
    (htag : tailKillTauChunk0163Rows[off].tag = 2) :
    tailKillTauChunk0163Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0163_witness_bound_ok off hoff htag


def tailKillTauChunk0164RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0164Start tailKillTauChunk0164Rows

theorem tailKillTauChunk0164_rows_match :
    tailKillTauChunk0164RowsMatch = true := by
  decide

def tailKillTauChunk0164WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0164Rows

theorem tailKillTauChunk0164_witness_bound_ok :
    tailKillTauChunk0164WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0164_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0164Rows.length) :
    RowValid tailKillTauChunk0164Rows[off] :=
  tailKillTauChunk0164_row_valid tailKillTauChunk0164Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0164_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0164Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0164Rows[off] (tailKillTauChunk0164Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0164_rows_match off hoff

theorem tailKillTauChunk0164_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0164Rows.length)
    (htag : tailKillTauChunk0164Rows[off].tag = 2) :
    tailKillTauChunk0164Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0164_witness_bound_ok off hoff htag


def tailKillTauChunk0165RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0165Start tailKillTauChunk0165Rows

theorem tailKillTauChunk0165_rows_match :
    tailKillTauChunk0165RowsMatch = true := by
  decide

def tailKillTauChunk0165WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0165Rows

theorem tailKillTauChunk0165_witness_bound_ok :
    tailKillTauChunk0165WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0165_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0165Rows.length) :
    RowValid tailKillTauChunk0165Rows[off] :=
  tailKillTauChunk0165_row_valid tailKillTauChunk0165Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0165_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0165Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0165Rows[off] (tailKillTauChunk0165Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0165_rows_match off hoff

theorem tailKillTauChunk0165_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0165Rows.length)
    (htag : tailKillTauChunk0165Rows[off].tag = 2) :
    tailKillTauChunk0165Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0165_witness_bound_ok off hoff htag


def tailKillTauChunk0166RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0166Start tailKillTauChunk0166Rows

theorem tailKillTauChunk0166_rows_match :
    tailKillTauChunk0166RowsMatch = true := by
  decide

def tailKillTauChunk0166WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0166Rows

theorem tailKillTauChunk0166_witness_bound_ok :
    tailKillTauChunk0166WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0166_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0166Rows.length) :
    RowValid tailKillTauChunk0166Rows[off] :=
  tailKillTauChunk0166_row_valid tailKillTauChunk0166Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0166_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0166Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0166Rows[off] (tailKillTauChunk0166Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0166_rows_match off hoff

theorem tailKillTauChunk0166_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0166Rows.length)
    (htag : tailKillTauChunk0166Rows[off].tag = 2) :
    tailKillTauChunk0166Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0166_witness_bound_ok off hoff htag


def tailKillTauChunk0167RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0167Start tailKillTauChunk0167Rows

theorem tailKillTauChunk0167_rows_match :
    tailKillTauChunk0167RowsMatch = true := by
  decide

def tailKillTauChunk0167WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0167Rows

theorem tailKillTauChunk0167_witness_bound_ok :
    tailKillTauChunk0167WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0167_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0167Rows.length) :
    RowValid tailKillTauChunk0167Rows[off] :=
  tailKillTauChunk0167_row_valid tailKillTauChunk0167Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0167_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0167Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0167Rows[off] (tailKillTauChunk0167Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0167_rows_match off hoff

theorem tailKillTauChunk0167_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0167Rows.length)
    (htag : tailKillTauChunk0167Rows[off].tag = 2) :
    tailKillTauChunk0167Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0167_witness_bound_ok off hoff htag


def tailKillTauChunk0168RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0168Start tailKillTauChunk0168Rows

theorem tailKillTauChunk0168_rows_match :
    tailKillTauChunk0168RowsMatch = true := by
  decide

def tailKillTauChunk0168WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0168Rows

theorem tailKillTauChunk0168_witness_bound_ok :
    tailKillTauChunk0168WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0168_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0168Rows.length) :
    RowValid tailKillTauChunk0168Rows[off] :=
  tailKillTauChunk0168_row_valid tailKillTauChunk0168Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0168_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0168Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0168Rows[off] (tailKillTauChunk0168Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0168_rows_match off hoff

theorem tailKillTauChunk0168_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0168Rows.length)
    (htag : tailKillTauChunk0168Rows[off].tag = 2) :
    tailKillTauChunk0168Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0168_witness_bound_ok off hoff htag


def tailKillTauChunk0169RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0169Start tailKillTauChunk0169Rows

theorem tailKillTauChunk0169_rows_match :
    tailKillTauChunk0169RowsMatch = true := by
  decide

def tailKillTauChunk0169WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0169Rows

theorem tailKillTauChunk0169_witness_bound_ok :
    tailKillTauChunk0169WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0169_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0169Rows.length) :
    RowValid tailKillTauChunk0169Rows[off] :=
  tailKillTauChunk0169_row_valid tailKillTauChunk0169Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0169_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0169Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0169Rows[off] (tailKillTauChunk0169Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0169_rows_match off hoff

theorem tailKillTauChunk0169_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0169Rows.length)
    (htag : tailKillTauChunk0169Rows[off].tag = 2) :
    tailKillTauChunk0169Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0169_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
