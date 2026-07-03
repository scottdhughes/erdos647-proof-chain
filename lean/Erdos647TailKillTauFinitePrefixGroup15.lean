import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0150
import Erdos647TailKillTauProofChunks.Chunk0151
import Erdos647TailKillTauProofChunks.Chunk0152
import Erdos647TailKillTauProofChunks.Chunk0153
import Erdos647TailKillTauProofChunks.Chunk0154
import Erdos647TailKillTauProofChunks.Chunk0155
import Erdos647TailKillTauProofChunks.Chunk0156
import Erdos647TailKillTauProofChunks.Chunk0157
import Erdos647TailKillTauProofChunks.Chunk0158
import Erdos647TailKillTauProofChunks.Chunk0159

/-!
# TailKill tau finite-prefix chunk interfaces, group 15

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

def tailKillTauChunk0150RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0150Start tailKillTauChunk0150Rows

theorem tailKillTauChunk0150_rows_match :
    tailKillTauChunk0150RowsMatch = true := by
  decide

def tailKillTauChunk0150WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0150Rows

theorem tailKillTauChunk0150_witness_bound_ok :
    tailKillTauChunk0150WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0150_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0150Rows.length) :
    RowValid tailKillTauChunk0150Rows[off] :=
  tailKillTauChunk0150_row_valid tailKillTauChunk0150Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0150_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0150Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0150Rows[off] (tailKillTauChunk0150Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0150_rows_match off hoff

theorem tailKillTauChunk0150_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0150Rows.length)
    (htag : tailKillTauChunk0150Rows[off].tag = 2) :
    tailKillTauChunk0150Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0150_witness_bound_ok off hoff htag


def tailKillTauChunk0151RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0151Start tailKillTauChunk0151Rows

theorem tailKillTauChunk0151_rows_match :
    tailKillTauChunk0151RowsMatch = true := by
  decide

def tailKillTauChunk0151WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0151Rows

theorem tailKillTauChunk0151_witness_bound_ok :
    tailKillTauChunk0151WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0151_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0151Rows.length) :
    RowValid tailKillTauChunk0151Rows[off] :=
  tailKillTauChunk0151_row_valid tailKillTauChunk0151Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0151_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0151Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0151Rows[off] (tailKillTauChunk0151Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0151_rows_match off hoff

theorem tailKillTauChunk0151_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0151Rows.length)
    (htag : tailKillTauChunk0151Rows[off].tag = 2) :
    tailKillTauChunk0151Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0151_witness_bound_ok off hoff htag


def tailKillTauChunk0152RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0152Start tailKillTauChunk0152Rows

theorem tailKillTauChunk0152_rows_match :
    tailKillTauChunk0152RowsMatch = true := by
  decide

def tailKillTauChunk0152WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0152Rows

theorem tailKillTauChunk0152_witness_bound_ok :
    tailKillTauChunk0152WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0152_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0152Rows.length) :
    RowValid tailKillTauChunk0152Rows[off] :=
  tailKillTauChunk0152_row_valid tailKillTauChunk0152Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0152_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0152Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0152Rows[off] (tailKillTauChunk0152Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0152_rows_match off hoff

theorem tailKillTauChunk0152_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0152Rows.length)
    (htag : tailKillTauChunk0152Rows[off].tag = 2) :
    tailKillTauChunk0152Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0152_witness_bound_ok off hoff htag


def tailKillTauChunk0153RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0153Start tailKillTauChunk0153Rows

theorem tailKillTauChunk0153_rows_match :
    tailKillTauChunk0153RowsMatch = true := by
  decide

def tailKillTauChunk0153WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0153Rows

theorem tailKillTauChunk0153_witness_bound_ok :
    tailKillTauChunk0153WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0153_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0153Rows.length) :
    RowValid tailKillTauChunk0153Rows[off] :=
  tailKillTauChunk0153_row_valid tailKillTauChunk0153Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0153_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0153Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0153Rows[off] (tailKillTauChunk0153Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0153_rows_match off hoff

theorem tailKillTauChunk0153_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0153Rows.length)
    (htag : tailKillTauChunk0153Rows[off].tag = 2) :
    tailKillTauChunk0153Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0153_witness_bound_ok off hoff htag


def tailKillTauChunk0154RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0154Start tailKillTauChunk0154Rows

theorem tailKillTauChunk0154_rows_match :
    tailKillTauChunk0154RowsMatch = true := by
  decide

def tailKillTauChunk0154WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0154Rows

theorem tailKillTauChunk0154_witness_bound_ok :
    tailKillTauChunk0154WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0154_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0154Rows.length) :
    RowValid tailKillTauChunk0154Rows[off] :=
  tailKillTauChunk0154_row_valid tailKillTauChunk0154Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0154_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0154Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0154Rows[off] (tailKillTauChunk0154Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0154_rows_match off hoff

theorem tailKillTauChunk0154_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0154Rows.length)
    (htag : tailKillTauChunk0154Rows[off].tag = 2) :
    tailKillTauChunk0154Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0154_witness_bound_ok off hoff htag


def tailKillTauChunk0155RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0155Start tailKillTauChunk0155Rows

theorem tailKillTauChunk0155_rows_match :
    tailKillTauChunk0155RowsMatch = true := by
  decide

def tailKillTauChunk0155WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0155Rows

theorem tailKillTauChunk0155_witness_bound_ok :
    tailKillTauChunk0155WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0155_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0155Rows.length) :
    RowValid tailKillTauChunk0155Rows[off] :=
  tailKillTauChunk0155_row_valid tailKillTauChunk0155Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0155_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0155Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0155Rows[off] (tailKillTauChunk0155Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0155_rows_match off hoff

theorem tailKillTauChunk0155_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0155Rows.length)
    (htag : tailKillTauChunk0155Rows[off].tag = 2) :
    tailKillTauChunk0155Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0155_witness_bound_ok off hoff htag


def tailKillTauChunk0156RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0156Start tailKillTauChunk0156Rows

theorem tailKillTauChunk0156_rows_match :
    tailKillTauChunk0156RowsMatch = true := by
  decide

def tailKillTauChunk0156WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0156Rows

theorem tailKillTauChunk0156_witness_bound_ok :
    tailKillTauChunk0156WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0156_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0156Rows.length) :
    RowValid tailKillTauChunk0156Rows[off] :=
  tailKillTauChunk0156_row_valid tailKillTauChunk0156Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0156_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0156Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0156Rows[off] (tailKillTauChunk0156Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0156_rows_match off hoff

theorem tailKillTauChunk0156_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0156Rows.length)
    (htag : tailKillTauChunk0156Rows[off].tag = 2) :
    tailKillTauChunk0156Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0156_witness_bound_ok off hoff htag


def tailKillTauChunk0157RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0157Start tailKillTauChunk0157Rows

theorem tailKillTauChunk0157_rows_match :
    tailKillTauChunk0157RowsMatch = true := by
  decide

def tailKillTauChunk0157WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0157Rows

theorem tailKillTauChunk0157_witness_bound_ok :
    tailKillTauChunk0157WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0157_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0157Rows.length) :
    RowValid tailKillTauChunk0157Rows[off] :=
  tailKillTauChunk0157_row_valid tailKillTauChunk0157Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0157_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0157Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0157Rows[off] (tailKillTauChunk0157Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0157_rows_match off hoff

theorem tailKillTauChunk0157_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0157Rows.length)
    (htag : tailKillTauChunk0157Rows[off].tag = 2) :
    tailKillTauChunk0157Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0157_witness_bound_ok off hoff htag


def tailKillTauChunk0158RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0158Start tailKillTauChunk0158Rows

theorem tailKillTauChunk0158_rows_match :
    tailKillTauChunk0158RowsMatch = true := by
  decide

def tailKillTauChunk0158WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0158Rows

theorem tailKillTauChunk0158_witness_bound_ok :
    tailKillTauChunk0158WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0158_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0158Rows.length) :
    RowValid tailKillTauChunk0158Rows[off] :=
  tailKillTauChunk0158_row_valid tailKillTauChunk0158Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0158_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0158Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0158Rows[off] (tailKillTauChunk0158Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0158_rows_match off hoff

theorem tailKillTauChunk0158_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0158Rows.length)
    (htag : tailKillTauChunk0158Rows[off].tag = 2) :
    tailKillTauChunk0158Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0158_witness_bound_ok off hoff htag


def tailKillTauChunk0159RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0159Start tailKillTauChunk0159Rows

theorem tailKillTauChunk0159_rows_match :
    tailKillTauChunk0159RowsMatch = true := by
  decide

def tailKillTauChunk0159WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0159Rows

theorem tailKillTauChunk0159_witness_bound_ok :
    tailKillTauChunk0159WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0159_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0159Rows.length) :
    RowValid tailKillTauChunk0159Rows[off] :=
  tailKillTauChunk0159_row_valid tailKillTauChunk0159Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0159_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0159Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0159Rows[off] (tailKillTauChunk0159Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0159_rows_match off hoff

theorem tailKillTauChunk0159_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0159Rows.length)
    (htag : tailKillTauChunk0159Rows[off].tag = 2) :
    tailKillTauChunk0159Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0159_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
