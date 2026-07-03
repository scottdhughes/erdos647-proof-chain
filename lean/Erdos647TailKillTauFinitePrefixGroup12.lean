import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0120
import Erdos647TailKillTauProofChunks.Chunk0121
import Erdos647TailKillTauProofChunks.Chunk0122
import Erdos647TailKillTauProofChunks.Chunk0123
import Erdos647TailKillTauProofChunks.Chunk0124
import Erdos647TailKillTauProofChunks.Chunk0125
import Erdos647TailKillTauProofChunks.Chunk0126
import Erdos647TailKillTauProofChunks.Chunk0127
import Erdos647TailKillTauProofChunks.Chunk0128
import Erdos647TailKillTauProofChunks.Chunk0129

/-!
# TailKill tau finite-prefix chunk interfaces, group 12

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

def tailKillTauChunk0120RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0120Start tailKillTauChunk0120Rows

theorem tailKillTauChunk0120_rows_match :
    tailKillTauChunk0120RowsMatch = true := by
  decide

def tailKillTauChunk0120WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0120Rows

theorem tailKillTauChunk0120_witness_bound_ok :
    tailKillTauChunk0120WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0120_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0120Rows.length) :
    RowValid tailKillTauChunk0120Rows[off] :=
  tailKillTauChunk0120_row_valid tailKillTauChunk0120Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0120_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0120Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0120Rows[off] (tailKillTauChunk0120Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0120_rows_match off hoff

theorem tailKillTauChunk0120_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0120Rows.length)
    (htag : tailKillTauChunk0120Rows[off].tag = 2) :
    tailKillTauChunk0120Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0120_witness_bound_ok off hoff htag


def tailKillTauChunk0121RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0121Start tailKillTauChunk0121Rows

theorem tailKillTauChunk0121_rows_match :
    tailKillTauChunk0121RowsMatch = true := by
  decide

def tailKillTauChunk0121WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0121Rows

theorem tailKillTauChunk0121_witness_bound_ok :
    tailKillTauChunk0121WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0121_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0121Rows.length) :
    RowValid tailKillTauChunk0121Rows[off] :=
  tailKillTauChunk0121_row_valid tailKillTauChunk0121Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0121_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0121Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0121Rows[off] (tailKillTauChunk0121Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0121_rows_match off hoff

theorem tailKillTauChunk0121_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0121Rows.length)
    (htag : tailKillTauChunk0121Rows[off].tag = 2) :
    tailKillTauChunk0121Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0121_witness_bound_ok off hoff htag


def tailKillTauChunk0122RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0122Start tailKillTauChunk0122Rows

theorem tailKillTauChunk0122_rows_match :
    tailKillTauChunk0122RowsMatch = true := by
  decide

def tailKillTauChunk0122WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0122Rows

theorem tailKillTauChunk0122_witness_bound_ok :
    tailKillTauChunk0122WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0122_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0122Rows.length) :
    RowValid tailKillTauChunk0122Rows[off] :=
  tailKillTauChunk0122_row_valid tailKillTauChunk0122Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0122_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0122Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0122Rows[off] (tailKillTauChunk0122Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0122_rows_match off hoff

theorem tailKillTauChunk0122_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0122Rows.length)
    (htag : tailKillTauChunk0122Rows[off].tag = 2) :
    tailKillTauChunk0122Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0122_witness_bound_ok off hoff htag


def tailKillTauChunk0123RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0123Start tailKillTauChunk0123Rows

theorem tailKillTauChunk0123_rows_match :
    tailKillTauChunk0123RowsMatch = true := by
  decide

def tailKillTauChunk0123WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0123Rows

theorem tailKillTauChunk0123_witness_bound_ok :
    tailKillTauChunk0123WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0123_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0123Rows.length) :
    RowValid tailKillTauChunk0123Rows[off] :=
  tailKillTauChunk0123_row_valid tailKillTauChunk0123Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0123_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0123Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0123Rows[off] (tailKillTauChunk0123Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0123_rows_match off hoff

theorem tailKillTauChunk0123_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0123Rows.length)
    (htag : tailKillTauChunk0123Rows[off].tag = 2) :
    tailKillTauChunk0123Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0123_witness_bound_ok off hoff htag


def tailKillTauChunk0124RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0124Start tailKillTauChunk0124Rows

theorem tailKillTauChunk0124_rows_match :
    tailKillTauChunk0124RowsMatch = true := by
  decide

def tailKillTauChunk0124WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0124Rows

theorem tailKillTauChunk0124_witness_bound_ok :
    tailKillTauChunk0124WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0124_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0124Rows.length) :
    RowValid tailKillTauChunk0124Rows[off] :=
  tailKillTauChunk0124_row_valid tailKillTauChunk0124Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0124_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0124Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0124Rows[off] (tailKillTauChunk0124Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0124_rows_match off hoff

theorem tailKillTauChunk0124_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0124Rows.length)
    (htag : tailKillTauChunk0124Rows[off].tag = 2) :
    tailKillTauChunk0124Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0124_witness_bound_ok off hoff htag


def tailKillTauChunk0125RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0125Start tailKillTauChunk0125Rows

theorem tailKillTauChunk0125_rows_match :
    tailKillTauChunk0125RowsMatch = true := by
  decide

def tailKillTauChunk0125WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0125Rows

theorem tailKillTauChunk0125_witness_bound_ok :
    tailKillTauChunk0125WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0125_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0125Rows.length) :
    RowValid tailKillTauChunk0125Rows[off] :=
  tailKillTauChunk0125_row_valid tailKillTauChunk0125Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0125_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0125Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0125Rows[off] (tailKillTauChunk0125Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0125_rows_match off hoff

theorem tailKillTauChunk0125_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0125Rows.length)
    (htag : tailKillTauChunk0125Rows[off].tag = 2) :
    tailKillTauChunk0125Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0125_witness_bound_ok off hoff htag


def tailKillTauChunk0126RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0126Start tailKillTauChunk0126Rows

theorem tailKillTauChunk0126_rows_match :
    tailKillTauChunk0126RowsMatch = true := by
  decide

def tailKillTauChunk0126WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0126Rows

theorem tailKillTauChunk0126_witness_bound_ok :
    tailKillTauChunk0126WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0126_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0126Rows.length) :
    RowValid tailKillTauChunk0126Rows[off] :=
  tailKillTauChunk0126_row_valid tailKillTauChunk0126Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0126_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0126Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0126Rows[off] (tailKillTauChunk0126Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0126_rows_match off hoff

theorem tailKillTauChunk0126_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0126Rows.length)
    (htag : tailKillTauChunk0126Rows[off].tag = 2) :
    tailKillTauChunk0126Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0126_witness_bound_ok off hoff htag


def tailKillTauChunk0127RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0127Start tailKillTauChunk0127Rows

theorem tailKillTauChunk0127_rows_match :
    tailKillTauChunk0127RowsMatch = true := by
  decide

def tailKillTauChunk0127WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0127Rows

theorem tailKillTauChunk0127_witness_bound_ok :
    tailKillTauChunk0127WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0127_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0127Rows.length) :
    RowValid tailKillTauChunk0127Rows[off] :=
  tailKillTauChunk0127_row_valid tailKillTauChunk0127Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0127_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0127Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0127Rows[off] (tailKillTauChunk0127Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0127_rows_match off hoff

theorem tailKillTauChunk0127_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0127Rows.length)
    (htag : tailKillTauChunk0127Rows[off].tag = 2) :
    tailKillTauChunk0127Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0127_witness_bound_ok off hoff htag


def tailKillTauChunk0128RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0128Start tailKillTauChunk0128Rows

theorem tailKillTauChunk0128_rows_match :
    tailKillTauChunk0128RowsMatch = true := by
  decide

def tailKillTauChunk0128WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0128Rows

theorem tailKillTauChunk0128_witness_bound_ok :
    tailKillTauChunk0128WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0128_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0128Rows.length) :
    RowValid tailKillTauChunk0128Rows[off] :=
  tailKillTauChunk0128_row_valid tailKillTauChunk0128Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0128_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0128Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0128Rows[off] (tailKillTauChunk0128Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0128_rows_match off hoff

theorem tailKillTauChunk0128_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0128Rows.length)
    (htag : tailKillTauChunk0128Rows[off].tag = 2) :
    tailKillTauChunk0128Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0128_witness_bound_ok off hoff htag


def tailKillTauChunk0129RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0129Start tailKillTauChunk0129Rows

theorem tailKillTauChunk0129_rows_match :
    tailKillTauChunk0129RowsMatch = true := by
  decide

def tailKillTauChunk0129WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0129Rows

theorem tailKillTauChunk0129_witness_bound_ok :
    tailKillTauChunk0129WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0129_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0129Rows.length) :
    RowValid tailKillTauChunk0129Rows[off] :=
  tailKillTauChunk0129_row_valid tailKillTauChunk0129Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0129_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0129Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0129Rows[off] (tailKillTauChunk0129Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0129_rows_match off hoff

theorem tailKillTauChunk0129_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0129Rows.length)
    (htag : tailKillTauChunk0129Rows[off].tag = 2) :
    tailKillTauChunk0129Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0129_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
