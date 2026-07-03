import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0090
import Erdos647TailKillTauProofChunks.Chunk0091
import Erdos647TailKillTauProofChunks.Chunk0092
import Erdos647TailKillTauProofChunks.Chunk0093
import Erdos647TailKillTauProofChunks.Chunk0094
import Erdos647TailKillTauProofChunks.Chunk0095
import Erdos647TailKillTauProofChunks.Chunk0096
import Erdos647TailKillTauProofChunks.Chunk0097
import Erdos647TailKillTauProofChunks.Chunk0098
import Erdos647TailKillTauProofChunks.Chunk0099

/-!
# TailKill tau finite-prefix chunk interfaces, group 09

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

def tailKillTauChunk0090RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0090Start tailKillTauChunk0090Rows

theorem tailKillTauChunk0090_rows_match :
    tailKillTauChunk0090RowsMatch = true := by
  decide

def tailKillTauChunk0090WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0090Rows

theorem tailKillTauChunk0090_witness_bound_ok :
    tailKillTauChunk0090WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0090_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0090Rows.length) :
    RowValid tailKillTauChunk0090Rows[off] :=
  tailKillTauChunk0090_row_valid tailKillTauChunk0090Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0090_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0090Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0090Rows[off] (tailKillTauChunk0090Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0090_rows_match off hoff

theorem tailKillTauChunk0090_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0090Rows.length)
    (htag : tailKillTauChunk0090Rows[off].tag = 2) :
    tailKillTauChunk0090Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0090_witness_bound_ok off hoff htag


def tailKillTauChunk0091RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0091Start tailKillTauChunk0091Rows

theorem tailKillTauChunk0091_rows_match :
    tailKillTauChunk0091RowsMatch = true := by
  decide

def tailKillTauChunk0091WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0091Rows

theorem tailKillTauChunk0091_witness_bound_ok :
    tailKillTauChunk0091WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0091_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0091Rows.length) :
    RowValid tailKillTauChunk0091Rows[off] :=
  tailKillTauChunk0091_row_valid tailKillTauChunk0091Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0091_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0091Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0091Rows[off] (tailKillTauChunk0091Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0091_rows_match off hoff

theorem tailKillTauChunk0091_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0091Rows.length)
    (htag : tailKillTauChunk0091Rows[off].tag = 2) :
    tailKillTauChunk0091Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0091_witness_bound_ok off hoff htag


def tailKillTauChunk0092RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0092Start tailKillTauChunk0092Rows

theorem tailKillTauChunk0092_rows_match :
    tailKillTauChunk0092RowsMatch = true := by
  decide

def tailKillTauChunk0092WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0092Rows

theorem tailKillTauChunk0092_witness_bound_ok :
    tailKillTauChunk0092WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0092_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0092Rows.length) :
    RowValid tailKillTauChunk0092Rows[off] :=
  tailKillTauChunk0092_row_valid tailKillTauChunk0092Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0092_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0092Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0092Rows[off] (tailKillTauChunk0092Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0092_rows_match off hoff

theorem tailKillTauChunk0092_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0092Rows.length)
    (htag : tailKillTauChunk0092Rows[off].tag = 2) :
    tailKillTauChunk0092Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0092_witness_bound_ok off hoff htag


def tailKillTauChunk0093RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0093Start tailKillTauChunk0093Rows

theorem tailKillTauChunk0093_rows_match :
    tailKillTauChunk0093RowsMatch = true := by
  decide

def tailKillTauChunk0093WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0093Rows

theorem tailKillTauChunk0093_witness_bound_ok :
    tailKillTauChunk0093WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0093_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0093Rows.length) :
    RowValid tailKillTauChunk0093Rows[off] :=
  tailKillTauChunk0093_row_valid tailKillTauChunk0093Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0093_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0093Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0093Rows[off] (tailKillTauChunk0093Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0093_rows_match off hoff

theorem tailKillTauChunk0093_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0093Rows.length)
    (htag : tailKillTauChunk0093Rows[off].tag = 2) :
    tailKillTauChunk0093Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0093_witness_bound_ok off hoff htag


def tailKillTauChunk0094RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0094Start tailKillTauChunk0094Rows

theorem tailKillTauChunk0094_rows_match :
    tailKillTauChunk0094RowsMatch = true := by
  decide

def tailKillTauChunk0094WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0094Rows

theorem tailKillTauChunk0094_witness_bound_ok :
    tailKillTauChunk0094WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0094_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0094Rows.length) :
    RowValid tailKillTauChunk0094Rows[off] :=
  tailKillTauChunk0094_row_valid tailKillTauChunk0094Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0094_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0094Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0094Rows[off] (tailKillTauChunk0094Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0094_rows_match off hoff

theorem tailKillTauChunk0094_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0094Rows.length)
    (htag : tailKillTauChunk0094Rows[off].tag = 2) :
    tailKillTauChunk0094Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0094_witness_bound_ok off hoff htag


def tailKillTauChunk0095RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0095Start tailKillTauChunk0095Rows

theorem tailKillTauChunk0095_rows_match :
    tailKillTauChunk0095RowsMatch = true := by
  decide

def tailKillTauChunk0095WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0095Rows

theorem tailKillTauChunk0095_witness_bound_ok :
    tailKillTauChunk0095WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0095_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0095Rows.length) :
    RowValid tailKillTauChunk0095Rows[off] :=
  tailKillTauChunk0095_row_valid tailKillTauChunk0095Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0095_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0095Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0095Rows[off] (tailKillTauChunk0095Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0095_rows_match off hoff

theorem tailKillTauChunk0095_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0095Rows.length)
    (htag : tailKillTauChunk0095Rows[off].tag = 2) :
    tailKillTauChunk0095Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0095_witness_bound_ok off hoff htag


def tailKillTauChunk0096RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0096Start tailKillTauChunk0096Rows

theorem tailKillTauChunk0096_rows_match :
    tailKillTauChunk0096RowsMatch = true := by
  decide

def tailKillTauChunk0096WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0096Rows

theorem tailKillTauChunk0096_witness_bound_ok :
    tailKillTauChunk0096WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0096_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0096Rows.length) :
    RowValid tailKillTauChunk0096Rows[off] :=
  tailKillTauChunk0096_row_valid tailKillTauChunk0096Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0096_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0096Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0096Rows[off] (tailKillTauChunk0096Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0096_rows_match off hoff

theorem tailKillTauChunk0096_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0096Rows.length)
    (htag : tailKillTauChunk0096Rows[off].tag = 2) :
    tailKillTauChunk0096Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0096_witness_bound_ok off hoff htag


def tailKillTauChunk0097RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0097Start tailKillTauChunk0097Rows

theorem tailKillTauChunk0097_rows_match :
    tailKillTauChunk0097RowsMatch = true := by
  decide

def tailKillTauChunk0097WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0097Rows

theorem tailKillTauChunk0097_witness_bound_ok :
    tailKillTauChunk0097WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0097_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0097Rows.length) :
    RowValid tailKillTauChunk0097Rows[off] :=
  tailKillTauChunk0097_row_valid tailKillTauChunk0097Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0097_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0097Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0097Rows[off] (tailKillTauChunk0097Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0097_rows_match off hoff

theorem tailKillTauChunk0097_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0097Rows.length)
    (htag : tailKillTauChunk0097Rows[off].tag = 2) :
    tailKillTauChunk0097Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0097_witness_bound_ok off hoff htag


def tailKillTauChunk0098RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0098Start tailKillTauChunk0098Rows

theorem tailKillTauChunk0098_rows_match :
    tailKillTauChunk0098RowsMatch = true := by
  decide

def tailKillTauChunk0098WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0098Rows

theorem tailKillTauChunk0098_witness_bound_ok :
    tailKillTauChunk0098WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0098_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0098Rows.length) :
    RowValid tailKillTauChunk0098Rows[off] :=
  tailKillTauChunk0098_row_valid tailKillTauChunk0098Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0098_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0098Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0098Rows[off] (tailKillTauChunk0098Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0098_rows_match off hoff

theorem tailKillTauChunk0098_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0098Rows.length)
    (htag : tailKillTauChunk0098Rows[off].tag = 2) :
    tailKillTauChunk0098Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0098_witness_bound_ok off hoff htag


def tailKillTauChunk0099RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0099Start tailKillTauChunk0099Rows

theorem tailKillTauChunk0099_rows_match :
    tailKillTauChunk0099RowsMatch = true := by
  decide

def tailKillTauChunk0099WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0099Rows

theorem tailKillTauChunk0099_witness_bound_ok :
    tailKillTauChunk0099WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0099_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0099Rows.length) :
    RowValid tailKillTauChunk0099Rows[off] :=
  tailKillTauChunk0099_row_valid tailKillTauChunk0099Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0099_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0099Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0099Rows[off] (tailKillTauChunk0099Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0099_rows_match off hoff

theorem tailKillTauChunk0099_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0099Rows.length)
    (htag : tailKillTauChunk0099Rows[off].tag = 2) :
    tailKillTauChunk0099Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0099_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
