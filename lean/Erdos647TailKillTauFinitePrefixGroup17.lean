import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0170
import Erdos647TailKillTauProofChunks.Chunk0171
import Erdos647TailKillTauProofChunks.Chunk0172
import Erdos647TailKillTauProofChunks.Chunk0173
import Erdos647TailKillTauProofChunks.Chunk0174
import Erdos647TailKillTauProofChunks.Chunk0175
import Erdos647TailKillTauProofChunks.Chunk0176
import Erdos647TailKillTauProofChunks.Chunk0177
import Erdos647TailKillTauProofChunks.Chunk0178
import Erdos647TailKillTauProofChunks.Chunk0179

/-!
# TailKill tau finite-prefix chunk interfaces, group 17

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

def tailKillTauChunk0170RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0170Start tailKillTauChunk0170Rows

theorem tailKillTauChunk0170_rows_match :
    tailKillTauChunk0170RowsMatch = true := by
  decide

def tailKillTauChunk0170WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0170Rows

theorem tailKillTauChunk0170_witness_bound_ok :
    tailKillTauChunk0170WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0170_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0170Rows.length) :
    RowValid tailKillTauChunk0170Rows[off] :=
  tailKillTauChunk0170_row_valid tailKillTauChunk0170Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0170_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0170Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0170Rows[off] (tailKillTauChunk0170Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0170_rows_match off hoff

theorem tailKillTauChunk0170_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0170Rows.length)
    (htag : tailKillTauChunk0170Rows[off].tag = 2) :
    tailKillTauChunk0170Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0170_witness_bound_ok off hoff htag


def tailKillTauChunk0171RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0171Start tailKillTauChunk0171Rows

theorem tailKillTauChunk0171_rows_match :
    tailKillTauChunk0171RowsMatch = true := by
  decide

def tailKillTauChunk0171WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0171Rows

theorem tailKillTauChunk0171_witness_bound_ok :
    tailKillTauChunk0171WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0171_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0171Rows.length) :
    RowValid tailKillTauChunk0171Rows[off] :=
  tailKillTauChunk0171_row_valid tailKillTauChunk0171Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0171_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0171Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0171Rows[off] (tailKillTauChunk0171Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0171_rows_match off hoff

theorem tailKillTauChunk0171_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0171Rows.length)
    (htag : tailKillTauChunk0171Rows[off].tag = 2) :
    tailKillTauChunk0171Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0171_witness_bound_ok off hoff htag


def tailKillTauChunk0172RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0172Start tailKillTauChunk0172Rows

theorem tailKillTauChunk0172_rows_match :
    tailKillTauChunk0172RowsMatch = true := by
  decide

def tailKillTauChunk0172WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0172Rows

theorem tailKillTauChunk0172_witness_bound_ok :
    tailKillTauChunk0172WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0172_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0172Rows.length) :
    RowValid tailKillTauChunk0172Rows[off] :=
  tailKillTauChunk0172_row_valid tailKillTauChunk0172Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0172_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0172Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0172Rows[off] (tailKillTauChunk0172Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0172_rows_match off hoff

theorem tailKillTauChunk0172_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0172Rows.length)
    (htag : tailKillTauChunk0172Rows[off].tag = 2) :
    tailKillTauChunk0172Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0172_witness_bound_ok off hoff htag


def tailKillTauChunk0173RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0173Start tailKillTauChunk0173Rows

theorem tailKillTauChunk0173_rows_match :
    tailKillTauChunk0173RowsMatch = true := by
  decide

def tailKillTauChunk0173WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0173Rows

theorem tailKillTauChunk0173_witness_bound_ok :
    tailKillTauChunk0173WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0173_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0173Rows.length) :
    RowValid tailKillTauChunk0173Rows[off] :=
  tailKillTauChunk0173_row_valid tailKillTauChunk0173Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0173_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0173Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0173Rows[off] (tailKillTauChunk0173Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0173_rows_match off hoff

theorem tailKillTauChunk0173_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0173Rows.length)
    (htag : tailKillTauChunk0173Rows[off].tag = 2) :
    tailKillTauChunk0173Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0173_witness_bound_ok off hoff htag


def tailKillTauChunk0174RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0174Start tailKillTauChunk0174Rows

theorem tailKillTauChunk0174_rows_match :
    tailKillTauChunk0174RowsMatch = true := by
  decide

def tailKillTauChunk0174WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0174Rows

theorem tailKillTauChunk0174_witness_bound_ok :
    tailKillTauChunk0174WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0174_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0174Rows.length) :
    RowValid tailKillTauChunk0174Rows[off] :=
  tailKillTauChunk0174_row_valid tailKillTauChunk0174Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0174_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0174Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0174Rows[off] (tailKillTauChunk0174Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0174_rows_match off hoff

theorem tailKillTauChunk0174_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0174Rows.length)
    (htag : tailKillTauChunk0174Rows[off].tag = 2) :
    tailKillTauChunk0174Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0174_witness_bound_ok off hoff htag


def tailKillTauChunk0175RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0175Start tailKillTauChunk0175Rows

theorem tailKillTauChunk0175_rows_match :
    tailKillTauChunk0175RowsMatch = true := by
  decide

def tailKillTauChunk0175WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0175Rows

theorem tailKillTauChunk0175_witness_bound_ok :
    tailKillTauChunk0175WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0175_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0175Rows.length) :
    RowValid tailKillTauChunk0175Rows[off] :=
  tailKillTauChunk0175_row_valid tailKillTauChunk0175Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0175_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0175Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0175Rows[off] (tailKillTauChunk0175Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0175_rows_match off hoff

theorem tailKillTauChunk0175_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0175Rows.length)
    (htag : tailKillTauChunk0175Rows[off].tag = 2) :
    tailKillTauChunk0175Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0175_witness_bound_ok off hoff htag


def tailKillTauChunk0176RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0176Start tailKillTauChunk0176Rows

theorem tailKillTauChunk0176_rows_match :
    tailKillTauChunk0176RowsMatch = true := by
  decide

def tailKillTauChunk0176WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0176Rows

theorem tailKillTauChunk0176_witness_bound_ok :
    tailKillTauChunk0176WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0176_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0176Rows.length) :
    RowValid tailKillTauChunk0176Rows[off] :=
  tailKillTauChunk0176_row_valid tailKillTauChunk0176Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0176_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0176Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0176Rows[off] (tailKillTauChunk0176Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0176_rows_match off hoff

theorem tailKillTauChunk0176_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0176Rows.length)
    (htag : tailKillTauChunk0176Rows[off].tag = 2) :
    tailKillTauChunk0176Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0176_witness_bound_ok off hoff htag


def tailKillTauChunk0177RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0177Start tailKillTauChunk0177Rows

theorem tailKillTauChunk0177_rows_match :
    tailKillTauChunk0177RowsMatch = true := by
  decide

def tailKillTauChunk0177WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0177Rows

theorem tailKillTauChunk0177_witness_bound_ok :
    tailKillTauChunk0177WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0177_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0177Rows.length) :
    RowValid tailKillTauChunk0177Rows[off] :=
  tailKillTauChunk0177_row_valid tailKillTauChunk0177Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0177_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0177Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0177Rows[off] (tailKillTauChunk0177Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0177_rows_match off hoff

theorem tailKillTauChunk0177_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0177Rows.length)
    (htag : tailKillTauChunk0177Rows[off].tag = 2) :
    tailKillTauChunk0177Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0177_witness_bound_ok off hoff htag


def tailKillTauChunk0178RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0178Start tailKillTauChunk0178Rows

theorem tailKillTauChunk0178_rows_match :
    tailKillTauChunk0178RowsMatch = true := by
  decide

def tailKillTauChunk0178WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0178Rows

theorem tailKillTauChunk0178_witness_bound_ok :
    tailKillTauChunk0178WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0178_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0178Rows.length) :
    RowValid tailKillTauChunk0178Rows[off] :=
  tailKillTauChunk0178_row_valid tailKillTauChunk0178Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0178_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0178Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0178Rows[off] (tailKillTauChunk0178Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0178_rows_match off hoff

theorem tailKillTauChunk0178_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0178Rows.length)
    (htag : tailKillTauChunk0178Rows[off].tag = 2) :
    tailKillTauChunk0178Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0178_witness_bound_ok off hoff htag


def tailKillTauChunk0179RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0179Start tailKillTauChunk0179Rows

theorem tailKillTauChunk0179_rows_match :
    tailKillTauChunk0179RowsMatch = true := by
  decide

def tailKillTauChunk0179WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0179Rows

theorem tailKillTauChunk0179_witness_bound_ok :
    tailKillTauChunk0179WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0179_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0179Rows.length) :
    RowValid tailKillTauChunk0179Rows[off] :=
  tailKillTauChunk0179_row_valid tailKillTauChunk0179Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0179_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0179Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0179Rows[off] (tailKillTauChunk0179Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0179_rows_match off hoff

theorem tailKillTauChunk0179_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0179Rows.length)
    (htag : tailKillTauChunk0179Rows[off].tag = 2) :
    tailKillTauChunk0179Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0179_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
