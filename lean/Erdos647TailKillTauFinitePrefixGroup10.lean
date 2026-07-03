import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0100
import Erdos647TailKillTauProofChunks.Chunk0101
import Erdos647TailKillTauProofChunks.Chunk0102
import Erdos647TailKillTauProofChunks.Chunk0103
import Erdos647TailKillTauProofChunks.Chunk0104
import Erdos647TailKillTauProofChunks.Chunk0105
import Erdos647TailKillTauProofChunks.Chunk0106
import Erdos647TailKillTauProofChunks.Chunk0107
import Erdos647TailKillTauProofChunks.Chunk0108
import Erdos647TailKillTauProofChunks.Chunk0109

/-!
# TailKill tau finite-prefix chunk interfaces, group 10

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

def tailKillTauChunk0100RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0100Start tailKillTauChunk0100Rows

theorem tailKillTauChunk0100_rows_match :
    tailKillTauChunk0100RowsMatch = true := by
  decide

def tailKillTauChunk0100WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0100Rows

theorem tailKillTauChunk0100_witness_bound_ok :
    tailKillTauChunk0100WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0100_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0100Rows.length) :
    RowValid tailKillTauChunk0100Rows[off] :=
  tailKillTauChunk0100_row_valid tailKillTauChunk0100Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0100_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0100Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0100Rows[off] (tailKillTauChunk0100Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0100_rows_match off hoff

theorem tailKillTauChunk0100_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0100Rows.length)
    (htag : tailKillTauChunk0100Rows[off].tag = 2) :
    tailKillTauChunk0100Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0100_witness_bound_ok off hoff htag


def tailKillTauChunk0101RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0101Start tailKillTauChunk0101Rows

theorem tailKillTauChunk0101_rows_match :
    tailKillTauChunk0101RowsMatch = true := by
  decide

def tailKillTauChunk0101WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0101Rows

theorem tailKillTauChunk0101_witness_bound_ok :
    tailKillTauChunk0101WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0101_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0101Rows.length) :
    RowValid tailKillTauChunk0101Rows[off] :=
  tailKillTauChunk0101_row_valid tailKillTauChunk0101Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0101_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0101Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0101Rows[off] (tailKillTauChunk0101Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0101_rows_match off hoff

theorem tailKillTauChunk0101_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0101Rows.length)
    (htag : tailKillTauChunk0101Rows[off].tag = 2) :
    tailKillTauChunk0101Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0101_witness_bound_ok off hoff htag


def tailKillTauChunk0102RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0102Start tailKillTauChunk0102Rows

theorem tailKillTauChunk0102_rows_match :
    tailKillTauChunk0102RowsMatch = true := by
  decide

def tailKillTauChunk0102WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0102Rows

theorem tailKillTauChunk0102_witness_bound_ok :
    tailKillTauChunk0102WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0102_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0102Rows.length) :
    RowValid tailKillTauChunk0102Rows[off] :=
  tailKillTauChunk0102_row_valid tailKillTauChunk0102Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0102_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0102Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0102Rows[off] (tailKillTauChunk0102Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0102_rows_match off hoff

theorem tailKillTauChunk0102_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0102Rows.length)
    (htag : tailKillTauChunk0102Rows[off].tag = 2) :
    tailKillTauChunk0102Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0102_witness_bound_ok off hoff htag


def tailKillTauChunk0103RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0103Start tailKillTauChunk0103Rows

theorem tailKillTauChunk0103_rows_match :
    tailKillTauChunk0103RowsMatch = true := by
  decide

def tailKillTauChunk0103WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0103Rows

theorem tailKillTauChunk0103_witness_bound_ok :
    tailKillTauChunk0103WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0103_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0103Rows.length) :
    RowValid tailKillTauChunk0103Rows[off] :=
  tailKillTauChunk0103_row_valid tailKillTauChunk0103Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0103_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0103Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0103Rows[off] (tailKillTauChunk0103Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0103_rows_match off hoff

theorem tailKillTauChunk0103_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0103Rows.length)
    (htag : tailKillTauChunk0103Rows[off].tag = 2) :
    tailKillTauChunk0103Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0103_witness_bound_ok off hoff htag


def tailKillTauChunk0104RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0104Start tailKillTauChunk0104Rows

theorem tailKillTauChunk0104_rows_match :
    tailKillTauChunk0104RowsMatch = true := by
  decide

def tailKillTauChunk0104WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0104Rows

theorem tailKillTauChunk0104_witness_bound_ok :
    tailKillTauChunk0104WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0104_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0104Rows.length) :
    RowValid tailKillTauChunk0104Rows[off] :=
  tailKillTauChunk0104_row_valid tailKillTauChunk0104Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0104_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0104Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0104Rows[off] (tailKillTauChunk0104Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0104_rows_match off hoff

theorem tailKillTauChunk0104_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0104Rows.length)
    (htag : tailKillTauChunk0104Rows[off].tag = 2) :
    tailKillTauChunk0104Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0104_witness_bound_ok off hoff htag


def tailKillTauChunk0105RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0105Start tailKillTauChunk0105Rows

theorem tailKillTauChunk0105_rows_match :
    tailKillTauChunk0105RowsMatch = true := by
  decide

def tailKillTauChunk0105WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0105Rows

theorem tailKillTauChunk0105_witness_bound_ok :
    tailKillTauChunk0105WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0105_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0105Rows.length) :
    RowValid tailKillTauChunk0105Rows[off] :=
  tailKillTauChunk0105_row_valid tailKillTauChunk0105Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0105_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0105Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0105Rows[off] (tailKillTauChunk0105Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0105_rows_match off hoff

theorem tailKillTauChunk0105_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0105Rows.length)
    (htag : tailKillTauChunk0105Rows[off].tag = 2) :
    tailKillTauChunk0105Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0105_witness_bound_ok off hoff htag


def tailKillTauChunk0106RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0106Start tailKillTauChunk0106Rows

theorem tailKillTauChunk0106_rows_match :
    tailKillTauChunk0106RowsMatch = true := by
  decide

def tailKillTauChunk0106WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0106Rows

theorem tailKillTauChunk0106_witness_bound_ok :
    tailKillTauChunk0106WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0106_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0106Rows.length) :
    RowValid tailKillTauChunk0106Rows[off] :=
  tailKillTauChunk0106_row_valid tailKillTauChunk0106Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0106_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0106Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0106Rows[off] (tailKillTauChunk0106Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0106_rows_match off hoff

theorem tailKillTauChunk0106_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0106Rows.length)
    (htag : tailKillTauChunk0106Rows[off].tag = 2) :
    tailKillTauChunk0106Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0106_witness_bound_ok off hoff htag


def tailKillTauChunk0107RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0107Start tailKillTauChunk0107Rows

theorem tailKillTauChunk0107_rows_match :
    tailKillTauChunk0107RowsMatch = true := by
  decide

def tailKillTauChunk0107WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0107Rows

theorem tailKillTauChunk0107_witness_bound_ok :
    tailKillTauChunk0107WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0107_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0107Rows.length) :
    RowValid tailKillTauChunk0107Rows[off] :=
  tailKillTauChunk0107_row_valid tailKillTauChunk0107Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0107_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0107Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0107Rows[off] (tailKillTauChunk0107Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0107_rows_match off hoff

theorem tailKillTauChunk0107_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0107Rows.length)
    (htag : tailKillTauChunk0107Rows[off].tag = 2) :
    tailKillTauChunk0107Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0107_witness_bound_ok off hoff htag


def tailKillTauChunk0108RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0108Start tailKillTauChunk0108Rows

theorem tailKillTauChunk0108_rows_match :
    tailKillTauChunk0108RowsMatch = true := by
  decide

def tailKillTauChunk0108WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0108Rows

theorem tailKillTauChunk0108_witness_bound_ok :
    tailKillTauChunk0108WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0108_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0108Rows.length) :
    RowValid tailKillTauChunk0108Rows[off] :=
  tailKillTauChunk0108_row_valid tailKillTauChunk0108Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0108_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0108Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0108Rows[off] (tailKillTauChunk0108Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0108_rows_match off hoff

theorem tailKillTauChunk0108_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0108Rows.length)
    (htag : tailKillTauChunk0108Rows[off].tag = 2) :
    tailKillTauChunk0108Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0108_witness_bound_ok off hoff htag


def tailKillTauChunk0109RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0109Start tailKillTauChunk0109Rows

theorem tailKillTauChunk0109_rows_match :
    tailKillTauChunk0109RowsMatch = true := by
  decide

def tailKillTauChunk0109WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0109Rows

theorem tailKillTauChunk0109_witness_bound_ok :
    tailKillTauChunk0109WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0109_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0109Rows.length) :
    RowValid tailKillTauChunk0109Rows[off] :=
  tailKillTauChunk0109_row_valid tailKillTauChunk0109Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0109_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0109Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0109Rows[off] (tailKillTauChunk0109Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0109_rows_match off hoff

theorem tailKillTauChunk0109_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0109Rows.length)
    (htag : tailKillTauChunk0109Rows[off].tag = 2) :
    tailKillTauChunk0109Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0109_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
