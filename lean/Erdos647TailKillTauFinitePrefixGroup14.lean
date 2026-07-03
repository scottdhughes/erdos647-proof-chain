import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0140
import Erdos647TailKillTauProofChunks.Chunk0141
import Erdos647TailKillTauProofChunks.Chunk0142
import Erdos647TailKillTauProofChunks.Chunk0143
import Erdos647TailKillTauProofChunks.Chunk0144
import Erdos647TailKillTauProofChunks.Chunk0145
import Erdos647TailKillTauProofChunks.Chunk0146
import Erdos647TailKillTauProofChunks.Chunk0147
import Erdos647TailKillTauProofChunks.Chunk0148
import Erdos647TailKillTauProofChunks.Chunk0149

/-!
# TailKill tau finite-prefix chunk interfaces, group 14

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

def tailKillTauChunk0140RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0140Start tailKillTauChunk0140Rows

theorem tailKillTauChunk0140_rows_match :
    tailKillTauChunk0140RowsMatch = true := by
  decide

def tailKillTauChunk0140WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0140Rows

theorem tailKillTauChunk0140_witness_bound_ok :
    tailKillTauChunk0140WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0140_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0140Rows.length) :
    RowValid tailKillTauChunk0140Rows[off] :=
  tailKillTauChunk0140_row_valid tailKillTauChunk0140Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0140_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0140Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0140Rows[off] (tailKillTauChunk0140Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0140_rows_match off hoff

theorem tailKillTauChunk0140_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0140Rows.length)
    (htag : tailKillTauChunk0140Rows[off].tag = 2) :
    tailKillTauChunk0140Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0140_witness_bound_ok off hoff htag


def tailKillTauChunk0141RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0141Start tailKillTauChunk0141Rows

theorem tailKillTauChunk0141_rows_match :
    tailKillTauChunk0141RowsMatch = true := by
  decide

def tailKillTauChunk0141WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0141Rows

theorem tailKillTauChunk0141_witness_bound_ok :
    tailKillTauChunk0141WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0141_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0141Rows.length) :
    RowValid tailKillTauChunk0141Rows[off] :=
  tailKillTauChunk0141_row_valid tailKillTauChunk0141Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0141_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0141Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0141Rows[off] (tailKillTauChunk0141Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0141_rows_match off hoff

theorem tailKillTauChunk0141_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0141Rows.length)
    (htag : tailKillTauChunk0141Rows[off].tag = 2) :
    tailKillTauChunk0141Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0141_witness_bound_ok off hoff htag


def tailKillTauChunk0142RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0142Start tailKillTauChunk0142Rows

theorem tailKillTauChunk0142_rows_match :
    tailKillTauChunk0142RowsMatch = true := by
  decide

def tailKillTauChunk0142WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0142Rows

theorem tailKillTauChunk0142_witness_bound_ok :
    tailKillTauChunk0142WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0142_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0142Rows.length) :
    RowValid tailKillTauChunk0142Rows[off] :=
  tailKillTauChunk0142_row_valid tailKillTauChunk0142Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0142_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0142Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0142Rows[off] (tailKillTauChunk0142Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0142_rows_match off hoff

theorem tailKillTauChunk0142_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0142Rows.length)
    (htag : tailKillTauChunk0142Rows[off].tag = 2) :
    tailKillTauChunk0142Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0142_witness_bound_ok off hoff htag


def tailKillTauChunk0143RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0143Start tailKillTauChunk0143Rows

theorem tailKillTauChunk0143_rows_match :
    tailKillTauChunk0143RowsMatch = true := by
  decide

def tailKillTauChunk0143WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0143Rows

theorem tailKillTauChunk0143_witness_bound_ok :
    tailKillTauChunk0143WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0143_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0143Rows.length) :
    RowValid tailKillTauChunk0143Rows[off] :=
  tailKillTauChunk0143_row_valid tailKillTauChunk0143Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0143_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0143Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0143Rows[off] (tailKillTauChunk0143Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0143_rows_match off hoff

theorem tailKillTauChunk0143_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0143Rows.length)
    (htag : tailKillTauChunk0143Rows[off].tag = 2) :
    tailKillTauChunk0143Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0143_witness_bound_ok off hoff htag


def tailKillTauChunk0144RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0144Start tailKillTauChunk0144Rows

theorem tailKillTauChunk0144_rows_match :
    tailKillTauChunk0144RowsMatch = true := by
  decide

def tailKillTauChunk0144WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0144Rows

theorem tailKillTauChunk0144_witness_bound_ok :
    tailKillTauChunk0144WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0144_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0144Rows.length) :
    RowValid tailKillTauChunk0144Rows[off] :=
  tailKillTauChunk0144_row_valid tailKillTauChunk0144Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0144_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0144Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0144Rows[off] (tailKillTauChunk0144Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0144_rows_match off hoff

theorem tailKillTauChunk0144_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0144Rows.length)
    (htag : tailKillTauChunk0144Rows[off].tag = 2) :
    tailKillTauChunk0144Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0144_witness_bound_ok off hoff htag


def tailKillTauChunk0145RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0145Start tailKillTauChunk0145Rows

theorem tailKillTauChunk0145_rows_match :
    tailKillTauChunk0145RowsMatch = true := by
  decide

def tailKillTauChunk0145WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0145Rows

theorem tailKillTauChunk0145_witness_bound_ok :
    tailKillTauChunk0145WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0145_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0145Rows.length) :
    RowValid tailKillTauChunk0145Rows[off] :=
  tailKillTauChunk0145_row_valid tailKillTauChunk0145Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0145_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0145Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0145Rows[off] (tailKillTauChunk0145Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0145_rows_match off hoff

theorem tailKillTauChunk0145_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0145Rows.length)
    (htag : tailKillTauChunk0145Rows[off].tag = 2) :
    tailKillTauChunk0145Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0145_witness_bound_ok off hoff htag


def tailKillTauChunk0146RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0146Start tailKillTauChunk0146Rows

theorem tailKillTauChunk0146_rows_match :
    tailKillTauChunk0146RowsMatch = true := by
  decide

def tailKillTauChunk0146WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0146Rows

theorem tailKillTauChunk0146_witness_bound_ok :
    tailKillTauChunk0146WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0146_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0146Rows.length) :
    RowValid tailKillTauChunk0146Rows[off] :=
  tailKillTauChunk0146_row_valid tailKillTauChunk0146Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0146_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0146Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0146Rows[off] (tailKillTauChunk0146Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0146_rows_match off hoff

theorem tailKillTauChunk0146_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0146Rows.length)
    (htag : tailKillTauChunk0146Rows[off].tag = 2) :
    tailKillTauChunk0146Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0146_witness_bound_ok off hoff htag


def tailKillTauChunk0147RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0147Start tailKillTauChunk0147Rows

theorem tailKillTauChunk0147_rows_match :
    tailKillTauChunk0147RowsMatch = true := by
  decide

def tailKillTauChunk0147WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0147Rows

theorem tailKillTauChunk0147_witness_bound_ok :
    tailKillTauChunk0147WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0147_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0147Rows.length) :
    RowValid tailKillTauChunk0147Rows[off] :=
  tailKillTauChunk0147_row_valid tailKillTauChunk0147Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0147_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0147Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0147Rows[off] (tailKillTauChunk0147Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0147_rows_match off hoff

theorem tailKillTauChunk0147_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0147Rows.length)
    (htag : tailKillTauChunk0147Rows[off].tag = 2) :
    tailKillTauChunk0147Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0147_witness_bound_ok off hoff htag


def tailKillTauChunk0148RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0148Start tailKillTauChunk0148Rows

theorem tailKillTauChunk0148_rows_match :
    tailKillTauChunk0148RowsMatch = true := by
  decide

def tailKillTauChunk0148WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0148Rows

theorem tailKillTauChunk0148_witness_bound_ok :
    tailKillTauChunk0148WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0148_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0148Rows.length) :
    RowValid tailKillTauChunk0148Rows[off] :=
  tailKillTauChunk0148_row_valid tailKillTauChunk0148Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0148_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0148Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0148Rows[off] (tailKillTauChunk0148Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0148_rows_match off hoff

theorem tailKillTauChunk0148_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0148Rows.length)
    (htag : tailKillTauChunk0148Rows[off].tag = 2) :
    tailKillTauChunk0148Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0148_witness_bound_ok off hoff htag


def tailKillTauChunk0149RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0149Start tailKillTauChunk0149Rows

theorem tailKillTauChunk0149_rows_match :
    tailKillTauChunk0149RowsMatch = true := by
  decide

def tailKillTauChunk0149WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0149Rows

theorem tailKillTauChunk0149_witness_bound_ok :
    tailKillTauChunk0149WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0149_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0149Rows.length) :
    RowValid tailKillTauChunk0149Rows[off] :=
  tailKillTauChunk0149_row_valid tailKillTauChunk0149Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0149_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0149Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0149Rows[off] (tailKillTauChunk0149Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0149_rows_match off hoff

theorem tailKillTauChunk0149_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0149Rows.length)
    (htag : tailKillTauChunk0149Rows[off].tag = 2) :
    tailKillTauChunk0149Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0149_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
