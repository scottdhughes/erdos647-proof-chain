import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0130
import Erdos647TailKillTauProofChunks.Chunk0131
import Erdos647TailKillTauProofChunks.Chunk0132
import Erdos647TailKillTauProofChunks.Chunk0133
import Erdos647TailKillTauProofChunks.Chunk0134
import Erdos647TailKillTauProofChunks.Chunk0135
import Erdos647TailKillTauProofChunks.Chunk0136
import Erdos647TailKillTauProofChunks.Chunk0137
import Erdos647TailKillTauProofChunks.Chunk0138
import Erdos647TailKillTauProofChunks.Chunk0139

/-!
# TailKill tau finite-prefix chunk interfaces, group 13

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

def tailKillTauChunk0130RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0130Start tailKillTauChunk0130Rows

theorem tailKillTauChunk0130_rows_match :
    tailKillTauChunk0130RowsMatch = true := by
  decide

def tailKillTauChunk0130WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0130Rows

theorem tailKillTauChunk0130_witness_bound_ok :
    tailKillTauChunk0130WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0130_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0130Rows.length) :
    RowValid tailKillTauChunk0130Rows[off] :=
  tailKillTauChunk0130_row_valid tailKillTauChunk0130Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0130_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0130Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0130Rows[off] (tailKillTauChunk0130Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0130_rows_match off hoff

theorem tailKillTauChunk0130_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0130Rows.length)
    (htag : tailKillTauChunk0130Rows[off].tag = 2) :
    tailKillTauChunk0130Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0130_witness_bound_ok off hoff htag


def tailKillTauChunk0131RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0131Start tailKillTauChunk0131Rows

theorem tailKillTauChunk0131_rows_match :
    tailKillTauChunk0131RowsMatch = true := by
  decide

def tailKillTauChunk0131WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0131Rows

theorem tailKillTauChunk0131_witness_bound_ok :
    tailKillTauChunk0131WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0131_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0131Rows.length) :
    RowValid tailKillTauChunk0131Rows[off] :=
  tailKillTauChunk0131_row_valid tailKillTauChunk0131Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0131_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0131Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0131Rows[off] (tailKillTauChunk0131Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0131_rows_match off hoff

theorem tailKillTauChunk0131_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0131Rows.length)
    (htag : tailKillTauChunk0131Rows[off].tag = 2) :
    tailKillTauChunk0131Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0131_witness_bound_ok off hoff htag


def tailKillTauChunk0132RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0132Start tailKillTauChunk0132Rows

theorem tailKillTauChunk0132_rows_match :
    tailKillTauChunk0132RowsMatch = true := by
  decide

def tailKillTauChunk0132WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0132Rows

theorem tailKillTauChunk0132_witness_bound_ok :
    tailKillTauChunk0132WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0132_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0132Rows.length) :
    RowValid tailKillTauChunk0132Rows[off] :=
  tailKillTauChunk0132_row_valid tailKillTauChunk0132Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0132_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0132Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0132Rows[off] (tailKillTauChunk0132Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0132_rows_match off hoff

theorem tailKillTauChunk0132_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0132Rows.length)
    (htag : tailKillTauChunk0132Rows[off].tag = 2) :
    tailKillTauChunk0132Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0132_witness_bound_ok off hoff htag


def tailKillTauChunk0133RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0133Start tailKillTauChunk0133Rows

theorem tailKillTauChunk0133_rows_match :
    tailKillTauChunk0133RowsMatch = true := by
  decide

def tailKillTauChunk0133WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0133Rows

theorem tailKillTauChunk0133_witness_bound_ok :
    tailKillTauChunk0133WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0133_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0133Rows.length) :
    RowValid tailKillTauChunk0133Rows[off] :=
  tailKillTauChunk0133_row_valid tailKillTauChunk0133Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0133_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0133Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0133Rows[off] (tailKillTauChunk0133Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0133_rows_match off hoff

theorem tailKillTauChunk0133_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0133Rows.length)
    (htag : tailKillTauChunk0133Rows[off].tag = 2) :
    tailKillTauChunk0133Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0133_witness_bound_ok off hoff htag


def tailKillTauChunk0134RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0134Start tailKillTauChunk0134Rows

theorem tailKillTauChunk0134_rows_match :
    tailKillTauChunk0134RowsMatch = true := by
  decide

def tailKillTauChunk0134WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0134Rows

theorem tailKillTauChunk0134_witness_bound_ok :
    tailKillTauChunk0134WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0134_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0134Rows.length) :
    RowValid tailKillTauChunk0134Rows[off] :=
  tailKillTauChunk0134_row_valid tailKillTauChunk0134Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0134_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0134Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0134Rows[off] (tailKillTauChunk0134Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0134_rows_match off hoff

theorem tailKillTauChunk0134_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0134Rows.length)
    (htag : tailKillTauChunk0134Rows[off].tag = 2) :
    tailKillTauChunk0134Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0134_witness_bound_ok off hoff htag


def tailKillTauChunk0135RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0135Start tailKillTauChunk0135Rows

theorem tailKillTauChunk0135_rows_match :
    tailKillTauChunk0135RowsMatch = true := by
  decide

def tailKillTauChunk0135WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0135Rows

theorem tailKillTauChunk0135_witness_bound_ok :
    tailKillTauChunk0135WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0135_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0135Rows.length) :
    RowValid tailKillTauChunk0135Rows[off] :=
  tailKillTauChunk0135_row_valid tailKillTauChunk0135Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0135_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0135Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0135Rows[off] (tailKillTauChunk0135Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0135_rows_match off hoff

theorem tailKillTauChunk0135_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0135Rows.length)
    (htag : tailKillTauChunk0135Rows[off].tag = 2) :
    tailKillTauChunk0135Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0135_witness_bound_ok off hoff htag


def tailKillTauChunk0136RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0136Start tailKillTauChunk0136Rows

theorem tailKillTauChunk0136_rows_match :
    tailKillTauChunk0136RowsMatch = true := by
  decide

def tailKillTauChunk0136WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0136Rows

theorem tailKillTauChunk0136_witness_bound_ok :
    tailKillTauChunk0136WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0136_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0136Rows.length) :
    RowValid tailKillTauChunk0136Rows[off] :=
  tailKillTauChunk0136_row_valid tailKillTauChunk0136Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0136_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0136Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0136Rows[off] (tailKillTauChunk0136Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0136_rows_match off hoff

theorem tailKillTauChunk0136_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0136Rows.length)
    (htag : tailKillTauChunk0136Rows[off].tag = 2) :
    tailKillTauChunk0136Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0136_witness_bound_ok off hoff htag


def tailKillTauChunk0137RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0137Start tailKillTauChunk0137Rows

theorem tailKillTauChunk0137_rows_match :
    tailKillTauChunk0137RowsMatch = true := by
  decide

def tailKillTauChunk0137WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0137Rows

theorem tailKillTauChunk0137_witness_bound_ok :
    tailKillTauChunk0137WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0137_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0137Rows.length) :
    RowValid tailKillTauChunk0137Rows[off] :=
  tailKillTauChunk0137_row_valid tailKillTauChunk0137Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0137_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0137Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0137Rows[off] (tailKillTauChunk0137Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0137_rows_match off hoff

theorem tailKillTauChunk0137_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0137Rows.length)
    (htag : tailKillTauChunk0137Rows[off].tag = 2) :
    tailKillTauChunk0137Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0137_witness_bound_ok off hoff htag


def tailKillTauChunk0138RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0138Start tailKillTauChunk0138Rows

theorem tailKillTauChunk0138_rows_match :
    tailKillTauChunk0138RowsMatch = true := by
  decide

def tailKillTauChunk0138WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0138Rows

theorem tailKillTauChunk0138_witness_bound_ok :
    tailKillTauChunk0138WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0138_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0138Rows.length) :
    RowValid tailKillTauChunk0138Rows[off] :=
  tailKillTauChunk0138_row_valid tailKillTauChunk0138Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0138_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0138Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0138Rows[off] (tailKillTauChunk0138Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0138_rows_match off hoff

theorem tailKillTauChunk0138_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0138Rows.length)
    (htag : tailKillTauChunk0138Rows[off].tag = 2) :
    tailKillTauChunk0138Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0138_witness_bound_ok off hoff htag


def tailKillTauChunk0139RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0139Start tailKillTauChunk0139Rows

theorem tailKillTauChunk0139_rows_match :
    tailKillTauChunk0139RowsMatch = true := by
  decide

def tailKillTauChunk0139WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0139Rows

theorem tailKillTauChunk0139_witness_bound_ok :
    tailKillTauChunk0139WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0139_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0139Rows.length) :
    RowValid tailKillTauChunk0139Rows[off] :=
  tailKillTauChunk0139_row_valid tailKillTauChunk0139Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0139_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0139Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0139Rows[off] (tailKillTauChunk0139Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0139_rows_match off hoff

theorem tailKillTauChunk0139_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0139Rows.length)
    (htag : tailKillTauChunk0139Rows[off].tag = 2) :
    tailKillTauChunk0139Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0139_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
