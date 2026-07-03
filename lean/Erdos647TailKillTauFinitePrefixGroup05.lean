import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0050
import Erdos647TailKillTauProofChunks.Chunk0051
import Erdos647TailKillTauProofChunks.Chunk0052
import Erdos647TailKillTauProofChunks.Chunk0053
import Erdos647TailKillTauProofChunks.Chunk0054
import Erdos647TailKillTauProofChunks.Chunk0055
import Erdos647TailKillTauProofChunks.Chunk0056
import Erdos647TailKillTauProofChunks.Chunk0057
import Erdos647TailKillTauProofChunks.Chunk0058
import Erdos647TailKillTauProofChunks.Chunk0059

/-!
# TailKill tau finite-prefix chunk interfaces, group 05

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

def tailKillTauChunk0050RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0050Start tailKillTauChunk0050Rows

theorem tailKillTauChunk0050_rows_match :
    tailKillTauChunk0050RowsMatch = true := by
  decide

def tailKillTauChunk0050WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0050Rows

theorem tailKillTauChunk0050_witness_bound_ok :
    tailKillTauChunk0050WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0050_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0050Rows.length) :
    RowValid tailKillTauChunk0050Rows[off] :=
  tailKillTauChunk0050_row_valid tailKillTauChunk0050Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0050_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0050Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0050Rows[off] (tailKillTauChunk0050Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0050_rows_match off hoff

theorem tailKillTauChunk0050_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0050Rows.length)
    (htag : tailKillTauChunk0050Rows[off].tag = 2) :
    tailKillTauChunk0050Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0050_witness_bound_ok off hoff htag


def tailKillTauChunk0051RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0051Start tailKillTauChunk0051Rows

theorem tailKillTauChunk0051_rows_match :
    tailKillTauChunk0051RowsMatch = true := by
  decide

def tailKillTauChunk0051WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0051Rows

theorem tailKillTauChunk0051_witness_bound_ok :
    tailKillTauChunk0051WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0051_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0051Rows.length) :
    RowValid tailKillTauChunk0051Rows[off] :=
  tailKillTauChunk0051_row_valid tailKillTauChunk0051Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0051_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0051Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0051Rows[off] (tailKillTauChunk0051Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0051_rows_match off hoff

theorem tailKillTauChunk0051_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0051Rows.length)
    (htag : tailKillTauChunk0051Rows[off].tag = 2) :
    tailKillTauChunk0051Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0051_witness_bound_ok off hoff htag


def tailKillTauChunk0052RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0052Start tailKillTauChunk0052Rows

theorem tailKillTauChunk0052_rows_match :
    tailKillTauChunk0052RowsMatch = true := by
  decide

def tailKillTauChunk0052WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0052Rows

theorem tailKillTauChunk0052_witness_bound_ok :
    tailKillTauChunk0052WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0052_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0052Rows.length) :
    RowValid tailKillTauChunk0052Rows[off] :=
  tailKillTauChunk0052_row_valid tailKillTauChunk0052Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0052_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0052Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0052Rows[off] (tailKillTauChunk0052Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0052_rows_match off hoff

theorem tailKillTauChunk0052_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0052Rows.length)
    (htag : tailKillTauChunk0052Rows[off].tag = 2) :
    tailKillTauChunk0052Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0052_witness_bound_ok off hoff htag


def tailKillTauChunk0053RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0053Start tailKillTauChunk0053Rows

theorem tailKillTauChunk0053_rows_match :
    tailKillTauChunk0053RowsMatch = true := by
  decide

def tailKillTauChunk0053WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0053Rows

theorem tailKillTauChunk0053_witness_bound_ok :
    tailKillTauChunk0053WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0053_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0053Rows.length) :
    RowValid tailKillTauChunk0053Rows[off] :=
  tailKillTauChunk0053_row_valid tailKillTauChunk0053Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0053_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0053Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0053Rows[off] (tailKillTauChunk0053Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0053_rows_match off hoff

theorem tailKillTauChunk0053_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0053Rows.length)
    (htag : tailKillTauChunk0053Rows[off].tag = 2) :
    tailKillTauChunk0053Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0053_witness_bound_ok off hoff htag


def tailKillTauChunk0054RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0054Start tailKillTauChunk0054Rows

theorem tailKillTauChunk0054_rows_match :
    tailKillTauChunk0054RowsMatch = true := by
  decide

def tailKillTauChunk0054WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0054Rows

theorem tailKillTauChunk0054_witness_bound_ok :
    tailKillTauChunk0054WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0054_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0054Rows.length) :
    RowValid tailKillTauChunk0054Rows[off] :=
  tailKillTauChunk0054_row_valid tailKillTauChunk0054Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0054_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0054Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0054Rows[off] (tailKillTauChunk0054Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0054_rows_match off hoff

theorem tailKillTauChunk0054_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0054Rows.length)
    (htag : tailKillTauChunk0054Rows[off].tag = 2) :
    tailKillTauChunk0054Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0054_witness_bound_ok off hoff htag


def tailKillTauChunk0055RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0055Start tailKillTauChunk0055Rows

theorem tailKillTauChunk0055_rows_match :
    tailKillTauChunk0055RowsMatch = true := by
  decide

def tailKillTauChunk0055WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0055Rows

theorem tailKillTauChunk0055_witness_bound_ok :
    tailKillTauChunk0055WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0055_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0055Rows.length) :
    RowValid tailKillTauChunk0055Rows[off] :=
  tailKillTauChunk0055_row_valid tailKillTauChunk0055Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0055_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0055Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0055Rows[off] (tailKillTauChunk0055Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0055_rows_match off hoff

theorem tailKillTauChunk0055_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0055Rows.length)
    (htag : tailKillTauChunk0055Rows[off].tag = 2) :
    tailKillTauChunk0055Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0055_witness_bound_ok off hoff htag


def tailKillTauChunk0056RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0056Start tailKillTauChunk0056Rows

theorem tailKillTauChunk0056_rows_match :
    tailKillTauChunk0056RowsMatch = true := by
  decide

def tailKillTauChunk0056WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0056Rows

theorem tailKillTauChunk0056_witness_bound_ok :
    tailKillTauChunk0056WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0056_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0056Rows.length) :
    RowValid tailKillTauChunk0056Rows[off] :=
  tailKillTauChunk0056_row_valid tailKillTauChunk0056Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0056_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0056Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0056Rows[off] (tailKillTauChunk0056Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0056_rows_match off hoff

theorem tailKillTauChunk0056_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0056Rows.length)
    (htag : tailKillTauChunk0056Rows[off].tag = 2) :
    tailKillTauChunk0056Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0056_witness_bound_ok off hoff htag


def tailKillTauChunk0057RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0057Start tailKillTauChunk0057Rows

theorem tailKillTauChunk0057_rows_match :
    tailKillTauChunk0057RowsMatch = true := by
  decide

def tailKillTauChunk0057WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0057Rows

theorem tailKillTauChunk0057_witness_bound_ok :
    tailKillTauChunk0057WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0057_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0057Rows.length) :
    RowValid tailKillTauChunk0057Rows[off] :=
  tailKillTauChunk0057_row_valid tailKillTauChunk0057Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0057_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0057Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0057Rows[off] (tailKillTauChunk0057Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0057_rows_match off hoff

theorem tailKillTauChunk0057_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0057Rows.length)
    (htag : tailKillTauChunk0057Rows[off].tag = 2) :
    tailKillTauChunk0057Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0057_witness_bound_ok off hoff htag


def tailKillTauChunk0058RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0058Start tailKillTauChunk0058Rows

theorem tailKillTauChunk0058_rows_match :
    tailKillTauChunk0058RowsMatch = true := by
  decide

def tailKillTauChunk0058WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0058Rows

theorem tailKillTauChunk0058_witness_bound_ok :
    tailKillTauChunk0058WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0058_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0058Rows.length) :
    RowValid tailKillTauChunk0058Rows[off] :=
  tailKillTauChunk0058_row_valid tailKillTauChunk0058Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0058_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0058Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0058Rows[off] (tailKillTauChunk0058Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0058_rows_match off hoff

theorem tailKillTauChunk0058_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0058Rows.length)
    (htag : tailKillTauChunk0058Rows[off].tag = 2) :
    tailKillTauChunk0058Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0058_witness_bound_ok off hoff htag


def tailKillTauChunk0059RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0059Start tailKillTauChunk0059Rows

theorem tailKillTauChunk0059_rows_match :
    tailKillTauChunk0059RowsMatch = true := by
  decide

def tailKillTauChunk0059WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0059Rows

theorem tailKillTauChunk0059_witness_bound_ok :
    tailKillTauChunk0059WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0059_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0059Rows.length) :
    RowValid tailKillTauChunk0059Rows[off] :=
  tailKillTauChunk0059_row_valid tailKillTauChunk0059Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0059_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0059Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0059Rows[off] (tailKillTauChunk0059Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0059_rows_match off hoff

theorem tailKillTauChunk0059_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0059Rows.length)
    (htag : tailKillTauChunk0059Rows[off].tag = 2) :
    tailKillTauChunk0059Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0059_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
