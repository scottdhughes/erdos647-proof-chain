import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0190
import Erdos647TailKillTauProofChunks.Chunk0191
import Erdos647TailKillTauProofChunks.Chunk0192
import Erdos647TailKillTauProofChunks.Chunk0193
import Erdos647TailKillTauProofChunks.Chunk0194
import Erdos647TailKillTauProofChunks.Chunk0195
import Erdos647TailKillTauProofChunks.Chunk0196
import Erdos647TailKillTauProofChunks.Chunk0197
import Erdos647TailKillTauProofChunks.Chunk0198
import Erdos647TailKillTauProofChunks.Chunk0199

/-!
# TailKill tau finite-prefix chunk interfaces, group 19

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

def tailKillTauChunk0190RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0190Start tailKillTauChunk0190Rows

theorem tailKillTauChunk0190_rows_match :
    tailKillTauChunk0190RowsMatch = true := by
  decide

def tailKillTauChunk0190WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0190Rows

theorem tailKillTauChunk0190_witness_bound_ok :
    tailKillTauChunk0190WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0190_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0190Rows.length) :
    RowValid tailKillTauChunk0190Rows[off] :=
  tailKillTauChunk0190_row_valid tailKillTauChunk0190Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0190_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0190Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0190Rows[off] (tailKillTauChunk0190Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0190_rows_match off hoff

theorem tailKillTauChunk0190_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0190Rows.length)
    (htag : tailKillTauChunk0190Rows[off].tag = 2) :
    tailKillTauChunk0190Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0190_witness_bound_ok off hoff htag


def tailKillTauChunk0191RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0191Start tailKillTauChunk0191Rows

theorem tailKillTauChunk0191_rows_match :
    tailKillTauChunk0191RowsMatch = true := by
  decide

def tailKillTauChunk0191WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0191Rows

theorem tailKillTauChunk0191_witness_bound_ok :
    tailKillTauChunk0191WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0191_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0191Rows.length) :
    RowValid tailKillTauChunk0191Rows[off] :=
  tailKillTauChunk0191_row_valid tailKillTauChunk0191Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0191_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0191Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0191Rows[off] (tailKillTauChunk0191Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0191_rows_match off hoff

theorem tailKillTauChunk0191_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0191Rows.length)
    (htag : tailKillTauChunk0191Rows[off].tag = 2) :
    tailKillTauChunk0191Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0191_witness_bound_ok off hoff htag


def tailKillTauChunk0192RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0192Start tailKillTauChunk0192Rows

theorem tailKillTauChunk0192_rows_match :
    tailKillTauChunk0192RowsMatch = true := by
  decide

def tailKillTauChunk0192WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0192Rows

theorem tailKillTauChunk0192_witness_bound_ok :
    tailKillTauChunk0192WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0192_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0192Rows.length) :
    RowValid tailKillTauChunk0192Rows[off] :=
  tailKillTauChunk0192_row_valid tailKillTauChunk0192Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0192_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0192Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0192Rows[off] (tailKillTauChunk0192Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0192_rows_match off hoff

theorem tailKillTauChunk0192_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0192Rows.length)
    (htag : tailKillTauChunk0192Rows[off].tag = 2) :
    tailKillTauChunk0192Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0192_witness_bound_ok off hoff htag


def tailKillTauChunk0193RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0193Start tailKillTauChunk0193Rows

theorem tailKillTauChunk0193_rows_match :
    tailKillTauChunk0193RowsMatch = true := by
  decide

def tailKillTauChunk0193WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0193Rows

theorem tailKillTauChunk0193_witness_bound_ok :
    tailKillTauChunk0193WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0193_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0193Rows.length) :
    RowValid tailKillTauChunk0193Rows[off] :=
  tailKillTauChunk0193_row_valid tailKillTauChunk0193Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0193_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0193Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0193Rows[off] (tailKillTauChunk0193Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0193_rows_match off hoff

theorem tailKillTauChunk0193_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0193Rows.length)
    (htag : tailKillTauChunk0193Rows[off].tag = 2) :
    tailKillTauChunk0193Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0193_witness_bound_ok off hoff htag


def tailKillTauChunk0194RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0194Start tailKillTauChunk0194Rows

theorem tailKillTauChunk0194_rows_match :
    tailKillTauChunk0194RowsMatch = true := by
  decide

def tailKillTauChunk0194WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0194Rows

theorem tailKillTauChunk0194_witness_bound_ok :
    tailKillTauChunk0194WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0194_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0194Rows.length) :
    RowValid tailKillTauChunk0194Rows[off] :=
  tailKillTauChunk0194_row_valid tailKillTauChunk0194Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0194_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0194Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0194Rows[off] (tailKillTauChunk0194Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0194_rows_match off hoff

theorem tailKillTauChunk0194_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0194Rows.length)
    (htag : tailKillTauChunk0194Rows[off].tag = 2) :
    tailKillTauChunk0194Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0194_witness_bound_ok off hoff htag


def tailKillTauChunk0195RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0195Start tailKillTauChunk0195Rows

theorem tailKillTauChunk0195_rows_match :
    tailKillTauChunk0195RowsMatch = true := by
  decide

def tailKillTauChunk0195WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0195Rows

theorem tailKillTauChunk0195_witness_bound_ok :
    tailKillTauChunk0195WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0195_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0195Rows.length) :
    RowValid tailKillTauChunk0195Rows[off] :=
  tailKillTauChunk0195_row_valid tailKillTauChunk0195Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0195_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0195Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0195Rows[off] (tailKillTauChunk0195Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0195_rows_match off hoff

theorem tailKillTauChunk0195_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0195Rows.length)
    (htag : tailKillTauChunk0195Rows[off].tag = 2) :
    tailKillTauChunk0195Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0195_witness_bound_ok off hoff htag


def tailKillTauChunk0196RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0196Start tailKillTauChunk0196Rows

theorem tailKillTauChunk0196_rows_match :
    tailKillTauChunk0196RowsMatch = true := by
  decide

def tailKillTauChunk0196WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0196Rows

theorem tailKillTauChunk0196_witness_bound_ok :
    tailKillTauChunk0196WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0196_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0196Rows.length) :
    RowValid tailKillTauChunk0196Rows[off] :=
  tailKillTauChunk0196_row_valid tailKillTauChunk0196Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0196_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0196Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0196Rows[off] (tailKillTauChunk0196Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0196_rows_match off hoff

theorem tailKillTauChunk0196_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0196Rows.length)
    (htag : tailKillTauChunk0196Rows[off].tag = 2) :
    tailKillTauChunk0196Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0196_witness_bound_ok off hoff htag


def tailKillTauChunk0197RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0197Start tailKillTauChunk0197Rows

theorem tailKillTauChunk0197_rows_match :
    tailKillTauChunk0197RowsMatch = true := by
  decide

def tailKillTauChunk0197WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0197Rows

theorem tailKillTauChunk0197_witness_bound_ok :
    tailKillTauChunk0197WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0197_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0197Rows.length) :
    RowValid tailKillTauChunk0197Rows[off] :=
  tailKillTauChunk0197_row_valid tailKillTauChunk0197Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0197_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0197Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0197Rows[off] (tailKillTauChunk0197Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0197_rows_match off hoff

theorem tailKillTauChunk0197_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0197Rows.length)
    (htag : tailKillTauChunk0197Rows[off].tag = 2) :
    tailKillTauChunk0197Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0197_witness_bound_ok off hoff htag


def tailKillTauChunk0198RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0198Start tailKillTauChunk0198Rows

theorem tailKillTauChunk0198_rows_match :
    tailKillTauChunk0198RowsMatch = true := by
  decide

def tailKillTauChunk0198WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0198Rows

theorem tailKillTauChunk0198_witness_bound_ok :
    tailKillTauChunk0198WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0198_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0198Rows.length) :
    RowValid tailKillTauChunk0198Rows[off] :=
  tailKillTauChunk0198_row_valid tailKillTauChunk0198Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0198_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0198Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0198Rows[off] (tailKillTauChunk0198Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0198_rows_match off hoff

theorem tailKillTauChunk0198_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0198Rows.length)
    (htag : tailKillTauChunk0198Rows[off].tag = 2) :
    tailKillTauChunk0198Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0198_witness_bound_ok off hoff htag


def tailKillTauChunk0199RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0199Start tailKillTauChunk0199Rows

theorem tailKillTauChunk0199_rows_match :
    tailKillTauChunk0199RowsMatch = true := by
  decide

def tailKillTauChunk0199WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0199Rows

theorem tailKillTauChunk0199_witness_bound_ok :
    tailKillTauChunk0199WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0199_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0199Rows.length) :
    RowValid tailKillTauChunk0199Rows[off] :=
  tailKillTauChunk0199_row_valid tailKillTauChunk0199Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0199_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0199Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0199Rows[off] (tailKillTauChunk0199Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0199_rows_match off hoff

theorem tailKillTauChunk0199_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0199Rows.length)
    (htag : tailKillTauChunk0199Rows[off].tag = 2) :
    tailKillTauChunk0199Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0199_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
