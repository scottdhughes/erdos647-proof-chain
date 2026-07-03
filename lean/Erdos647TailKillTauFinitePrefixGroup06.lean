import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0060
import Erdos647TailKillTauProofChunks.Chunk0061
import Erdos647TailKillTauProofChunks.Chunk0062
import Erdos647TailKillTauProofChunks.Chunk0063
import Erdos647TailKillTauProofChunks.Chunk0064
import Erdos647TailKillTauProofChunks.Chunk0065
import Erdos647TailKillTauProofChunks.Chunk0066
import Erdos647TailKillTauProofChunks.Chunk0067
import Erdos647TailKillTauProofChunks.Chunk0068
import Erdos647TailKillTauProofChunks.Chunk0069

/-!
# TailKill tau finite-prefix chunk interfaces, group 06

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

def tailKillTauChunk0060RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0060Start tailKillTauChunk0060Rows

theorem tailKillTauChunk0060_rows_match :
    tailKillTauChunk0060RowsMatch = true := by
  decide

def tailKillTauChunk0060WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0060Rows

theorem tailKillTauChunk0060_witness_bound_ok :
    tailKillTauChunk0060WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0060_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0060Rows.length) :
    RowValid tailKillTauChunk0060Rows[off] :=
  tailKillTauChunk0060_row_valid tailKillTauChunk0060Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0060_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0060Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0060Rows[off] (tailKillTauChunk0060Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0060_rows_match off hoff

theorem tailKillTauChunk0060_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0060Rows.length)
    (htag : tailKillTauChunk0060Rows[off].tag = 2) :
    tailKillTauChunk0060Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0060_witness_bound_ok off hoff htag


def tailKillTauChunk0061RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0061Start tailKillTauChunk0061Rows

theorem tailKillTauChunk0061_rows_match :
    tailKillTauChunk0061RowsMatch = true := by
  decide

def tailKillTauChunk0061WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0061Rows

theorem tailKillTauChunk0061_witness_bound_ok :
    tailKillTauChunk0061WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0061_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0061Rows.length) :
    RowValid tailKillTauChunk0061Rows[off] :=
  tailKillTauChunk0061_row_valid tailKillTauChunk0061Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0061_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0061Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0061Rows[off] (tailKillTauChunk0061Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0061_rows_match off hoff

theorem tailKillTauChunk0061_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0061Rows.length)
    (htag : tailKillTauChunk0061Rows[off].tag = 2) :
    tailKillTauChunk0061Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0061_witness_bound_ok off hoff htag


def tailKillTauChunk0062RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0062Start tailKillTauChunk0062Rows

theorem tailKillTauChunk0062_rows_match :
    tailKillTauChunk0062RowsMatch = true := by
  decide

def tailKillTauChunk0062WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0062Rows

theorem tailKillTauChunk0062_witness_bound_ok :
    tailKillTauChunk0062WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0062_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0062Rows.length) :
    RowValid tailKillTauChunk0062Rows[off] :=
  tailKillTauChunk0062_row_valid tailKillTauChunk0062Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0062_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0062Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0062Rows[off] (tailKillTauChunk0062Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0062_rows_match off hoff

theorem tailKillTauChunk0062_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0062Rows.length)
    (htag : tailKillTauChunk0062Rows[off].tag = 2) :
    tailKillTauChunk0062Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0062_witness_bound_ok off hoff htag


def tailKillTauChunk0063RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0063Start tailKillTauChunk0063Rows

theorem tailKillTauChunk0063_rows_match :
    tailKillTauChunk0063RowsMatch = true := by
  decide

def tailKillTauChunk0063WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0063Rows

theorem tailKillTauChunk0063_witness_bound_ok :
    tailKillTauChunk0063WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0063_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0063Rows.length) :
    RowValid tailKillTauChunk0063Rows[off] :=
  tailKillTauChunk0063_row_valid tailKillTauChunk0063Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0063_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0063Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0063Rows[off] (tailKillTauChunk0063Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0063_rows_match off hoff

theorem tailKillTauChunk0063_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0063Rows.length)
    (htag : tailKillTauChunk0063Rows[off].tag = 2) :
    tailKillTauChunk0063Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0063_witness_bound_ok off hoff htag


def tailKillTauChunk0064RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0064Start tailKillTauChunk0064Rows

theorem tailKillTauChunk0064_rows_match :
    tailKillTauChunk0064RowsMatch = true := by
  decide

def tailKillTauChunk0064WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0064Rows

theorem tailKillTauChunk0064_witness_bound_ok :
    tailKillTauChunk0064WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0064_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0064Rows.length) :
    RowValid tailKillTauChunk0064Rows[off] :=
  tailKillTauChunk0064_row_valid tailKillTauChunk0064Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0064_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0064Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0064Rows[off] (tailKillTauChunk0064Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0064_rows_match off hoff

theorem tailKillTauChunk0064_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0064Rows.length)
    (htag : tailKillTauChunk0064Rows[off].tag = 2) :
    tailKillTauChunk0064Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0064_witness_bound_ok off hoff htag


def tailKillTauChunk0065RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0065Start tailKillTauChunk0065Rows

theorem tailKillTauChunk0065_rows_match :
    tailKillTauChunk0065RowsMatch = true := by
  decide

def tailKillTauChunk0065WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0065Rows

theorem tailKillTauChunk0065_witness_bound_ok :
    tailKillTauChunk0065WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0065_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0065Rows.length) :
    RowValid tailKillTauChunk0065Rows[off] :=
  tailKillTauChunk0065_row_valid tailKillTauChunk0065Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0065_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0065Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0065Rows[off] (tailKillTauChunk0065Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0065_rows_match off hoff

theorem tailKillTauChunk0065_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0065Rows.length)
    (htag : tailKillTauChunk0065Rows[off].tag = 2) :
    tailKillTauChunk0065Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0065_witness_bound_ok off hoff htag


def tailKillTauChunk0066RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0066Start tailKillTauChunk0066Rows

theorem tailKillTauChunk0066_rows_match :
    tailKillTauChunk0066RowsMatch = true := by
  decide

def tailKillTauChunk0066WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0066Rows

theorem tailKillTauChunk0066_witness_bound_ok :
    tailKillTauChunk0066WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0066_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0066Rows.length) :
    RowValid tailKillTauChunk0066Rows[off] :=
  tailKillTauChunk0066_row_valid tailKillTauChunk0066Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0066_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0066Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0066Rows[off] (tailKillTauChunk0066Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0066_rows_match off hoff

theorem tailKillTauChunk0066_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0066Rows.length)
    (htag : tailKillTauChunk0066Rows[off].tag = 2) :
    tailKillTauChunk0066Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0066_witness_bound_ok off hoff htag


def tailKillTauChunk0067RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0067Start tailKillTauChunk0067Rows

theorem tailKillTauChunk0067_rows_match :
    tailKillTauChunk0067RowsMatch = true := by
  decide

def tailKillTauChunk0067WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0067Rows

theorem tailKillTauChunk0067_witness_bound_ok :
    tailKillTauChunk0067WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0067_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0067Rows.length) :
    RowValid tailKillTauChunk0067Rows[off] :=
  tailKillTauChunk0067_row_valid tailKillTauChunk0067Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0067_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0067Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0067Rows[off] (tailKillTauChunk0067Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0067_rows_match off hoff

theorem tailKillTauChunk0067_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0067Rows.length)
    (htag : tailKillTauChunk0067Rows[off].tag = 2) :
    tailKillTauChunk0067Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0067_witness_bound_ok off hoff htag


def tailKillTauChunk0068RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0068Start tailKillTauChunk0068Rows

theorem tailKillTauChunk0068_rows_match :
    tailKillTauChunk0068RowsMatch = true := by
  decide

def tailKillTauChunk0068WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0068Rows

theorem tailKillTauChunk0068_witness_bound_ok :
    tailKillTauChunk0068WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0068_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0068Rows.length) :
    RowValid tailKillTauChunk0068Rows[off] :=
  tailKillTauChunk0068_row_valid tailKillTauChunk0068Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0068_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0068Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0068Rows[off] (tailKillTauChunk0068Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0068_rows_match off hoff

theorem tailKillTauChunk0068_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0068Rows.length)
    (htag : tailKillTauChunk0068Rows[off].tag = 2) :
    tailKillTauChunk0068Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0068_witness_bound_ok off hoff htag


def tailKillTauChunk0069RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0069Start tailKillTauChunk0069Rows

theorem tailKillTauChunk0069_rows_match :
    tailKillTauChunk0069RowsMatch = true := by
  decide

def tailKillTauChunk0069WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0069Rows

theorem tailKillTauChunk0069_witness_bound_ok :
    tailKillTauChunk0069WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0069_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0069Rows.length) :
    RowValid tailKillTauChunk0069Rows[off] :=
  tailKillTauChunk0069_row_valid tailKillTauChunk0069Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0069_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0069Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0069Rows[off] (tailKillTauChunk0069Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0069_rows_match off hoff

theorem tailKillTauChunk0069_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0069Rows.length)
    (htag : tailKillTauChunk0069Rows[off].tag = 2) :
    tailKillTauChunk0069Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0069_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
