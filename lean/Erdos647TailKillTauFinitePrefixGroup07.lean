import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0070
import Erdos647TailKillTauProofChunks.Chunk0071
import Erdos647TailKillTauProofChunks.Chunk0072
import Erdos647TailKillTauProofChunks.Chunk0073
import Erdos647TailKillTauProofChunks.Chunk0074
import Erdos647TailKillTauProofChunks.Chunk0075
import Erdos647TailKillTauProofChunks.Chunk0076
import Erdos647TailKillTauProofChunks.Chunk0077
import Erdos647TailKillTauProofChunks.Chunk0078
import Erdos647TailKillTauProofChunks.Chunk0079

/-!
# TailKill tau finite-prefix chunk interfaces, group 07

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

def tailKillTauChunk0070RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0070Start tailKillTauChunk0070Rows

theorem tailKillTauChunk0070_rows_match :
    tailKillTauChunk0070RowsMatch = true := by
  decide

def tailKillTauChunk0070WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0070Rows

theorem tailKillTauChunk0070_witness_bound_ok :
    tailKillTauChunk0070WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0070_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0070Rows.length) :
    RowValid tailKillTauChunk0070Rows[off] :=
  tailKillTauChunk0070_row_valid tailKillTauChunk0070Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0070_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0070Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0070Rows[off] (tailKillTauChunk0070Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0070_rows_match off hoff

theorem tailKillTauChunk0070_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0070Rows.length)
    (htag : tailKillTauChunk0070Rows[off].tag = 2) :
    tailKillTauChunk0070Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0070_witness_bound_ok off hoff htag


def tailKillTauChunk0071RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0071Start tailKillTauChunk0071Rows

theorem tailKillTauChunk0071_rows_match :
    tailKillTauChunk0071RowsMatch = true := by
  decide

def tailKillTauChunk0071WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0071Rows

theorem tailKillTauChunk0071_witness_bound_ok :
    tailKillTauChunk0071WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0071_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0071Rows.length) :
    RowValid tailKillTauChunk0071Rows[off] :=
  tailKillTauChunk0071_row_valid tailKillTauChunk0071Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0071_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0071Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0071Rows[off] (tailKillTauChunk0071Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0071_rows_match off hoff

theorem tailKillTauChunk0071_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0071Rows.length)
    (htag : tailKillTauChunk0071Rows[off].tag = 2) :
    tailKillTauChunk0071Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0071_witness_bound_ok off hoff htag


def tailKillTauChunk0072RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0072Start tailKillTauChunk0072Rows

theorem tailKillTauChunk0072_rows_match :
    tailKillTauChunk0072RowsMatch = true := by
  decide

def tailKillTauChunk0072WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0072Rows

theorem tailKillTauChunk0072_witness_bound_ok :
    tailKillTauChunk0072WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0072_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0072Rows.length) :
    RowValid tailKillTauChunk0072Rows[off] :=
  tailKillTauChunk0072_row_valid tailKillTauChunk0072Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0072_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0072Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0072Rows[off] (tailKillTauChunk0072Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0072_rows_match off hoff

theorem tailKillTauChunk0072_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0072Rows.length)
    (htag : tailKillTauChunk0072Rows[off].tag = 2) :
    tailKillTauChunk0072Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0072_witness_bound_ok off hoff htag


def tailKillTauChunk0073RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0073Start tailKillTauChunk0073Rows

theorem tailKillTauChunk0073_rows_match :
    tailKillTauChunk0073RowsMatch = true := by
  decide

def tailKillTauChunk0073WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0073Rows

theorem tailKillTauChunk0073_witness_bound_ok :
    tailKillTauChunk0073WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0073_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0073Rows.length) :
    RowValid tailKillTauChunk0073Rows[off] :=
  tailKillTauChunk0073_row_valid tailKillTauChunk0073Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0073_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0073Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0073Rows[off] (tailKillTauChunk0073Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0073_rows_match off hoff

theorem tailKillTauChunk0073_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0073Rows.length)
    (htag : tailKillTauChunk0073Rows[off].tag = 2) :
    tailKillTauChunk0073Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0073_witness_bound_ok off hoff htag


def tailKillTauChunk0074RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0074Start tailKillTauChunk0074Rows

theorem tailKillTauChunk0074_rows_match :
    tailKillTauChunk0074RowsMatch = true := by
  decide

def tailKillTauChunk0074WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0074Rows

theorem tailKillTauChunk0074_witness_bound_ok :
    tailKillTauChunk0074WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0074_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0074Rows.length) :
    RowValid tailKillTauChunk0074Rows[off] :=
  tailKillTauChunk0074_row_valid tailKillTauChunk0074Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0074_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0074Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0074Rows[off] (tailKillTauChunk0074Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0074_rows_match off hoff

theorem tailKillTauChunk0074_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0074Rows.length)
    (htag : tailKillTauChunk0074Rows[off].tag = 2) :
    tailKillTauChunk0074Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0074_witness_bound_ok off hoff htag


def tailKillTauChunk0075RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0075Start tailKillTauChunk0075Rows

theorem tailKillTauChunk0075_rows_match :
    tailKillTauChunk0075RowsMatch = true := by
  decide

def tailKillTauChunk0075WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0075Rows

theorem tailKillTauChunk0075_witness_bound_ok :
    tailKillTauChunk0075WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0075_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0075Rows.length) :
    RowValid tailKillTauChunk0075Rows[off] :=
  tailKillTauChunk0075_row_valid tailKillTauChunk0075Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0075_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0075Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0075Rows[off] (tailKillTauChunk0075Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0075_rows_match off hoff

theorem tailKillTauChunk0075_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0075Rows.length)
    (htag : tailKillTauChunk0075Rows[off].tag = 2) :
    tailKillTauChunk0075Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0075_witness_bound_ok off hoff htag


def tailKillTauChunk0076RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0076Start tailKillTauChunk0076Rows

theorem tailKillTauChunk0076_rows_match :
    tailKillTauChunk0076RowsMatch = true := by
  decide

def tailKillTauChunk0076WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0076Rows

theorem tailKillTauChunk0076_witness_bound_ok :
    tailKillTauChunk0076WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0076_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0076Rows.length) :
    RowValid tailKillTauChunk0076Rows[off] :=
  tailKillTauChunk0076_row_valid tailKillTauChunk0076Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0076_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0076Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0076Rows[off] (tailKillTauChunk0076Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0076_rows_match off hoff

theorem tailKillTauChunk0076_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0076Rows.length)
    (htag : tailKillTauChunk0076Rows[off].tag = 2) :
    tailKillTauChunk0076Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0076_witness_bound_ok off hoff htag


def tailKillTauChunk0077RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0077Start tailKillTauChunk0077Rows

theorem tailKillTauChunk0077_rows_match :
    tailKillTauChunk0077RowsMatch = true := by
  decide

def tailKillTauChunk0077WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0077Rows

theorem tailKillTauChunk0077_witness_bound_ok :
    tailKillTauChunk0077WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0077_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0077Rows.length) :
    RowValid tailKillTauChunk0077Rows[off] :=
  tailKillTauChunk0077_row_valid tailKillTauChunk0077Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0077_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0077Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0077Rows[off] (tailKillTauChunk0077Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0077_rows_match off hoff

theorem tailKillTauChunk0077_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0077Rows.length)
    (htag : tailKillTauChunk0077Rows[off].tag = 2) :
    tailKillTauChunk0077Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0077_witness_bound_ok off hoff htag


def tailKillTauChunk0078RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0078Start tailKillTauChunk0078Rows

theorem tailKillTauChunk0078_rows_match :
    tailKillTauChunk0078RowsMatch = true := by
  decide

def tailKillTauChunk0078WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0078Rows

theorem tailKillTauChunk0078_witness_bound_ok :
    tailKillTauChunk0078WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0078_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0078Rows.length) :
    RowValid tailKillTauChunk0078Rows[off] :=
  tailKillTauChunk0078_row_valid tailKillTauChunk0078Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0078_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0078Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0078Rows[off] (tailKillTauChunk0078Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0078_rows_match off hoff

theorem tailKillTauChunk0078_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0078Rows.length)
    (htag : tailKillTauChunk0078Rows[off].tag = 2) :
    tailKillTauChunk0078Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0078_witness_bound_ok off hoff htag


def tailKillTauChunk0079RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0079Start tailKillTauChunk0079Rows

theorem tailKillTauChunk0079_rows_match :
    tailKillTauChunk0079RowsMatch = true := by
  decide

def tailKillTauChunk0079WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0079Rows

theorem tailKillTauChunk0079_witness_bound_ok :
    tailKillTauChunk0079WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0079_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0079Rows.length) :
    RowValid tailKillTauChunk0079Rows[off] :=
  tailKillTauChunk0079_row_valid tailKillTauChunk0079Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0079_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0079Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0079Rows[off] (tailKillTauChunk0079Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0079_rows_match off hoff

theorem tailKillTauChunk0079_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0079Rows.length)
    (htag : tailKillTauChunk0079Rows[off].tag = 2) :
    tailKillTauChunk0079Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0079_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
