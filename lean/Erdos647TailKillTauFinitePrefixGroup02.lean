import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0020
import Erdos647TailKillTauProofChunks.Chunk0021
import Erdos647TailKillTauProofChunks.Chunk0022
import Erdos647TailKillTauProofChunks.Chunk0023
import Erdos647TailKillTauProofChunks.Chunk0024
import Erdos647TailKillTauProofChunks.Chunk0025
import Erdos647TailKillTauProofChunks.Chunk0026
import Erdos647TailKillTauProofChunks.Chunk0027
import Erdos647TailKillTauProofChunks.Chunk0028
import Erdos647TailKillTauProofChunks.Chunk0029

/-!
# TailKill tau finite-prefix chunk interfaces, group 02

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

def tailKillTauChunk0020RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0020Start tailKillTauChunk0020Rows

theorem tailKillTauChunk0020_rows_match :
    tailKillTauChunk0020RowsMatch = true := by
  decide

def tailKillTauChunk0020WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0020Rows

theorem tailKillTauChunk0020_witness_bound_ok :
    tailKillTauChunk0020WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0020_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0020Rows.length) :
    RowValid tailKillTauChunk0020Rows[off] :=
  tailKillTauChunk0020_row_valid tailKillTauChunk0020Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0020_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0020Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0020Rows[off] (tailKillTauChunk0020Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0020_rows_match off hoff

theorem tailKillTauChunk0020_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0020Rows.length)
    (htag : tailKillTauChunk0020Rows[off].tag = 2) :
    tailKillTauChunk0020Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0020_witness_bound_ok off hoff htag


def tailKillTauChunk0021RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0021Start tailKillTauChunk0021Rows

theorem tailKillTauChunk0021_rows_match :
    tailKillTauChunk0021RowsMatch = true := by
  decide

def tailKillTauChunk0021WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0021Rows

theorem tailKillTauChunk0021_witness_bound_ok :
    tailKillTauChunk0021WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0021_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0021Rows.length) :
    RowValid tailKillTauChunk0021Rows[off] :=
  tailKillTauChunk0021_row_valid tailKillTauChunk0021Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0021_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0021Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0021Rows[off] (tailKillTauChunk0021Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0021_rows_match off hoff

theorem tailKillTauChunk0021_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0021Rows.length)
    (htag : tailKillTauChunk0021Rows[off].tag = 2) :
    tailKillTauChunk0021Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0021_witness_bound_ok off hoff htag


def tailKillTauChunk0022RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0022Start tailKillTauChunk0022Rows

theorem tailKillTauChunk0022_rows_match :
    tailKillTauChunk0022RowsMatch = true := by
  decide

def tailKillTauChunk0022WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0022Rows

theorem tailKillTauChunk0022_witness_bound_ok :
    tailKillTauChunk0022WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0022_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0022Rows.length) :
    RowValid tailKillTauChunk0022Rows[off] :=
  tailKillTauChunk0022_row_valid tailKillTauChunk0022Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0022_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0022Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0022Rows[off] (tailKillTauChunk0022Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0022_rows_match off hoff

theorem tailKillTauChunk0022_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0022Rows.length)
    (htag : tailKillTauChunk0022Rows[off].tag = 2) :
    tailKillTauChunk0022Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0022_witness_bound_ok off hoff htag


def tailKillTauChunk0023RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0023Start tailKillTauChunk0023Rows

theorem tailKillTauChunk0023_rows_match :
    tailKillTauChunk0023RowsMatch = true := by
  decide

def tailKillTauChunk0023WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0023Rows

theorem tailKillTauChunk0023_witness_bound_ok :
    tailKillTauChunk0023WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0023_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0023Rows.length) :
    RowValid tailKillTauChunk0023Rows[off] :=
  tailKillTauChunk0023_row_valid tailKillTauChunk0023Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0023_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0023Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0023Rows[off] (tailKillTauChunk0023Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0023_rows_match off hoff

theorem tailKillTauChunk0023_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0023Rows.length)
    (htag : tailKillTauChunk0023Rows[off].tag = 2) :
    tailKillTauChunk0023Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0023_witness_bound_ok off hoff htag


def tailKillTauChunk0024RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0024Start tailKillTauChunk0024Rows

theorem tailKillTauChunk0024_rows_match :
    tailKillTauChunk0024RowsMatch = true := by
  decide

def tailKillTauChunk0024WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0024Rows

theorem tailKillTauChunk0024_witness_bound_ok :
    tailKillTauChunk0024WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0024_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0024Rows.length) :
    RowValid tailKillTauChunk0024Rows[off] :=
  tailKillTauChunk0024_row_valid tailKillTauChunk0024Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0024_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0024Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0024Rows[off] (tailKillTauChunk0024Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0024_rows_match off hoff

theorem tailKillTauChunk0024_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0024Rows.length)
    (htag : tailKillTauChunk0024Rows[off].tag = 2) :
    tailKillTauChunk0024Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0024_witness_bound_ok off hoff htag


def tailKillTauChunk0025RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0025Start tailKillTauChunk0025Rows

theorem tailKillTauChunk0025_rows_match :
    tailKillTauChunk0025RowsMatch = true := by
  decide

def tailKillTauChunk0025WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0025Rows

theorem tailKillTauChunk0025_witness_bound_ok :
    tailKillTauChunk0025WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0025_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0025Rows.length) :
    RowValid tailKillTauChunk0025Rows[off] :=
  tailKillTauChunk0025_row_valid tailKillTauChunk0025Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0025_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0025Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0025Rows[off] (tailKillTauChunk0025Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0025_rows_match off hoff

theorem tailKillTauChunk0025_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0025Rows.length)
    (htag : tailKillTauChunk0025Rows[off].tag = 2) :
    tailKillTauChunk0025Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0025_witness_bound_ok off hoff htag


def tailKillTauChunk0026RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0026Start tailKillTauChunk0026Rows

theorem tailKillTauChunk0026_rows_match :
    tailKillTauChunk0026RowsMatch = true := by
  decide

def tailKillTauChunk0026WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0026Rows

theorem tailKillTauChunk0026_witness_bound_ok :
    tailKillTauChunk0026WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0026_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0026Rows.length) :
    RowValid tailKillTauChunk0026Rows[off] :=
  tailKillTauChunk0026_row_valid tailKillTauChunk0026Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0026_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0026Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0026Rows[off] (tailKillTauChunk0026Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0026_rows_match off hoff

theorem tailKillTauChunk0026_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0026Rows.length)
    (htag : tailKillTauChunk0026Rows[off].tag = 2) :
    tailKillTauChunk0026Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0026_witness_bound_ok off hoff htag


def tailKillTauChunk0027RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0027Start tailKillTauChunk0027Rows

theorem tailKillTauChunk0027_rows_match :
    tailKillTauChunk0027RowsMatch = true := by
  decide

def tailKillTauChunk0027WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0027Rows

theorem tailKillTauChunk0027_witness_bound_ok :
    tailKillTauChunk0027WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0027_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0027Rows.length) :
    RowValid tailKillTauChunk0027Rows[off] :=
  tailKillTauChunk0027_row_valid tailKillTauChunk0027Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0027_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0027Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0027Rows[off] (tailKillTauChunk0027Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0027_rows_match off hoff

theorem tailKillTauChunk0027_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0027Rows.length)
    (htag : tailKillTauChunk0027Rows[off].tag = 2) :
    tailKillTauChunk0027Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0027_witness_bound_ok off hoff htag


def tailKillTauChunk0028RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0028Start tailKillTauChunk0028Rows

theorem tailKillTauChunk0028_rows_match :
    tailKillTauChunk0028RowsMatch = true := by
  decide

def tailKillTauChunk0028WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0028Rows

theorem tailKillTauChunk0028_witness_bound_ok :
    tailKillTauChunk0028WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0028_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0028Rows.length) :
    RowValid tailKillTauChunk0028Rows[off] :=
  tailKillTauChunk0028_row_valid tailKillTauChunk0028Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0028_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0028Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0028Rows[off] (tailKillTauChunk0028Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0028_rows_match off hoff

theorem tailKillTauChunk0028_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0028Rows.length)
    (htag : tailKillTauChunk0028Rows[off].tag = 2) :
    tailKillTauChunk0028Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0028_witness_bound_ok off hoff htag


def tailKillTauChunk0029RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0029Start tailKillTauChunk0029Rows

theorem tailKillTauChunk0029_rows_match :
    tailKillTauChunk0029RowsMatch = true := by
  decide

def tailKillTauChunk0029WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0029Rows

theorem tailKillTauChunk0029_witness_bound_ok :
    tailKillTauChunk0029WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0029_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0029Rows.length) :
    RowValid tailKillTauChunk0029Rows[off] :=
  tailKillTauChunk0029_row_valid tailKillTauChunk0029Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0029_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0029Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0029Rows[off] (tailKillTauChunk0029Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0029_rows_match off hoff

theorem tailKillTauChunk0029_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0029Rows.length)
    (htag : tailKillTauChunk0029Rows[off].tag = 2) :
    tailKillTauChunk0029Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0029_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
