import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0030
import Erdos647TailKillTauProofChunks.Chunk0031
import Erdos647TailKillTauProofChunks.Chunk0032
import Erdos647TailKillTauProofChunks.Chunk0033
import Erdos647TailKillTauProofChunks.Chunk0034
import Erdos647TailKillTauProofChunks.Chunk0035
import Erdos647TailKillTauProofChunks.Chunk0036
import Erdos647TailKillTauProofChunks.Chunk0037
import Erdos647TailKillTauProofChunks.Chunk0038
import Erdos647TailKillTauProofChunks.Chunk0039

/-!
# TailKill tau finite-prefix chunk interfaces, group 03

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

def tailKillTauChunk0030RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0030Start tailKillTauChunk0030Rows

theorem tailKillTauChunk0030_rows_match :
    tailKillTauChunk0030RowsMatch = true := by
  decide

def tailKillTauChunk0030WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0030Rows

theorem tailKillTauChunk0030_witness_bound_ok :
    tailKillTauChunk0030WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0030_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0030Rows.length) :
    RowValid tailKillTauChunk0030Rows[off] :=
  tailKillTauChunk0030_row_valid tailKillTauChunk0030Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0030_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0030Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0030Rows[off] (tailKillTauChunk0030Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0030_rows_match off hoff

theorem tailKillTauChunk0030_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0030Rows.length)
    (htag : tailKillTauChunk0030Rows[off].tag = 2) :
    tailKillTauChunk0030Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0030_witness_bound_ok off hoff htag


def tailKillTauChunk0031RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0031Start tailKillTauChunk0031Rows

theorem tailKillTauChunk0031_rows_match :
    tailKillTauChunk0031RowsMatch = true := by
  decide

def tailKillTauChunk0031WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0031Rows

theorem tailKillTauChunk0031_witness_bound_ok :
    tailKillTauChunk0031WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0031_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0031Rows.length) :
    RowValid tailKillTauChunk0031Rows[off] :=
  tailKillTauChunk0031_row_valid tailKillTauChunk0031Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0031_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0031Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0031Rows[off] (tailKillTauChunk0031Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0031_rows_match off hoff

theorem tailKillTauChunk0031_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0031Rows.length)
    (htag : tailKillTauChunk0031Rows[off].tag = 2) :
    tailKillTauChunk0031Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0031_witness_bound_ok off hoff htag


def tailKillTauChunk0032RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0032Start tailKillTauChunk0032Rows

theorem tailKillTauChunk0032_rows_match :
    tailKillTauChunk0032RowsMatch = true := by
  decide

def tailKillTauChunk0032WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0032Rows

theorem tailKillTauChunk0032_witness_bound_ok :
    tailKillTauChunk0032WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0032_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0032Rows.length) :
    RowValid tailKillTauChunk0032Rows[off] :=
  tailKillTauChunk0032_row_valid tailKillTauChunk0032Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0032_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0032Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0032Rows[off] (tailKillTauChunk0032Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0032_rows_match off hoff

theorem tailKillTauChunk0032_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0032Rows.length)
    (htag : tailKillTauChunk0032Rows[off].tag = 2) :
    tailKillTauChunk0032Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0032_witness_bound_ok off hoff htag


def tailKillTauChunk0033RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0033Start tailKillTauChunk0033Rows

theorem tailKillTauChunk0033_rows_match :
    tailKillTauChunk0033RowsMatch = true := by
  decide

def tailKillTauChunk0033WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0033Rows

theorem tailKillTauChunk0033_witness_bound_ok :
    tailKillTauChunk0033WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0033_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0033Rows.length) :
    RowValid tailKillTauChunk0033Rows[off] :=
  tailKillTauChunk0033_row_valid tailKillTauChunk0033Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0033_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0033Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0033Rows[off] (tailKillTauChunk0033Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0033_rows_match off hoff

theorem tailKillTauChunk0033_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0033Rows.length)
    (htag : tailKillTauChunk0033Rows[off].tag = 2) :
    tailKillTauChunk0033Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0033_witness_bound_ok off hoff htag


def tailKillTauChunk0034RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0034Start tailKillTauChunk0034Rows

theorem tailKillTauChunk0034_rows_match :
    tailKillTauChunk0034RowsMatch = true := by
  decide

def tailKillTauChunk0034WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0034Rows

theorem tailKillTauChunk0034_witness_bound_ok :
    tailKillTauChunk0034WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0034_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0034Rows.length) :
    RowValid tailKillTauChunk0034Rows[off] :=
  tailKillTauChunk0034_row_valid tailKillTauChunk0034Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0034_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0034Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0034Rows[off] (tailKillTauChunk0034Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0034_rows_match off hoff

theorem tailKillTauChunk0034_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0034Rows.length)
    (htag : tailKillTauChunk0034Rows[off].tag = 2) :
    tailKillTauChunk0034Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0034_witness_bound_ok off hoff htag


def tailKillTauChunk0035RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0035Start tailKillTauChunk0035Rows

theorem tailKillTauChunk0035_rows_match :
    tailKillTauChunk0035RowsMatch = true := by
  decide

def tailKillTauChunk0035WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0035Rows

theorem tailKillTauChunk0035_witness_bound_ok :
    tailKillTauChunk0035WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0035_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0035Rows.length) :
    RowValid tailKillTauChunk0035Rows[off] :=
  tailKillTauChunk0035_row_valid tailKillTauChunk0035Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0035_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0035Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0035Rows[off] (tailKillTauChunk0035Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0035_rows_match off hoff

theorem tailKillTauChunk0035_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0035Rows.length)
    (htag : tailKillTauChunk0035Rows[off].tag = 2) :
    tailKillTauChunk0035Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0035_witness_bound_ok off hoff htag


def tailKillTauChunk0036RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0036Start tailKillTauChunk0036Rows

theorem tailKillTauChunk0036_rows_match :
    tailKillTauChunk0036RowsMatch = true := by
  decide

def tailKillTauChunk0036WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0036Rows

theorem tailKillTauChunk0036_witness_bound_ok :
    tailKillTauChunk0036WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0036_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0036Rows.length) :
    RowValid tailKillTauChunk0036Rows[off] :=
  tailKillTauChunk0036_row_valid tailKillTauChunk0036Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0036_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0036Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0036Rows[off] (tailKillTauChunk0036Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0036_rows_match off hoff

theorem tailKillTauChunk0036_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0036Rows.length)
    (htag : tailKillTauChunk0036Rows[off].tag = 2) :
    tailKillTauChunk0036Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0036_witness_bound_ok off hoff htag


def tailKillTauChunk0037RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0037Start tailKillTauChunk0037Rows

theorem tailKillTauChunk0037_rows_match :
    tailKillTauChunk0037RowsMatch = true := by
  decide

def tailKillTauChunk0037WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0037Rows

theorem tailKillTauChunk0037_witness_bound_ok :
    tailKillTauChunk0037WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0037_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0037Rows.length) :
    RowValid tailKillTauChunk0037Rows[off] :=
  tailKillTauChunk0037_row_valid tailKillTauChunk0037Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0037_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0037Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0037Rows[off] (tailKillTauChunk0037Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0037_rows_match off hoff

theorem tailKillTauChunk0037_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0037Rows.length)
    (htag : tailKillTauChunk0037Rows[off].tag = 2) :
    tailKillTauChunk0037Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0037_witness_bound_ok off hoff htag


def tailKillTauChunk0038RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0038Start tailKillTauChunk0038Rows

theorem tailKillTauChunk0038_rows_match :
    tailKillTauChunk0038RowsMatch = true := by
  decide

def tailKillTauChunk0038WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0038Rows

theorem tailKillTauChunk0038_witness_bound_ok :
    tailKillTauChunk0038WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0038_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0038Rows.length) :
    RowValid tailKillTauChunk0038Rows[off] :=
  tailKillTauChunk0038_row_valid tailKillTauChunk0038Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0038_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0038Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0038Rows[off] (tailKillTauChunk0038Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0038_rows_match off hoff

theorem tailKillTauChunk0038_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0038Rows.length)
    (htag : tailKillTauChunk0038Rows[off].tag = 2) :
    tailKillTauChunk0038Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0038_witness_bound_ok off hoff htag


def tailKillTauChunk0039RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0039Start tailKillTauChunk0039Rows

theorem tailKillTauChunk0039_rows_match :
    tailKillTauChunk0039RowsMatch = true := by
  decide

def tailKillTauChunk0039WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0039Rows

theorem tailKillTauChunk0039_witness_bound_ok :
    tailKillTauChunk0039WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0039_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0039Rows.length) :
    RowValid tailKillTauChunk0039Rows[off] :=
  tailKillTauChunk0039_row_valid tailKillTauChunk0039Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0039_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0039Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0039Rows[off] (tailKillTauChunk0039Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0039_rows_match off hoff

theorem tailKillTauChunk0039_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0039Rows.length)
    (htag : tailKillTauChunk0039Rows[off].tag = 2) :
    tailKillTauChunk0039Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0039_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
