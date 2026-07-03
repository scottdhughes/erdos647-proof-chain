import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0080
import Erdos647TailKillTauProofChunks.Chunk0081
import Erdos647TailKillTauProofChunks.Chunk0082
import Erdos647TailKillTauProofChunks.Chunk0083
import Erdos647TailKillTauProofChunks.Chunk0084
import Erdos647TailKillTauProofChunks.Chunk0085
import Erdos647TailKillTauProofChunks.Chunk0086
import Erdos647TailKillTauProofChunks.Chunk0087
import Erdos647TailKillTauProofChunks.Chunk0088
import Erdos647TailKillTauProofChunks.Chunk0089

/-!
# TailKill tau finite-prefix chunk interfaces, group 08

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

def tailKillTauChunk0080RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0080Start tailKillTauChunk0080Rows

theorem tailKillTauChunk0080_rows_match :
    tailKillTauChunk0080RowsMatch = true := by
  decide

def tailKillTauChunk0080WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0080Rows

theorem tailKillTauChunk0080_witness_bound_ok :
    tailKillTauChunk0080WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0080_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0080Rows.length) :
    RowValid tailKillTauChunk0080Rows[off] :=
  tailKillTauChunk0080_row_valid tailKillTauChunk0080Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0080_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0080Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0080Rows[off] (tailKillTauChunk0080Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0080_rows_match off hoff

theorem tailKillTauChunk0080_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0080Rows.length)
    (htag : tailKillTauChunk0080Rows[off].tag = 2) :
    tailKillTauChunk0080Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0080_witness_bound_ok off hoff htag


def tailKillTauChunk0081RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0081Start tailKillTauChunk0081Rows

theorem tailKillTauChunk0081_rows_match :
    tailKillTauChunk0081RowsMatch = true := by
  decide

def tailKillTauChunk0081WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0081Rows

theorem tailKillTauChunk0081_witness_bound_ok :
    tailKillTauChunk0081WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0081_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0081Rows.length) :
    RowValid tailKillTauChunk0081Rows[off] :=
  tailKillTauChunk0081_row_valid tailKillTauChunk0081Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0081_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0081Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0081Rows[off] (tailKillTauChunk0081Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0081_rows_match off hoff

theorem tailKillTauChunk0081_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0081Rows.length)
    (htag : tailKillTauChunk0081Rows[off].tag = 2) :
    tailKillTauChunk0081Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0081_witness_bound_ok off hoff htag


def tailKillTauChunk0082RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0082Start tailKillTauChunk0082Rows

theorem tailKillTauChunk0082_rows_match :
    tailKillTauChunk0082RowsMatch = true := by
  decide

def tailKillTauChunk0082WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0082Rows

theorem tailKillTauChunk0082_witness_bound_ok :
    tailKillTauChunk0082WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0082_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0082Rows.length) :
    RowValid tailKillTauChunk0082Rows[off] :=
  tailKillTauChunk0082_row_valid tailKillTauChunk0082Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0082_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0082Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0082Rows[off] (tailKillTauChunk0082Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0082_rows_match off hoff

theorem tailKillTauChunk0082_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0082Rows.length)
    (htag : tailKillTauChunk0082Rows[off].tag = 2) :
    tailKillTauChunk0082Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0082_witness_bound_ok off hoff htag


def tailKillTauChunk0083RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0083Start tailKillTauChunk0083Rows

theorem tailKillTauChunk0083_rows_match :
    tailKillTauChunk0083RowsMatch = true := by
  decide

def tailKillTauChunk0083WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0083Rows

theorem tailKillTauChunk0083_witness_bound_ok :
    tailKillTauChunk0083WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0083_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0083Rows.length) :
    RowValid tailKillTauChunk0083Rows[off] :=
  tailKillTauChunk0083_row_valid tailKillTauChunk0083Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0083_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0083Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0083Rows[off] (tailKillTauChunk0083Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0083_rows_match off hoff

theorem tailKillTauChunk0083_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0083Rows.length)
    (htag : tailKillTauChunk0083Rows[off].tag = 2) :
    tailKillTauChunk0083Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0083_witness_bound_ok off hoff htag


def tailKillTauChunk0084RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0084Start tailKillTauChunk0084Rows

theorem tailKillTauChunk0084_rows_match :
    tailKillTauChunk0084RowsMatch = true := by
  decide

def tailKillTauChunk0084WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0084Rows

theorem tailKillTauChunk0084_witness_bound_ok :
    tailKillTauChunk0084WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0084_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0084Rows.length) :
    RowValid tailKillTauChunk0084Rows[off] :=
  tailKillTauChunk0084_row_valid tailKillTauChunk0084Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0084_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0084Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0084Rows[off] (tailKillTauChunk0084Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0084_rows_match off hoff

theorem tailKillTauChunk0084_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0084Rows.length)
    (htag : tailKillTauChunk0084Rows[off].tag = 2) :
    tailKillTauChunk0084Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0084_witness_bound_ok off hoff htag


def tailKillTauChunk0085RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0085Start tailKillTauChunk0085Rows

theorem tailKillTauChunk0085_rows_match :
    tailKillTauChunk0085RowsMatch = true := by
  decide

def tailKillTauChunk0085WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0085Rows

theorem tailKillTauChunk0085_witness_bound_ok :
    tailKillTauChunk0085WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0085_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0085Rows.length) :
    RowValid tailKillTauChunk0085Rows[off] :=
  tailKillTauChunk0085_row_valid tailKillTauChunk0085Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0085_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0085Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0085Rows[off] (tailKillTauChunk0085Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0085_rows_match off hoff

theorem tailKillTauChunk0085_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0085Rows.length)
    (htag : tailKillTauChunk0085Rows[off].tag = 2) :
    tailKillTauChunk0085Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0085_witness_bound_ok off hoff htag


def tailKillTauChunk0086RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0086Start tailKillTauChunk0086Rows

theorem tailKillTauChunk0086_rows_match :
    tailKillTauChunk0086RowsMatch = true := by
  decide

def tailKillTauChunk0086WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0086Rows

theorem tailKillTauChunk0086_witness_bound_ok :
    tailKillTauChunk0086WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0086_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0086Rows.length) :
    RowValid tailKillTauChunk0086Rows[off] :=
  tailKillTauChunk0086_row_valid tailKillTauChunk0086Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0086_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0086Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0086Rows[off] (tailKillTauChunk0086Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0086_rows_match off hoff

theorem tailKillTauChunk0086_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0086Rows.length)
    (htag : tailKillTauChunk0086Rows[off].tag = 2) :
    tailKillTauChunk0086Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0086_witness_bound_ok off hoff htag


def tailKillTauChunk0087RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0087Start tailKillTauChunk0087Rows

theorem tailKillTauChunk0087_rows_match :
    tailKillTauChunk0087RowsMatch = true := by
  decide

def tailKillTauChunk0087WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0087Rows

theorem tailKillTauChunk0087_witness_bound_ok :
    tailKillTauChunk0087WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0087_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0087Rows.length) :
    RowValid tailKillTauChunk0087Rows[off] :=
  tailKillTauChunk0087_row_valid tailKillTauChunk0087Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0087_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0087Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0087Rows[off] (tailKillTauChunk0087Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0087_rows_match off hoff

theorem tailKillTauChunk0087_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0087Rows.length)
    (htag : tailKillTauChunk0087Rows[off].tag = 2) :
    tailKillTauChunk0087Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0087_witness_bound_ok off hoff htag


def tailKillTauChunk0088RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0088Start tailKillTauChunk0088Rows

theorem tailKillTauChunk0088_rows_match :
    tailKillTauChunk0088RowsMatch = true := by
  decide

def tailKillTauChunk0088WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0088Rows

theorem tailKillTauChunk0088_witness_bound_ok :
    tailKillTauChunk0088WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0088_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0088Rows.length) :
    RowValid tailKillTauChunk0088Rows[off] :=
  tailKillTauChunk0088_row_valid tailKillTauChunk0088Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0088_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0088Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0088Rows[off] (tailKillTauChunk0088Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0088_rows_match off hoff

theorem tailKillTauChunk0088_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0088Rows.length)
    (htag : tailKillTauChunk0088Rows[off].tag = 2) :
    tailKillTauChunk0088Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0088_witness_bound_ok off hoff htag


def tailKillTauChunk0089RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0089Start tailKillTauChunk0089Rows

theorem tailKillTauChunk0089_rows_match :
    tailKillTauChunk0089RowsMatch = true := by
  decide

def tailKillTauChunk0089WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0089Rows

theorem tailKillTauChunk0089_witness_bound_ok :
    tailKillTauChunk0089WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0089_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0089Rows.length) :
    RowValid tailKillTauChunk0089Rows[off] :=
  tailKillTauChunk0089_row_valid tailKillTauChunk0089Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0089_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0089Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0089Rows[off] (tailKillTauChunk0089Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0089_rows_match off hoff

theorem tailKillTauChunk0089_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0089Rows.length)
    (htag : tailKillTauChunk0089Rows[off].tag = 2) :
    tailKillTauChunk0089Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0089_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
