import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0200
import Erdos647TailKillTauProofChunks.Chunk0201
import Erdos647TailKillTauProofChunks.Chunk0202
import Erdos647TailKillTauProofChunks.Chunk0203
import Erdos647TailKillTauProofChunks.Chunk0204
import Erdos647TailKillTauProofChunks.Chunk0205
import Erdos647TailKillTauProofChunks.Chunk0206
import Erdos647TailKillTauProofChunks.Chunk0207
import Erdos647TailKillTauProofChunks.Chunk0208
import Erdos647TailKillTauProofChunks.Chunk0209

/-!
# TailKill tau finite-prefix chunk interfaces, group 20

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

def tailKillTauChunk0200RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0200Start tailKillTauChunk0200Rows

theorem tailKillTauChunk0200_rows_match :
    tailKillTauChunk0200RowsMatch = true := by
  decide

def tailKillTauChunk0200WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0200Rows

theorem tailKillTauChunk0200_witness_bound_ok :
    tailKillTauChunk0200WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0200_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0200Rows.length) :
    RowValid tailKillTauChunk0200Rows[off] :=
  tailKillTauChunk0200_row_valid tailKillTauChunk0200Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0200_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0200Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0200Rows[off] (tailKillTauChunk0200Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0200_rows_match off hoff

theorem tailKillTauChunk0200_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0200Rows.length)
    (htag : tailKillTauChunk0200Rows[off].tag = 2) :
    tailKillTauChunk0200Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0200_witness_bound_ok off hoff htag


def tailKillTauChunk0201RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0201Start tailKillTauChunk0201Rows

theorem tailKillTauChunk0201_rows_match :
    tailKillTauChunk0201RowsMatch = true := by
  decide

def tailKillTauChunk0201WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0201Rows

theorem tailKillTauChunk0201_witness_bound_ok :
    tailKillTauChunk0201WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0201_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0201Rows.length) :
    RowValid tailKillTauChunk0201Rows[off] :=
  tailKillTauChunk0201_row_valid tailKillTauChunk0201Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0201_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0201Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0201Rows[off] (tailKillTauChunk0201Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0201_rows_match off hoff

theorem tailKillTauChunk0201_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0201Rows.length)
    (htag : tailKillTauChunk0201Rows[off].tag = 2) :
    tailKillTauChunk0201Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0201_witness_bound_ok off hoff htag


def tailKillTauChunk0202RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0202Start tailKillTauChunk0202Rows

theorem tailKillTauChunk0202_rows_match :
    tailKillTauChunk0202RowsMatch = true := by
  decide

def tailKillTauChunk0202WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0202Rows

theorem tailKillTauChunk0202_witness_bound_ok :
    tailKillTauChunk0202WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0202_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0202Rows.length) :
    RowValid tailKillTauChunk0202Rows[off] :=
  tailKillTauChunk0202_row_valid tailKillTauChunk0202Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0202_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0202Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0202Rows[off] (tailKillTauChunk0202Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0202_rows_match off hoff

theorem tailKillTauChunk0202_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0202Rows.length)
    (htag : tailKillTauChunk0202Rows[off].tag = 2) :
    tailKillTauChunk0202Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0202_witness_bound_ok off hoff htag


def tailKillTauChunk0203RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0203Start tailKillTauChunk0203Rows

theorem tailKillTauChunk0203_rows_match :
    tailKillTauChunk0203RowsMatch = true := by
  decide

def tailKillTauChunk0203WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0203Rows

theorem tailKillTauChunk0203_witness_bound_ok :
    tailKillTauChunk0203WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0203_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0203Rows.length) :
    RowValid tailKillTauChunk0203Rows[off] :=
  tailKillTauChunk0203_row_valid tailKillTauChunk0203Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0203_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0203Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0203Rows[off] (tailKillTauChunk0203Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0203_rows_match off hoff

theorem tailKillTauChunk0203_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0203Rows.length)
    (htag : tailKillTauChunk0203Rows[off].tag = 2) :
    tailKillTauChunk0203Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0203_witness_bound_ok off hoff htag


def tailKillTauChunk0204RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0204Start tailKillTauChunk0204Rows

theorem tailKillTauChunk0204_rows_match :
    tailKillTauChunk0204RowsMatch = true := by
  decide

def tailKillTauChunk0204WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0204Rows

theorem tailKillTauChunk0204_witness_bound_ok :
    tailKillTauChunk0204WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0204_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0204Rows.length) :
    RowValid tailKillTauChunk0204Rows[off] :=
  tailKillTauChunk0204_row_valid tailKillTauChunk0204Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0204_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0204Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0204Rows[off] (tailKillTauChunk0204Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0204_rows_match off hoff

theorem tailKillTauChunk0204_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0204Rows.length)
    (htag : tailKillTauChunk0204Rows[off].tag = 2) :
    tailKillTauChunk0204Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0204_witness_bound_ok off hoff htag


def tailKillTauChunk0205RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0205Start tailKillTauChunk0205Rows

theorem tailKillTauChunk0205_rows_match :
    tailKillTauChunk0205RowsMatch = true := by
  decide

def tailKillTauChunk0205WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0205Rows

theorem tailKillTauChunk0205_witness_bound_ok :
    tailKillTauChunk0205WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0205_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0205Rows.length) :
    RowValid tailKillTauChunk0205Rows[off] :=
  tailKillTauChunk0205_row_valid tailKillTauChunk0205Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0205_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0205Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0205Rows[off] (tailKillTauChunk0205Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0205_rows_match off hoff

theorem tailKillTauChunk0205_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0205Rows.length)
    (htag : tailKillTauChunk0205Rows[off].tag = 2) :
    tailKillTauChunk0205Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0205_witness_bound_ok off hoff htag


def tailKillTauChunk0206RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0206Start tailKillTauChunk0206Rows

theorem tailKillTauChunk0206_rows_match :
    tailKillTauChunk0206RowsMatch = true := by
  decide

def tailKillTauChunk0206WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0206Rows

theorem tailKillTauChunk0206_witness_bound_ok :
    tailKillTauChunk0206WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0206_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0206Rows.length) :
    RowValid tailKillTauChunk0206Rows[off] :=
  tailKillTauChunk0206_row_valid tailKillTauChunk0206Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0206_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0206Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0206Rows[off] (tailKillTauChunk0206Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0206_rows_match off hoff

theorem tailKillTauChunk0206_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0206Rows.length)
    (htag : tailKillTauChunk0206Rows[off].tag = 2) :
    tailKillTauChunk0206Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0206_witness_bound_ok off hoff htag


def tailKillTauChunk0207RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0207Start tailKillTauChunk0207Rows

theorem tailKillTauChunk0207_rows_match :
    tailKillTauChunk0207RowsMatch = true := by
  decide

def tailKillTauChunk0207WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0207Rows

theorem tailKillTauChunk0207_witness_bound_ok :
    tailKillTauChunk0207WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0207_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0207Rows.length) :
    RowValid tailKillTauChunk0207Rows[off] :=
  tailKillTauChunk0207_row_valid tailKillTauChunk0207Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0207_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0207Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0207Rows[off] (tailKillTauChunk0207Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0207_rows_match off hoff

theorem tailKillTauChunk0207_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0207Rows.length)
    (htag : tailKillTauChunk0207Rows[off].tag = 2) :
    tailKillTauChunk0207Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0207_witness_bound_ok off hoff htag


def tailKillTauChunk0208RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0208Start tailKillTauChunk0208Rows

theorem tailKillTauChunk0208_rows_match :
    tailKillTauChunk0208RowsMatch = true := by
  decide

def tailKillTauChunk0208WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0208Rows

theorem tailKillTauChunk0208_witness_bound_ok :
    tailKillTauChunk0208WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0208_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0208Rows.length) :
    RowValid tailKillTauChunk0208Rows[off] :=
  tailKillTauChunk0208_row_valid tailKillTauChunk0208Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0208_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0208Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0208Rows[off] (tailKillTauChunk0208Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0208_rows_match off hoff

theorem tailKillTauChunk0208_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0208Rows.length)
    (htag : tailKillTauChunk0208Rows[off].tag = 2) :
    tailKillTauChunk0208Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0208_witness_bound_ok off hoff htag


def tailKillTauChunk0209RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0209Start tailKillTauChunk0209Rows

theorem tailKillTauChunk0209_rows_match :
    tailKillTauChunk0209RowsMatch = true := by
  decide

def tailKillTauChunk0209WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0209Rows

theorem tailKillTauChunk0209_witness_bound_ok :
    tailKillTauChunk0209WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0209_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0209Rows.length) :
    RowValid tailKillTauChunk0209Rows[off] :=
  tailKillTauChunk0209_row_valid tailKillTauChunk0209Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0209_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0209Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0209Rows[off] (tailKillTauChunk0209Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0209_rows_match off hoff

theorem tailKillTauChunk0209_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0209Rows.length)
    (htag : tailKillTauChunk0209Rows[off].tag = 2) :
    tailKillTauChunk0209Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0209_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
