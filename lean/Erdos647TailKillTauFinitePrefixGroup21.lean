import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0210
import Erdos647TailKillTauProofChunks.Chunk0211
import Erdos647TailKillTauProofChunks.Chunk0212
import Erdos647TailKillTauProofChunks.Chunk0213
import Erdos647TailKillTauProofChunks.Chunk0214
import Erdos647TailKillTauProofChunks.Chunk0215
import Erdos647TailKillTauProofChunks.Chunk0216
import Erdos647TailKillTauProofChunks.Chunk0217
import Erdos647TailKillTauProofChunks.Chunk0218
import Erdos647TailKillTauProofChunks.Chunk0219

/-!
# TailKill tau finite-prefix chunk interfaces, group 21

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

def tailKillTauChunk0210RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0210Start tailKillTauChunk0210Rows

theorem tailKillTauChunk0210_rows_match :
    tailKillTauChunk0210RowsMatch = true := by
  decide

def tailKillTauChunk0210WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0210Rows

theorem tailKillTauChunk0210_witness_bound_ok :
    tailKillTauChunk0210WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0210_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0210Rows.length) :
    RowValid tailKillTauChunk0210Rows[off] :=
  tailKillTauChunk0210_row_valid tailKillTauChunk0210Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0210_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0210Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0210Rows[off] (tailKillTauChunk0210Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0210_rows_match off hoff

theorem tailKillTauChunk0210_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0210Rows.length)
    (htag : tailKillTauChunk0210Rows[off].tag = 2) :
    tailKillTauChunk0210Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0210_witness_bound_ok off hoff htag


def tailKillTauChunk0211RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0211Start tailKillTauChunk0211Rows

theorem tailKillTauChunk0211_rows_match :
    tailKillTauChunk0211RowsMatch = true := by
  decide

def tailKillTauChunk0211WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0211Rows

theorem tailKillTauChunk0211_witness_bound_ok :
    tailKillTauChunk0211WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0211_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0211Rows.length) :
    RowValid tailKillTauChunk0211Rows[off] :=
  tailKillTauChunk0211_row_valid tailKillTauChunk0211Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0211_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0211Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0211Rows[off] (tailKillTauChunk0211Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0211_rows_match off hoff

theorem tailKillTauChunk0211_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0211Rows.length)
    (htag : tailKillTauChunk0211Rows[off].tag = 2) :
    tailKillTauChunk0211Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0211_witness_bound_ok off hoff htag


def tailKillTauChunk0212RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0212Start tailKillTauChunk0212Rows

theorem tailKillTauChunk0212_rows_match :
    tailKillTauChunk0212RowsMatch = true := by
  decide

def tailKillTauChunk0212WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0212Rows

theorem tailKillTauChunk0212_witness_bound_ok :
    tailKillTauChunk0212WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0212_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0212Rows.length) :
    RowValid tailKillTauChunk0212Rows[off] :=
  tailKillTauChunk0212_row_valid tailKillTauChunk0212Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0212_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0212Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0212Rows[off] (tailKillTauChunk0212Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0212_rows_match off hoff

theorem tailKillTauChunk0212_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0212Rows.length)
    (htag : tailKillTauChunk0212Rows[off].tag = 2) :
    tailKillTauChunk0212Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0212_witness_bound_ok off hoff htag


def tailKillTauChunk0213RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0213Start tailKillTauChunk0213Rows

theorem tailKillTauChunk0213_rows_match :
    tailKillTauChunk0213RowsMatch = true := by
  decide

def tailKillTauChunk0213WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0213Rows

theorem tailKillTauChunk0213_witness_bound_ok :
    tailKillTauChunk0213WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0213_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0213Rows.length) :
    RowValid tailKillTauChunk0213Rows[off] :=
  tailKillTauChunk0213_row_valid tailKillTauChunk0213Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0213_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0213Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0213Rows[off] (tailKillTauChunk0213Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0213_rows_match off hoff

theorem tailKillTauChunk0213_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0213Rows.length)
    (htag : tailKillTauChunk0213Rows[off].tag = 2) :
    tailKillTauChunk0213Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0213_witness_bound_ok off hoff htag


def tailKillTauChunk0214RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0214Start tailKillTauChunk0214Rows

theorem tailKillTauChunk0214_rows_match :
    tailKillTauChunk0214RowsMatch = true := by
  decide

def tailKillTauChunk0214WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0214Rows

theorem tailKillTauChunk0214_witness_bound_ok :
    tailKillTauChunk0214WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0214_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0214Rows.length) :
    RowValid tailKillTauChunk0214Rows[off] :=
  tailKillTauChunk0214_row_valid tailKillTauChunk0214Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0214_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0214Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0214Rows[off] (tailKillTauChunk0214Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0214_rows_match off hoff

theorem tailKillTauChunk0214_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0214Rows.length)
    (htag : tailKillTauChunk0214Rows[off].tag = 2) :
    tailKillTauChunk0214Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0214_witness_bound_ok off hoff htag


def tailKillTauChunk0215RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0215Start tailKillTauChunk0215Rows

theorem tailKillTauChunk0215_rows_match :
    tailKillTauChunk0215RowsMatch = true := by
  decide

def tailKillTauChunk0215WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0215Rows

theorem tailKillTauChunk0215_witness_bound_ok :
    tailKillTauChunk0215WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0215_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0215Rows.length) :
    RowValid tailKillTauChunk0215Rows[off] :=
  tailKillTauChunk0215_row_valid tailKillTauChunk0215Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0215_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0215Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0215Rows[off] (tailKillTauChunk0215Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0215_rows_match off hoff

theorem tailKillTauChunk0215_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0215Rows.length)
    (htag : tailKillTauChunk0215Rows[off].tag = 2) :
    tailKillTauChunk0215Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0215_witness_bound_ok off hoff htag


def tailKillTauChunk0216RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0216Start tailKillTauChunk0216Rows

theorem tailKillTauChunk0216_rows_match :
    tailKillTauChunk0216RowsMatch = true := by
  decide

def tailKillTauChunk0216WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0216Rows

theorem tailKillTauChunk0216_witness_bound_ok :
    tailKillTauChunk0216WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0216_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0216Rows.length) :
    RowValid tailKillTauChunk0216Rows[off] :=
  tailKillTauChunk0216_row_valid tailKillTauChunk0216Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0216_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0216Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0216Rows[off] (tailKillTauChunk0216Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0216_rows_match off hoff

theorem tailKillTauChunk0216_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0216Rows.length)
    (htag : tailKillTauChunk0216Rows[off].tag = 2) :
    tailKillTauChunk0216Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0216_witness_bound_ok off hoff htag


def tailKillTauChunk0217RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0217Start tailKillTauChunk0217Rows

theorem tailKillTauChunk0217_rows_match :
    tailKillTauChunk0217RowsMatch = true := by
  decide

def tailKillTauChunk0217WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0217Rows

theorem tailKillTauChunk0217_witness_bound_ok :
    tailKillTauChunk0217WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0217_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0217Rows.length) :
    RowValid tailKillTauChunk0217Rows[off] :=
  tailKillTauChunk0217_row_valid tailKillTauChunk0217Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0217_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0217Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0217Rows[off] (tailKillTauChunk0217Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0217_rows_match off hoff

theorem tailKillTauChunk0217_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0217Rows.length)
    (htag : tailKillTauChunk0217Rows[off].tag = 2) :
    tailKillTauChunk0217Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0217_witness_bound_ok off hoff htag


def tailKillTauChunk0218RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0218Start tailKillTauChunk0218Rows

theorem tailKillTauChunk0218_rows_match :
    tailKillTauChunk0218RowsMatch = true := by
  decide

def tailKillTauChunk0218WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0218Rows

theorem tailKillTauChunk0218_witness_bound_ok :
    tailKillTauChunk0218WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0218_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0218Rows.length) :
    RowValid tailKillTauChunk0218Rows[off] :=
  tailKillTauChunk0218_row_valid tailKillTauChunk0218Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0218_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0218Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0218Rows[off] (tailKillTauChunk0218Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0218_rows_match off hoff

theorem tailKillTauChunk0218_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0218Rows.length)
    (htag : tailKillTauChunk0218Rows[off].tag = 2) :
    tailKillTauChunk0218Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0218_witness_bound_ok off hoff htag


def tailKillTauChunk0219RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0219Start tailKillTauChunk0219Rows

theorem tailKillTauChunk0219_rows_match :
    tailKillTauChunk0219RowsMatch = true := by
  decide

def tailKillTauChunk0219WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0219Rows

theorem tailKillTauChunk0219_witness_bound_ok :
    tailKillTauChunk0219WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0219_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0219Rows.length) :
    RowValid tailKillTauChunk0219Rows[off] :=
  tailKillTauChunk0219_row_valid tailKillTauChunk0219Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0219_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0219Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0219Rows[off] (tailKillTauChunk0219Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0219_rows_match off hoff

theorem tailKillTauChunk0219_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0219Rows.length)
    (htag : tailKillTauChunk0219Rows[off].tag = 2) :
    tailKillTauChunk0219Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0219_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
