import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0010
import Erdos647TailKillTauProofChunks.Chunk0011
import Erdos647TailKillTauProofChunks.Chunk0012
import Erdos647TailKillTauProofChunks.Chunk0013
import Erdos647TailKillTauProofChunks.Chunk0014
import Erdos647TailKillTauProofChunks.Chunk0015
import Erdos647TailKillTauProofChunks.Chunk0016
import Erdos647TailKillTauProofChunks.Chunk0017
import Erdos647TailKillTauProofChunks.Chunk0018
import Erdos647TailKillTauProofChunks.Chunk0019

/-!
# TailKill tau finite-prefix chunk interfaces, group 01

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

def tailKillTauChunk0010RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0010Start tailKillTauChunk0010Rows

theorem tailKillTauChunk0010_rows_match :
    tailKillTauChunk0010RowsMatch = true := by
  decide

def tailKillTauChunk0010WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0010Rows

theorem tailKillTauChunk0010_witness_bound_ok :
    tailKillTauChunk0010WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0010_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0010Rows.length) :
    RowValid tailKillTauChunk0010Rows[off] :=
  tailKillTauChunk0010_row_valid tailKillTauChunk0010Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0010_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0010Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0010Rows[off] (tailKillTauChunk0010Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0010_rows_match off hoff

theorem tailKillTauChunk0010_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0010Rows.length)
    (htag : tailKillTauChunk0010Rows[off].tag = 2) :
    tailKillTauChunk0010Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0010_witness_bound_ok off hoff htag


def tailKillTauChunk0011RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0011Start tailKillTauChunk0011Rows

theorem tailKillTauChunk0011_rows_match :
    tailKillTauChunk0011RowsMatch = true := by
  decide

def tailKillTauChunk0011WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0011Rows

theorem tailKillTauChunk0011_witness_bound_ok :
    tailKillTauChunk0011WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0011_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0011Rows.length) :
    RowValid tailKillTauChunk0011Rows[off] :=
  tailKillTauChunk0011_row_valid tailKillTauChunk0011Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0011_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0011Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0011Rows[off] (tailKillTauChunk0011Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0011_rows_match off hoff

theorem tailKillTauChunk0011_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0011Rows.length)
    (htag : tailKillTauChunk0011Rows[off].tag = 2) :
    tailKillTauChunk0011Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0011_witness_bound_ok off hoff htag


def tailKillTauChunk0012RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0012Start tailKillTauChunk0012Rows

theorem tailKillTauChunk0012_rows_match :
    tailKillTauChunk0012RowsMatch = true := by
  decide

def tailKillTauChunk0012WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0012Rows

theorem tailKillTauChunk0012_witness_bound_ok :
    tailKillTauChunk0012WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0012_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0012Rows.length) :
    RowValid tailKillTauChunk0012Rows[off] :=
  tailKillTauChunk0012_row_valid tailKillTauChunk0012Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0012_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0012Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0012Rows[off] (tailKillTauChunk0012Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0012_rows_match off hoff

theorem tailKillTauChunk0012_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0012Rows.length)
    (htag : tailKillTauChunk0012Rows[off].tag = 2) :
    tailKillTauChunk0012Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0012_witness_bound_ok off hoff htag


def tailKillTauChunk0013RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0013Start tailKillTauChunk0013Rows

theorem tailKillTauChunk0013_rows_match :
    tailKillTauChunk0013RowsMatch = true := by
  decide

def tailKillTauChunk0013WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0013Rows

theorem tailKillTauChunk0013_witness_bound_ok :
    tailKillTauChunk0013WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0013_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0013Rows.length) :
    RowValid tailKillTauChunk0013Rows[off] :=
  tailKillTauChunk0013_row_valid tailKillTauChunk0013Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0013_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0013Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0013Rows[off] (tailKillTauChunk0013Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0013_rows_match off hoff

theorem tailKillTauChunk0013_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0013Rows.length)
    (htag : tailKillTauChunk0013Rows[off].tag = 2) :
    tailKillTauChunk0013Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0013_witness_bound_ok off hoff htag


def tailKillTauChunk0014RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0014Start tailKillTauChunk0014Rows

theorem tailKillTauChunk0014_rows_match :
    tailKillTauChunk0014RowsMatch = true := by
  decide

def tailKillTauChunk0014WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0014Rows

theorem tailKillTauChunk0014_witness_bound_ok :
    tailKillTauChunk0014WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0014_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0014Rows.length) :
    RowValid tailKillTauChunk0014Rows[off] :=
  tailKillTauChunk0014_row_valid tailKillTauChunk0014Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0014_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0014Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0014Rows[off] (tailKillTauChunk0014Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0014_rows_match off hoff

theorem tailKillTauChunk0014_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0014Rows.length)
    (htag : tailKillTauChunk0014Rows[off].tag = 2) :
    tailKillTauChunk0014Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0014_witness_bound_ok off hoff htag


def tailKillTauChunk0015RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0015Start tailKillTauChunk0015Rows

theorem tailKillTauChunk0015_rows_match :
    tailKillTauChunk0015RowsMatch = true := by
  decide

def tailKillTauChunk0015WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0015Rows

theorem tailKillTauChunk0015_witness_bound_ok :
    tailKillTauChunk0015WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0015_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0015Rows.length) :
    RowValid tailKillTauChunk0015Rows[off] :=
  tailKillTauChunk0015_row_valid tailKillTauChunk0015Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0015_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0015Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0015Rows[off] (tailKillTauChunk0015Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0015_rows_match off hoff

theorem tailKillTauChunk0015_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0015Rows.length)
    (htag : tailKillTauChunk0015Rows[off].tag = 2) :
    tailKillTauChunk0015Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0015_witness_bound_ok off hoff htag


def tailKillTauChunk0016RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0016Start tailKillTauChunk0016Rows

theorem tailKillTauChunk0016_rows_match :
    tailKillTauChunk0016RowsMatch = true := by
  decide

def tailKillTauChunk0016WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0016Rows

theorem tailKillTauChunk0016_witness_bound_ok :
    tailKillTauChunk0016WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0016_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0016Rows.length) :
    RowValid tailKillTauChunk0016Rows[off] :=
  tailKillTauChunk0016_row_valid tailKillTauChunk0016Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0016_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0016Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0016Rows[off] (tailKillTauChunk0016Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0016_rows_match off hoff

theorem tailKillTauChunk0016_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0016Rows.length)
    (htag : tailKillTauChunk0016Rows[off].tag = 2) :
    tailKillTauChunk0016Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0016_witness_bound_ok off hoff htag


def tailKillTauChunk0017RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0017Start tailKillTauChunk0017Rows

theorem tailKillTauChunk0017_rows_match :
    tailKillTauChunk0017RowsMatch = true := by
  decide

def tailKillTauChunk0017WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0017Rows

theorem tailKillTauChunk0017_witness_bound_ok :
    tailKillTauChunk0017WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0017_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0017Rows.length) :
    RowValid tailKillTauChunk0017Rows[off] :=
  tailKillTauChunk0017_row_valid tailKillTauChunk0017Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0017_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0017Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0017Rows[off] (tailKillTauChunk0017Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0017_rows_match off hoff

theorem tailKillTauChunk0017_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0017Rows.length)
    (htag : tailKillTauChunk0017Rows[off].tag = 2) :
    tailKillTauChunk0017Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0017_witness_bound_ok off hoff htag


def tailKillTauChunk0018RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0018Start tailKillTauChunk0018Rows

theorem tailKillTauChunk0018_rows_match :
    tailKillTauChunk0018RowsMatch = true := by
  decide

def tailKillTauChunk0018WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0018Rows

theorem tailKillTauChunk0018_witness_bound_ok :
    tailKillTauChunk0018WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0018_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0018Rows.length) :
    RowValid tailKillTauChunk0018Rows[off] :=
  tailKillTauChunk0018_row_valid tailKillTauChunk0018Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0018_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0018Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0018Rows[off] (tailKillTauChunk0018Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0018_rows_match off hoff

theorem tailKillTauChunk0018_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0018Rows.length)
    (htag : tailKillTauChunk0018Rows[off].tag = 2) :
    tailKillTauChunk0018Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0018_witness_bound_ok off hoff htag


def tailKillTauChunk0019RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0019Start tailKillTauChunk0019Rows

theorem tailKillTauChunk0019_rows_match :
    tailKillTauChunk0019RowsMatch = true := by
  decide

def tailKillTauChunk0019WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0019Rows

theorem tailKillTauChunk0019_witness_bound_ok :
    tailKillTauChunk0019WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0019_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0019Rows.length) :
    RowValid tailKillTauChunk0019Rows[off] :=
  tailKillTauChunk0019_row_valid tailKillTauChunk0019Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0019_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0019Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0019Rows[off] (tailKillTauChunk0019Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0019_rows_match off hoff

theorem tailKillTauChunk0019_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0019Rows.length)
    (htag : tailKillTauChunk0019Rows[off].tag = 2) :
    tailKillTauChunk0019Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0019_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
