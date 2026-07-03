import Erdos647TailKillTauFinitePrefixSemantic
import Erdos647TailKillTauProofChunks.Chunk0040
import Erdos647TailKillTauProofChunks.Chunk0041
import Erdos647TailKillTauProofChunks.Chunk0042
import Erdos647TailKillTauProofChunks.Chunk0043
import Erdos647TailKillTauProofChunks.Chunk0044
import Erdos647TailKillTauProofChunks.Chunk0045
import Erdos647TailKillTauProofChunks.Chunk0046
import Erdos647TailKillTauProofChunks.Chunk0047
import Erdos647TailKillTauProofChunks.Chunk0048
import Erdos647TailKillTauProofChunks.Chunk0049

/-!
# TailKill tau finite-prefix chunk interfaces, group 04

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

def tailKillTauChunk0040RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0040Start tailKillTauChunk0040Rows

theorem tailKillTauChunk0040_rows_match :
    tailKillTauChunk0040RowsMatch = true := by
  decide

def tailKillTauChunk0040WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0040Rows

theorem tailKillTauChunk0040_witness_bound_ok :
    tailKillTauChunk0040WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0040_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0040Rows.length) :
    RowValid tailKillTauChunk0040Rows[off] :=
  tailKillTauChunk0040_row_valid tailKillTauChunk0040Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0040_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0040Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0040Rows[off] (tailKillTauChunk0040Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0040_rows_match off hoff

theorem tailKillTauChunk0040_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0040Rows.length)
    (htag : tailKillTauChunk0040Rows[off].tag = 2) :
    tailKillTauChunk0040Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0040_witness_bound_ok off hoff htag


def tailKillTauChunk0041RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0041Start tailKillTauChunk0041Rows

theorem tailKillTauChunk0041_rows_match :
    tailKillTauChunk0041RowsMatch = true := by
  decide

def tailKillTauChunk0041WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0041Rows

theorem tailKillTauChunk0041_witness_bound_ok :
    tailKillTauChunk0041WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0041_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0041Rows.length) :
    RowValid tailKillTauChunk0041Rows[off] :=
  tailKillTauChunk0041_row_valid tailKillTauChunk0041Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0041_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0041Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0041Rows[off] (tailKillTauChunk0041Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0041_rows_match off hoff

theorem tailKillTauChunk0041_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0041Rows.length)
    (htag : tailKillTauChunk0041Rows[off].tag = 2) :
    tailKillTauChunk0041Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0041_witness_bound_ok off hoff htag


def tailKillTauChunk0042RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0042Start tailKillTauChunk0042Rows

theorem tailKillTauChunk0042_rows_match :
    tailKillTauChunk0042RowsMatch = true := by
  decide

def tailKillTauChunk0042WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0042Rows

theorem tailKillTauChunk0042_witness_bound_ok :
    tailKillTauChunk0042WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0042_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0042Rows.length) :
    RowValid tailKillTauChunk0042Rows[off] :=
  tailKillTauChunk0042_row_valid tailKillTauChunk0042Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0042_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0042Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0042Rows[off] (tailKillTauChunk0042Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0042_rows_match off hoff

theorem tailKillTauChunk0042_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0042Rows.length)
    (htag : tailKillTauChunk0042Rows[off].tag = 2) :
    tailKillTauChunk0042Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0042_witness_bound_ok off hoff htag


def tailKillTauChunk0043RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0043Start tailKillTauChunk0043Rows

theorem tailKillTauChunk0043_rows_match :
    tailKillTauChunk0043RowsMatch = true := by
  decide

def tailKillTauChunk0043WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0043Rows

theorem tailKillTauChunk0043_witness_bound_ok :
    tailKillTauChunk0043WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0043_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0043Rows.length) :
    RowValid tailKillTauChunk0043Rows[off] :=
  tailKillTauChunk0043_row_valid tailKillTauChunk0043Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0043_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0043Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0043Rows[off] (tailKillTauChunk0043Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0043_rows_match off hoff

theorem tailKillTauChunk0043_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0043Rows.length)
    (htag : tailKillTauChunk0043Rows[off].tag = 2) :
    tailKillTauChunk0043Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0043_witness_bound_ok off hoff htag


def tailKillTauChunk0044RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0044Start tailKillTauChunk0044Rows

theorem tailKillTauChunk0044_rows_match :
    tailKillTauChunk0044RowsMatch = true := by
  decide

def tailKillTauChunk0044WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0044Rows

theorem tailKillTauChunk0044_witness_bound_ok :
    tailKillTauChunk0044WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0044_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0044Rows.length) :
    RowValid tailKillTauChunk0044Rows[off] :=
  tailKillTauChunk0044_row_valid tailKillTauChunk0044Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0044_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0044Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0044Rows[off] (tailKillTauChunk0044Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0044_rows_match off hoff

theorem tailKillTauChunk0044_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0044Rows.length)
    (htag : tailKillTauChunk0044Rows[off].tag = 2) :
    tailKillTauChunk0044Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0044_witness_bound_ok off hoff htag


def tailKillTauChunk0045RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0045Start tailKillTauChunk0045Rows

theorem tailKillTauChunk0045_rows_match :
    tailKillTauChunk0045RowsMatch = true := by
  decide

def tailKillTauChunk0045WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0045Rows

theorem tailKillTauChunk0045_witness_bound_ok :
    tailKillTauChunk0045WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0045_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0045Rows.length) :
    RowValid tailKillTauChunk0045Rows[off] :=
  tailKillTauChunk0045_row_valid tailKillTauChunk0045Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0045_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0045Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0045Rows[off] (tailKillTauChunk0045Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0045_rows_match off hoff

theorem tailKillTauChunk0045_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0045Rows.length)
    (htag : tailKillTauChunk0045Rows[off].tag = 2) :
    tailKillTauChunk0045Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0045_witness_bound_ok off hoff htag


def tailKillTauChunk0046RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0046Start tailKillTauChunk0046Rows

theorem tailKillTauChunk0046_rows_match :
    tailKillTauChunk0046RowsMatch = true := by
  decide

def tailKillTauChunk0046WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0046Rows

theorem tailKillTauChunk0046_witness_bound_ok :
    tailKillTauChunk0046WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0046_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0046Rows.length) :
    RowValid tailKillTauChunk0046Rows[off] :=
  tailKillTauChunk0046_row_valid tailKillTauChunk0046Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0046_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0046Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0046Rows[off] (tailKillTauChunk0046Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0046_rows_match off hoff

theorem tailKillTauChunk0046_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0046Rows.length)
    (htag : tailKillTauChunk0046Rows[off].tag = 2) :
    tailKillTauChunk0046Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0046_witness_bound_ok off hoff htag


def tailKillTauChunk0047RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0047Start tailKillTauChunk0047Rows

theorem tailKillTauChunk0047_rows_match :
    tailKillTauChunk0047RowsMatch = true := by
  decide

def tailKillTauChunk0047WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0047Rows

theorem tailKillTauChunk0047_witness_bound_ok :
    tailKillTauChunk0047WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0047_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0047Rows.length) :
    RowValid tailKillTauChunk0047Rows[off] :=
  tailKillTauChunk0047_row_valid tailKillTauChunk0047Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0047_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0047Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0047Rows[off] (tailKillTauChunk0047Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0047_rows_match off hoff

theorem tailKillTauChunk0047_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0047Rows.length)
    (htag : tailKillTauChunk0047Rows[off].tag = 2) :
    tailKillTauChunk0047Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0047_witness_bound_ok off hoff htag


def tailKillTauChunk0048RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0048Start tailKillTauChunk0048Rows

theorem tailKillTauChunk0048_rows_match :
    tailKillTauChunk0048RowsMatch = true := by
  decide

def tailKillTauChunk0048WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0048Rows

theorem tailKillTauChunk0048_witness_bound_ok :
    tailKillTauChunk0048WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0048_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0048Rows.length) :
    RowValid tailKillTauChunk0048Rows[off] :=
  tailKillTauChunk0048_row_valid tailKillTauChunk0048Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0048_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0048Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0048Rows[off] (tailKillTauChunk0048Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0048_rows_match off hoff

theorem tailKillTauChunk0048_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0048Rows.length)
    (htag : tailKillTauChunk0048Rows[off].tag = 2) :
    tailKillTauChunk0048Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0048_witness_bound_ok off hoff htag


def tailKillTauChunk0049RowsMatch : Bool :=
  rowsMatchFrom tailKillTauChunk0049Start tailKillTauChunk0049Rows

theorem tailKillTauChunk0049_rows_match :
    tailKillTauChunk0049RowsMatch = true := by
  decide

def tailKillTauChunk0049WitnessBoundOk : Bool :=
  rowsWitnessBoundOk tailKillTauChunk0049Rows

theorem tailKillTauChunk0049_witness_bound_ok :
    tailKillTauChunk0049WitnessBoundOk = true := by
  decide

theorem tailKillTauChunk0049_row_valid_at
    (off : Nat) (hoff : off < tailKillTauChunk0049Rows.length) :
    RowValid tailKillTauChunk0049Rows[off] :=
  tailKillTauChunk0049_row_valid tailKillTauChunk0049Rows[off] (List.getElem_mem hoff)

theorem tailKillTauChunk0049_row_matches_at
    (off : Nat) (hoff : off < tailKillTauChunk0049Rows.length) :
    rowMatchesGlobalIndex tailKillTauChunk0049Rows[off] (tailKillTauChunk0049Start + off) = true :=
  rowsMatchFrom_get tailKillTauChunk0049_rows_match off hoff

theorem tailKillTauChunk0049_witness_bound_at
    (off : Nat) (hoff : off < tailKillTauChunk0049Rows.length)
    (htag : tailKillTauChunk0049Rows[off].tag = 2) :
    tailKillTauChunk0049Rows[off].k ≤ finitePrefixWitnessBound :=
  rowsWitnessBoundOk_get tailKillTauChunk0049_witness_bound_ok off hoff htag

end FinitePrefixChunkInterfaces
end Erdos647TailKillTauProofChunks
