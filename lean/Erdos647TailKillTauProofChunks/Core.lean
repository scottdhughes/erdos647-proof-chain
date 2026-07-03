import Erdos647TailKillTauLowerCertificate

/-!
# TailKillUpTo tau proof chunk core

This module is the shared executable checker for the distributed tau-certificate
proof chunks.  It intentionally does not import TailKill slice trees, generated
evidence modules, adapters, route modules, bridge modules, or any finite-prefix
aggregate theorem.
-/

namespace Erdos647TailKillTauProofChunks

open Erdos647TailKillTauLowerCertificate

def subAPMod : Nat := 529
def stage1Mod : Nat := 46189

def nSubAP (r s u : Nat) : Nat :=
  2520 * (stage1Mod * (subAPMod * u + s) + r)

def fShift (r s u k : Nat) : Nat :=
  nSubAP r s u - k

def f1 (r s u : Nat) : Nat :=
  fShift r s u 1

structure CertRow where
  tag : Nat
  r : Nat
  s : Nat
  u : Nat
  k : Nat
  payload : List Nat
deriving DecidableEq, Repr

def noDupAux (seen : List Nat) : List Nat -> Bool
  | [] => true
  | d :: rest => if seen.contains d then false else noDupAux (d :: seen) rest

def noDup (xs : List Nat) : Bool :=
  noDupAux [] xs

def allDivisorsOf (n : Nat) : List Nat -> Bool
  | [] => true
  | d :: rest => d != 0 && n % d == 0 && allDivisorsOf n rest

def checkWitnessCert (r s u k : Nat) (ds : List Nat) : Bool :=
  let n := fShift r s u k
  2 <= k && k < nSubAP r s u && k + 2 < ds.length && noDup ds && allDivisorsOf n ds

def checkFactorCert (r s u d : Nat) : Bool :=
  let n := f1 r s u
  2 <= d && d < n && n % d == 0

def checkZeroOrOneCert (r s u : Nat) : Bool :=
  f1 r s u < 2

def checkRow (row : CertRow) : Bool :=
  match row.tag, row.payload with
  | 2, ds => checkWitnessCert row.r row.s row.u row.k ds
  | 1, [d] => checkFactorCert row.r row.s row.u d
  | 0, [] => checkZeroOrOneCert row.r row.s row.u
  | _, _ => false

def RowValid (row : CertRow) : Prop :=
  checkRow row = true

theorem row_valid_of_all_valid
    {rows : List CertRow} (h : rows.all checkRow = true)
    {row : CertRow} (hmem : row ∈ rows) :
    RowValid row := by
  exact (List.all_eq_true.mp h) row hmem

/--
Generic tau soundness hook used by downstream semantic interfaces.  Production
chunks prove executable validity; this theorem is the retained connection from
a TailKill witness divisor-array certificate to the `Nat.divisors` lower bound.
-/
theorem witness_tau_sound_of_array_cert
    {r s u k : Nat} {ds : Array Nat}
    (h : TailKillWitnessTauCertValid (fShift r s u k) k ds) :
    k + 2 < (Nat.divisors (fShift r s u k)).card :=
  tau_gt_k_plus_two_of_tailkill_witness_cert h

end Erdos647TailKillTauProofChunks
