import Erdos647ShiftedPrimeTailMechanismCover
import Erdos647TailKillTauProofChunks.Core

/-!
# Semantic bridge for TailKillUpTo tau proof chunks

This module contains only generic soundness lemmas for the distributed tau
certificate rows.  It does not import production proof chunks and does not
prove the finite-prefix, eventual-u, local-layer, shifted-prime, or global
theorem surfaces.
-/

namespace Erdos647TailKillTauProofChunks

namespace FinitePrefixSemantic

open Erdos647ShiftedPrimeChannel

def finitePrefixResidueCount : Nat := 41
def finitePrefixSCount : Nat := 529
def finitePrefixUCount : Nat := 101
def finitePrefixDomainSize : Nat := 2190589
def finitePrefixChunkSize : Nat := 10000
def finitePrefixWitnessBound : Nat := 10

def openResidueAt : Nat -> Nat
  | 0 => 0
  | 1 => 858
  | 2 => 1287
  | 3 => 1716
  | 4 => 2431
  | 5 => 2574
  | 6 => 4862
  | 7 => 5291
  | 8 => 6149
  | 9 => 8151
  | 10 => 9009
  | 11 => 9867
  | 12 => 10582
  | 13 => 12155
  | 14 => 12584
  | 15 => 13013
  | 16 => 13442
  | 17 => 16302
  | 18 => 17017
  | 19 => 17160
  | 20 => 18733
  | 21 => 19877
  | 22 => 20306
  | 23 => 20735
  | 24 => 21164
  | 25 => 24310
  | 26 => 24453
  | 27 => 25168
  | 28 => 27170
  | 29 => 28028
  | 30 => 28457
  | 31 => 29315
  | 32 => 29601
  | 33 => 31603
  | 34 => 32032
  | 35 => 32461
  | 36 => 35321
  | 37 => 36608
  | 38 => 37752
  | 39 => 38896
  | 40 => 44187
  | _ => 0

def residueIndex? : Nat -> Option Nat
  | 0 => some 0
  | 858 => some 1
  | 1287 => some 2
  | 1716 => some 3
  | 2431 => some 4
  | 2574 => some 5
  | 4862 => some 6
  | 5291 => some 7
  | 6149 => some 8
  | 8151 => some 9
  | 9009 => some 10
  | 9867 => some 11
  | 10582 => some 12
  | 12155 => some 13
  | 12584 => some 14
  | 13013 => some 15
  | 13442 => some 16
  | 16302 => some 17
  | 17017 => some 18
  | 17160 => some 19
  | 18733 => some 20
  | 19877 => some 21
  | 20306 => some 22
  | 20735 => some 23
  | 21164 => some 24
  | 24310 => some 25
  | 24453 => some 26
  | 25168 => some 27
  | 27170 => some 28
  | 28028 => some 29
  | 28457 => some 30
  | 29315 => some 31
  | 29601 => some 32
  | 31603 => some 33
  | 32032 => some 34
  | 32461 => some 35
  | 35321 => some 36
  | 36608 => some 37
  | 37752 => some 38
  | 38896 => some 39
  | 44187 => some 40
  | _ => none

def globalIndexOfResidueIndex (ri s u : Nat) : Nat :=
  ri * (finitePrefixSCount * finitePrefixUCount) + s * finitePrefixUCount + u

def expectedResidueIndexOfGlobal (idx : Nat) : Nat :=
  idx / (finitePrefixSCount * finitePrefixUCount)

def expectedSOfGlobal (idx : Nat) : Nat :=
  (idx % (finitePrefixSCount * finitePrefixUCount)) / finitePrefixUCount

def expectedUOfGlobal (idx : Nat) : Nat :=
  idx % finitePrefixUCount

def rowMatchesGlobalIndex (row : CertRow) (idx : Nat) : Bool :=
  row.r == openResidueAt (expectedResidueIndexOfGlobal idx) &&
    row.s == expectedSOfGlobal idx &&
      row.u == expectedUOfGlobal idx

def rowWitnessBoundOk (row : CertRow) : Bool :=
  row.tag != 2 || row.k <= finitePrefixWitnessBound

def rowsMatchFrom (start : Nat) (rows : List CertRow) : Bool :=
  rows.zipIdx start |>.all (fun item => rowMatchesGlobalIndex item.1 item.2)

def rowsWitnessBoundOk (rows : List CertRow) : Bool :=
  rows.all rowWitnessBoundOk

theorem rowMatchesGlobalIndex_true
    {row : CertRow} {idx : Nat}
    (h : rowMatchesGlobalIndex row idx = true) :
    row.r = openResidueAt (expectedResidueIndexOfGlobal idx) ∧
      row.s = expectedSOfGlobal idx ∧
        row.u = expectedUOfGlobal idx := by
  unfold rowMatchesGlobalIndex at h
  simp at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rowsMatchFrom_get
    {start : Nat} {rows : List CertRow}
    (hall : rowsMatchFrom start rows = true)
    (off : Nat) (hoff : off < rows.length) :
    rowMatchesGlobalIndex rows[off] (start + off) = true := by
  unfold rowsMatchFrom at hall
  have hmem :
      ∀ item ∈ rows.zipIdx start, rowMatchesGlobalIndex item.1 item.2 = true :=
    List.all_eq_true.mp hall
  exact (List.forall_mem_zipIdx.mp hmem) off hoff

theorem rowsWitnessBoundOk_get
    {rows : List CertRow}
    (hall : rowsWitnessBoundOk rows = true)
    (off : Nat) (hoff : off < rows.length)
    (htag : rows[off].tag = 2) :
    rows[off].k ≤ finitePrefixWitnessBound := by
  unfold rowsWitnessBoundOk at hall
  have hrow : rowWitnessBoundOk rows[off] = true :=
    (List.all_eq_true.mp hall) rows[off] (List.getElem_mem hoff)
  unfold rowWitnessBoundOk at hrow
  simp [htag] at hrow
  exact hrow

theorem tailKillUpTo_mono
    {r s u K K' : Nat}
    (hKK : K ≤ K') (h : TailKillUpTo r s u K) :
    TailKillUpTo r s u K' := by
  rcases h with ⟨k, hk2, hkK, hklt, htau⟩
  exact ⟨k, hk2, le_trans hkK hKK, hklt, htau⟩

theorem core_nSubAP_eq_project (r s u : Nat) :
    Erdos647TailKillTauProofChunks.nSubAP r s u =
      Erdos647ShiftedPrimeChannel.nSubAP r s u := by
  simp [Erdos647TailKillTauProofChunks.nSubAP,
    Erdos647TailKillTauProofChunks.stage1Mod,
    Erdos647TailKillTauProofChunks.subAPMod,
    Erdos647ShiftedPrimeChannel.nSubAP,
    Erdos647ShiftedPrimeChannel.NSubAP,
    Erdos647ShiftedPrimeChannel.subAPMod,
    Erdos647SieveCertificate.M]

theorem core_fShift_eq_project (r s u k : Nat) :
    Erdos647TailKillTauProofChunks.fShift r s u k =
      Erdos647ShiftedPrimeChannel.F r s u k := by
  simp [Erdos647TailKillTauProofChunks.fShift,
    Erdos647ShiftedPrimeChannel.F,
    core_nSubAP_eq_project]

theorem core_f1_eq_project (r s u : Nat) :
    Erdos647TailKillTauProofChunks.f1 r s u =
      Erdos647ShiftedPrimeChannel.F1 r s u := by
  simp [Erdos647TailKillTauProofChunks.f1,
    Erdos647ShiftedPrimeChannel.F1,
    core_fShift_eq_project]

theorem allDivisorsOf_true {n : Nat} {ds : List Nat}
    (h : allDivisorsOf n ds = true) :
    ∀ d ∈ ds, d ≠ 0 ∧ n % d = 0 := by
  induction ds with
  | nil =>
      simp
  | cons d rest ih =>
      simp [allDivisorsOf] at h
      rcases h with ⟨⟨hdne, hdmod⟩, hrest⟩
      intro x hx
      simp at hx
      rcases hx with hxd | hxrest
      · subst x
        exact ⟨hdne, hdmod⟩
      · exact ih hrest x hxrest

theorem noDupAux_true {seen ds : List Nat}
    (h : noDupAux seen ds = true) :
    ds.Nodup ∧ ∀ d ∈ ds, d ∉ seen := by
  induction ds generalizing seen with
  | nil =>
      simp
  | cons d rest ih =>
      unfold noDupAux at h
      by_cases hdseen : d ∈ seen
      · simp at h
        exact False.elim (h.1 hdseen)
      · simp at h
        rcases h with ⟨hd_not_seen, hrest_bool⟩
        rcases ih hrest_bool with ⟨hrest_nodup, hrest_not_seen⟩
        have hd_not_rest : d ∉ rest := by
          intro hdrest
          have hnot : d ∉ d :: seen := hrest_not_seen d hdrest
          exact hnot (by simp)
        constructor
        · exact List.nodup_cons.mpr ⟨hd_not_rest, hrest_nodup⟩
        · intro x hx
          simp at hx
          rcases hx with hxd | hxrest
          · subst x
            exact hd_not_seen
          · intro hxseen
            exact hrest_not_seen x hxrest (by simp [hxseen])

theorem noDup_true {ds : List Nat} (h : noDup ds = true) : ds.Nodup := by
  exact (noDupAux_true h).1

theorem witness_check_sound
    {r s u k : Nat} {ds : List Nat}
    (h : checkWitnessCert r s u k ds = true) :
    TailKillUpTo r s u k := by
  unfold checkWitnessCert at h
  simp at h
  rcases h with ⟨⟨⟨⟨hk2, hklt⟩, hcard⟩, hnodup_bool⟩, hdivs_bool⟩
  have hnodup : ds.Nodup := noDup_true hnodup_bool
  have hvalid : ∀ d ∈ ds, d ≠ 0 ∧
      (Erdos647TailKillTauProofChunks.fShift r s u k) % d = 0 :=
    allDivisorsOf_true hdivs_bool
  have hnpos : 0 < Erdos647TailKillTauProofChunks.fShift r s u k := by
    simp [Erdos647TailKillTauProofChunks.fShift]
    omega
  have hfin : Erdos647TailKillTauLowerCertificate.TauLowerFinsetCertValid
      (Erdos647TailKillTauProofChunks.fShift r s u k) (k + 2) ds.toFinset := by
    refine ⟨?_, ?_, ?_⟩
    · exact ne_of_gt hnpos
    · rw [List.toFinset_card_of_nodup hnodup]
      exact hcard
    · intro d hd
      exact hvalid d (List.mem_toFinset.mp hd)
  have htau_core :
      k + 2 <
        (Nat.divisors (Erdos647TailKillTauProofChunks.fShift r s u k)).card :=
    Erdos647TailKillTauLowerCertificate.tau_gt_of_valid_divisor_finset_cert hfin
  refine ⟨k, hk2, le_rfl, ?_, ?_⟩
  · simpa [core_nSubAP_eq_project] using hklt
  · simpa [core_fShift_eq_project] using htau_core

theorem factor_check_not_prime
    {r s u d : Nat}
    (h : checkFactorCert r s u d = true) :
    ¬ Nat.Prime (F1 r s u) := by
  unfold checkFactorCert at h
  simp at h
  rcases h with ⟨⟨hd2, hdlt⟩, hdmod⟩
  intro hp
  have hdvd : d ∣ F1 r s u := by
    exact Nat.dvd_of_mod_eq_zero (by simpa [core_f1_eq_project] using hdmod)
  exact (Nat.prime_def_lt'.mp hp).2 d hd2 hdlt hdvd

theorem zero_or_one_check_not_prime
    {r s u : Nat}
    (h : checkZeroOrOneCert r s u = true) :
    ¬ Nat.Prime (F1 r s u) := by
  unfold checkZeroOrOneCert at h
  simp at h
  intro hp
  exact (not_le_of_gt (by simpa [core_f1_eq_project] using h)) hp.two_le

theorem tailKillUpTo_mechanismWitness
    {r s u K : Nat}
    (h : TailKillUpTo r s u K) :
    ShiftedPrimeMechanismWitness (fun _ _ _ => K) ⟨r, s⟩ u := by
  rcases h with ⟨k, hk2, hkK, hklt, htau⟩
  refine ⟨k - 1, ?_, ?_, ShiftedPrimeKillMechanism.accidentalWide, ?_⟩
  · omega
  · simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hkK
  · change ShiftedPrimeShiftKills ⟨r, s⟩ u (k - 1)
    constructor
    · simpa [ShiftedPrimeShiftKills, Fshift, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hklt
    · have hrewrite : k - 1 + 3 = k + 2 := by omega
      simpa [ShiftedPrimeShiftKills, Fshift, hrewrite,
        Nat.sub_add_cancel (by omega : 1 ≤ k)] using htau

theorem tailKillUpTo_mechanismWitness_const
    {r s u K K' : Nat}
    (hKK : K ≤ K') (h : TailKillUpTo r s u K) :
    ShiftedPrimeMechanismWitness (fun _ _ _ => K') ⟨r, s⟩ u :=
  tailKillUpTo_mechanismWitness (tailKillUpTo_mono hKK h)

theorem row_valid_semantic
    {row : CertRow} (h : RowValid row) :
    match row.tag, row.payload with
    | 0, [] => ¬ Nat.Prime (F1 row.r row.s row.u)
    | 1, [_] => ¬ Nat.Prime (F1 row.r row.s row.u)
    | 2, _ => TailKillUpTo row.r row.s row.u row.k
    | _, _ => False := by
  rcases row with ⟨tag, r, s, u, k, payload⟩
  unfold RowValid checkRow at h
  dsimp at h ⊢
  cases tag with
  | zero =>
      cases payload with
      | nil =>
          exact zero_or_one_check_not_prime h
      | cons d rest =>
          simp at h
  | succ tag1 =>
      cases tag1 with
      | zero =>
          cases payload with
          | nil =>
              simp at h
          | cons d rest =>
              cases rest with
              | nil =>
                  exact factor_check_not_prime h
              | cons d2 rest2 =>
                  simp at h
      | succ tag2 =>
          cases tag2 with
          | zero =>
              exact witness_check_sound h
          | succ tag3 =>
              simp at h

theorem row_valid_prime_mechanismWitness
    {row : CertRow} {r s u : Nat}
    (hvalid : RowValid row)
    (hr : row.r = r) (hs : row.s = s) (hu : row.u = u)
    (hbound : row.tag = 2 -> row.k ≤ finitePrefixWitnessBound)
    (hprime : Nat.Prime (F1 r s u)) :
    ShiftedPrimeMechanismWitness
      (fun _ _ _ => finitePrefixWitnessBound) ⟨r, s⟩ u := by
  have hsem := row_valid_semantic hvalid
  rcases row with ⟨tag, rr, ss, uu, k, payload⟩
  dsimp at hr hs hu hbound hsem
  subst rr
  subst ss
  subst uu
  cases tag with
  | zero =>
      cases payload with
      | nil =>
          exact False.elim (hsem hprime)
      | cons d rest =>
          simp at hsem
  | succ tag1 =>
      cases tag1 with
      | zero =>
          cases payload with
          | nil =>
              simp at hsem
          | cons d rest =>
              cases rest with
              | nil =>
                  exact False.elim (hsem hprime)
              | cons d2 rest2 =>
                  simp at hsem
      | succ tag2 =>
          cases tag2 with
          | zero =>
              exact tailKillUpTo_mechanismWitness_const (hbound rfl) hsem
          | succ tag3 =>
              simp at hsem

end FinitePrefixSemantic

end Erdos647TailKillTauProofChunks
