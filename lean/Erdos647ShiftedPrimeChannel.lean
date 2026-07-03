import Mathlib
import Erdos647SieveCertificate
import Erdos647ValuationCore
import Erdos647ResiduePartitionStage1
import Erdos647ReductionChain
import ShapeDecomposition

/-!
# Shifted-prime channel for the Stage-1 open frontier

This file contains small structural support lemmas for the post-B1 pivot.
It does not close any Stage-1 open residue. The point is to formalize the
k = 1 channel collapse used in the shifted-prime theorem-design route:

* refine an open residue to `N = M * (529 * u + s) + r`;
* set `n = 2520 * N`;
* then `n - 1 ≡ 7 (mod 8)`, so the k = 1 survivor channel cannot be
  `1` or a square.

The remaining hard theorem is about divisor-rich shifts of primes
`P = n - 1` in these explicit arithmetic progressions.
-/

namespace Erdos647ShiftedPrimeChannel

/-- The mod-529 refinement used by the current open-sub-AP diagnostics. -/
def subAPMod : ℕ := 529

/-- Stage-1 sub-AP parameterization of `N`. -/
def NSubAP (r s u : ℕ) : ℕ :=
  Erdos647SieveCertificate.M * (subAPMod * u + s) + r

/-- The sub-AP parameterization lies over the base residue `r mod M`. -/
theorem NSubAP_mod_M (r s u : ℕ) (hr : r < Erdos647SieveCertificate.M) :
    NSubAP r s u % Erdos647SieveCertificate.M = r := by
  unfold NSubAP
  have hMpos : 0 < Erdos647SieveCertificate.M := by native_decide
  rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hr]

/-- Every `N` decomposes into a base residue mod `M`, a sub-AP residue
mod `529`, and a quotient. -/
theorem NSubAP_decompose (N : ℕ) :
    N =
      NSubAP (N % Erdos647SieveCertificate.M)
        ((N / Erdos647SieveCertificate.M) % subAPMod)
        ((N / Erdos647SieveCertificate.M) / subAPMod) := by
  unfold NSubAP
  have hq :
      N / Erdos647SieveCertificate.M =
        subAPMod * ((N / Erdos647SieveCertificate.M) / subAPMod) +
          (N / Erdos647SieveCertificate.M) % subAPMod := by
    simpa [Nat.mul_comm] using
      (Nat.div_add_mod (N / Erdos647SieveCertificate.M) subAPMod).symm
  have hN :
      N =
        Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) +
          N % Erdos647SieveCertificate.M := by
    simpa [Nat.mul_comm] using
      (Nat.div_add_mod N Erdos647SieveCertificate.M).symm
  calc
    N =
        Erdos647SieveCertificate.M * (N / Erdos647SieveCertificate.M) +
          N % Erdos647SieveCertificate.M := hN
    _ =
        Erdos647SieveCertificate.M *
            (subAPMod * ((N / Erdos647SieveCertificate.M) / subAPMod) +
              (N / Erdos647SieveCertificate.M) % subAPMod) +
          N % Erdos647SieveCertificate.M := by
        conv_lhs => rw [hq]
    _ =
        NSubAP (N % Erdos647SieveCertificate.M)
          ((N / Erdos647SieveCertificate.M) % subAPMod)
          ((N / Erdos647SieveCertificate.M) / subAPMod) := by
        unfold NSubAP
        ring

/-- The corresponding #647 candidate value `n = 2520 * N`. -/
def nSubAP (r s u : ℕ) : ℕ :=
  2520 * NSubAP r s u

/-- Shifted value `n - k`. -/
def F (r s u k : ℕ) : ℕ :=
  nSubAP r s u - k

/-- The k = 1 shifted value. -/
def F1 (r s u : ℕ) : ℕ :=
  F r s u 1

/-- `nSubAP` is always divisible by 8 because `8 | 2520`. -/
theorem eight_dvd_nSubAP (r s u : ℕ) :
    8 ∣ nSubAP r s u := by
  unfold nSubAP
  rcases (show 8 ∣ 2520 by native_decide) with ⟨c, hc⟩
  refine ⟨c * NSubAP r s u, ?_⟩
  rw [hc]
  ring

/-- The k = 1 value is always `7 mod 8`, provided the subtraction is
nontrivial. This is the arithmetic core of the shifted-prime channel
collapse. -/
theorem F1_mod_eight (r s u : ℕ) (hpos : 0 < nSubAP r s u) :
    F1 r s u % 8 = 7 := by
  rcases eight_dvd_nSubAP r s u with ⟨q, hq⟩
  have hqpos : 0 < q := by omega
  unfold F1 F
  rw [hq]
  have hsub : 8 * q - 1 = 8 * (q - 1) + 7 := by omega
  rw [hsub]
  omega

/-- Squares are never `7 mod 8`. -/
theorem square_mod_eight_ne_seven (a : ℕ) :
    a ^ 2 % 8 ≠ 7 := by
  intro h
  have hbad : ∀ z : ZMod 8, z ^ 2 ≠ (7 : ZMod 8) := by
    native_decide
  have hz : ((a : ZMod 8) ^ 2) = (7 : ZMod 8) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod 8)) h
    simpa [pow_two] using hc
  exact hbad (a : ZMod 8) hz

/-- Consequently the k = 1 channel value is never a square. -/
theorem F1_not_square (r s u a : ℕ) (hpos : 0 < nSubAP r s u) :
    F1 r s u ≠ a ^ 2 := by
  intro hs
  have hmod : a ^ 2 % 8 = 7 := by
    rw [← hs]
    exact F1_mod_eight r s u hpos
  exact square_mod_eight_ne_seven a hmod

/-- The k = 1 channel value is not `1`. -/
theorem F1_ne_one (r s u : ℕ) (hpos : 0 < nSubAP r s u) :
    F1 r s u ≠ 1 := by
  intro h
  have hmod := F1_mod_eight r s u hpos
  rw [h] at hmod
  omega

/-- The k = 1 channel value is positive. -/
theorem F1_pos (r s u : ℕ) (hpos : 0 < nSubAP r s u) :
    0 < F1 r s u := by
  have hmod := F1_mod_eight r s u hpos
  by_cases hzero : F1 r s u = 0
  · rw [hzero] at hmod
    omega
  · exact Nat.pos_of_ne_zero hzero

/-- If the k = 1 divisor budget holds, then the k = 1 channel is prime.

This packages the shape classification `τ(x) ≤ 3 ⇒ x ∈ {1, p, p²}` with
the mod-8 obstruction above. -/
theorem F1_prime_of_tau_le_three (r s u : ℕ) (hpos : 0 < nSubAP r s u)
    (h_tau : (Nat.divisors (F1 r s u)).card ≤ 3) :
    Nat.Prime (F1 r s u) := by
  have hFpos : 0 < F1 r s u := F1_pos r s u hpos
  have h4 : (Nat.divisors (F1 r s u)).card ≤ 4 := by omega
  rcases shape_decomposition (F1 r s u) hFpos h4 with
    h_one | ⟨p, hp, hprime⟩ | ⟨p, hp, hsquare⟩ |
      ⟨p, hp, hcube⟩ | ⟨p, q, hp, hq, hpq, hpq_eq⟩
  · exfalso
    exact F1_ne_one r s u hpos h_one
  · rw [hprime]
    exact hp
  · exfalso
    exact F1_not_square r s u p hpos hsquare
  · exfalso
    have h_card : (p ^ 3).divisors.card = 4 := by
      rw [Nat.divisors_prime_pow hp]
      simp
    rw [hcube, h_card] at h_tau
    omega
  · exfalso
    have hpne : p ≠ q := Nat.ne_of_lt hpq
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpne
    have hp_card : (Nat.divisors p).card = 2 := by
      rw [hp.divisors]
      exact Finset.card_pair hp.one_lt.ne
    have hq_card : (Nat.divisors q).card = 2 := by
      rw [hq.divisors]
      exact Finset.card_pair hq.one_lt.ne
    rw [hpq_eq, hco.card_divisors_mul, hp_card, hq_card] at h_tau
    omega

/-- Under the #647 predicate on a positive sub-AP value, the k = 1 survivor
channel is exactly prime. -/
theorem F1_prime_of_isErdos647 (r s u : ℕ)
    (hNpos : 0 < NSubAP r s u)
    (hE : Erdos647BridgeV1.IsErdos647 (nSubAP r s u)) :
    Nat.Prime (F1 r s u) := by
  have hnpos : 0 < nSubAP r s u := by
    unfold nSubAP
    positivity
  have hNge : 1 ≤ NSubAP r s u := Nat.succ_le_of_lt hNpos
  have hlt : 1 < 2520 * NSubAP r s u := by
    have hmul : 2520 ≤ 2520 * NSubAP r s u :=
      Nat.mul_le_mul_left 2520 hNge
    omega
  have hE' : Erdos647BridgeV1.IsErdos647 (2520 * NSubAP r s u) := by
    simpa [nSubAP] using hE
  have htau :
      (Nat.divisors (F1 r s u)).card ≤ 3 := by
    simpa [F1, F, nSubAP] using
      Erdos647ValuationCore.tau_bound_at_k (NSubAP r s u) 1 hE'
        (by decide) hlt
  exact F1_prime_of_tau_le_three r s u hnpos htau

/-- A bounded shifted-prime tail kill: some later shift has divisor count
above the #647 budget. -/
def TailKillUpTo (r s u K : ℕ) : Prop :=
  ∃ k : ℕ,
    2 ≤ k ∧ k ≤ K ∧ k < nSubAP r s u ∧
      k + 2 < (Nat.divisors (F r s u k)).card

/-- The theorem-design target for a fixed sub-AP point: once the k = 1
channel is prime, some bounded later shift kills it. -/
def ShiftedPrimeTailClosesAt (r s u K : ℕ) : Prop :=
  Nat.Prime (F1 r s u) → TailKillUpTo r s u K

/-- Pointwise shifted-prime tail closure. This is the non-uniform form used
when no global fixed window is expected: the allowed tail bound may depend
on the open residue, the mod-529 sub-AP residue, and the sub-AP parameter. -/
def ShiftedPrimeTailClosesBy (K : ℕ → ℕ → ℕ → ℕ) (r s u : ℕ) : Prop :=
  Nat.Prime (F1 r s u) → TailKillUpTo r s u (K r s u)

/-- Fixed-`K` shifted-prime closure over the active Stage-1 open residues,
after the large-`N` threshold used by the reduction chain. -/
def ShiftedPrimeOpenSubAPCloses (K : ℕ) : Prop :=
  ∀ r s u,
    r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
      s < subAPMod →
        84 < nSubAP r s u →
          ShiftedPrimeTailClosesAt r s u K

/-- Non-uniform shifted-prime closure over the active Stage-1 open residues.

This is the theorem-design surface for pointwise `K(r,s,u)` attacks. It is
weaker than a fixed-window theorem but still strong enough to discharge the
open Stage-1 hypothesis because each produced tail kill directly contradicts
`IsErdos647`. -/
def ShiftedPrimeOpenSubAPClosesBy (K : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ r s u,
    r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
      s < subAPMod →
        84 < nSubAP r s u →
          ShiftedPrimeTailClosesBy K r s u

/-- A fixed-window closure is a special case of the pointwise closure
schema, using a constant tail bound. -/
theorem shiftedPrimeOpenSubAPClosesBy_const (K : ℕ)
    (hclose : ShiftedPrimeOpenSubAPCloses K) :
    ShiftedPrimeOpenSubAPClosesBy (fun _ _ _ => K) := by
  intro r s u hOpen hs hlarge
  simpa [ShiftedPrimeTailClosesBy, ShiftedPrimeTailClosesAt] using
    hclose r s u hOpen hs hlarge

/-- Any concrete tail kill contradicts `IsErdos647`. -/
theorem not_isErdos647_of_tailKillUpTo (r s u K : ℕ)
    (hkill : TailKillUpTo r s u K) :
    ¬ Erdos647BridgeV1.IsErdos647 (nSubAP r s u) := by
  rcases hkill with ⟨k, hk2, _hK, hklt, htau⟩
  have hk1 : 1 ≤ k := by omega
  have hnot :
      ¬ Erdos647BridgeV1.IsErdos647 (2520 * NSubAP r s u) :=
    Erdos647ValuationCore.not_isErdos647_of_tau_gt_at
      (N := NSubAP r s u) (k := k) hk1 (by simpa [nSubAP] using hklt)
      (by simpa [F, nSubAP] using htau)
  simpa [nSubAP] using hnot

/-- If the shifted-prime tail closes at `(r,s,u,K)`, then no #647 candidate
can live at that sub-AP point. -/
theorem not_isErdos647_of_shiftedPrimeTailClosesAt (r s u K : ℕ)
    (hNpos : 0 < NSubAP r s u)
    (hclose : ShiftedPrimeTailClosesAt r s u K) :
    ¬ Erdos647BridgeV1.IsErdos647 (nSubAP r s u) := by
  intro hE
  have hprime : Nat.Prime (F1 r s u) :=
    F1_prime_of_isErdos647 r s u hNpos hE
  exact not_isErdos647_of_tailKillUpTo r s u K (hclose hprime) hE

/-- Pointwise-tail variant of
`not_isErdos647_of_shiftedPrimeTailClosesAt`. -/
theorem not_isErdos647_of_shiftedPrimeTailClosesBy
    (K : ℕ → ℕ → ℕ → ℕ) (r s u : ℕ)
    (hNpos : 0 < NSubAP r s u)
    (hclose : ShiftedPrimeTailClosesBy K r s u) :
    ¬ Erdos647BridgeV1.IsErdos647 (nSubAP r s u) :=
  not_isErdos647_of_shiftedPrimeTailClosesAt r s u (K r s u) hNpos hclose

/-- Large-`N` open-residue no-solution wrapper from the shifted-prime
sub-AP target. This is the sound form needed by the reduction chain. -/
theorem large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPCloses
    (K : ℕ) (hclose : ShiftedPrimeOpenSubAPCloses K) :
    ∀ N,
      N % Erdos647SieveCertificate.M ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
        84 < 2520 * N →
          ¬ Erdos647BridgeV1.IsErdos647 (2520 * N) := by
  intro N hOpen hlarge hE
  let r := N % Erdos647SieveCertificate.M
  let s := (N / Erdos647SieveCertificate.M) % subAPMod
  let u := (N / Erdos647SieveCertificate.M) / subAPMod
  have hdecomp : N = NSubAP r s u := by
    simpa [r, s, u] using NSubAP_decompose N
  have hslt : s < subAPMod := by
    dsimp [s]
    exact Nat.mod_lt _ (by native_decide)
  have hlargeSub : 84 < nSubAP r s u := by
    rw [nSubAP]
    rw [← hdecomp]
    exact hlarge
  have hNpos : 0 < NSubAP r s u := by
    rw [← hdecomp]
    omega
  have hcloseAt : ShiftedPrimeTailClosesAt r s u K :=
    hclose r s u (by simpa [r] using hOpen) hslt hlargeSub
  have hnot :
      ¬ Erdos647BridgeV1.IsErdos647 (nSubAP r s u) :=
    not_isErdos647_of_shiftedPrimeTailClosesAt r s u K hNpos hcloseAt
  have hnEq : nSubAP r s u = 2520 * N := by
    rw [nSubAP]
    rw [← hdecomp]
  exact hnot (by simpa [hnEq] using hE)

/-- Large-`N` open-residue no-solution wrapper from a pointwise shifted-prime
sub-AP target. This is the non-uniform theorem-design route that avoids
reopening fixed-window B1 compute. -/
theorem large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPClosesBy
    (K : ℕ → ℕ → ℕ → ℕ) (hclose : ShiftedPrimeOpenSubAPClosesBy K) :
    ∀ N,
      N % Erdos647SieveCertificate.M ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
        84 < 2520 * N →
          ¬ Erdos647BridgeV1.IsErdos647 (2520 * N) := by
  intro N hOpen hlarge hE
  let r := N % Erdos647SieveCertificate.M
  let s := (N / Erdos647SieveCertificate.M) % subAPMod
  let u := (N / Erdos647SieveCertificate.M) / subAPMod
  have hdecomp : N = NSubAP r s u := by
    simpa [r, s, u] using NSubAP_decompose N
  have hslt : s < subAPMod := by
    dsimp [s]
    exact Nat.mod_lt _ (by native_decide)
  have hlargeSub : 84 < nSubAP r s u := by
    rw [nSubAP]
    rw [← hdecomp]
    exact hlarge
  have hNpos : 0 < NSubAP r s u := by
    rw [← hdecomp]
    omega
  have hcloseAt : ShiftedPrimeTailClosesBy K r s u :=
    hclose r s u (by simpa [r] using hOpen) hslt hlargeSub
  have hnot :
      ¬ Erdos647BridgeV1.IsErdos647 (nSubAP r s u) :=
    not_isErdos647_of_shiftedPrimeTailClosesBy K r s u hNpos hcloseAt
  have hnEq : nSubAP r s u = 2520 * N := by
    rw [nSubAP]
    rw [← hdecomp]
  exact hnot (by simpa [hnEq] using hE)

/-- Full conditional #647 theorem from a shifted-prime open-sub-AP closure
theorem. The only remaining mathematical input is `ShiftedPrimeOpenSubAPCloses`. -/
theorem erdos647_conditional_on_shiftedPrimeOpenSubAPCloses
    (K : ℕ) (hclose : ShiftedPrimeOpenSubAPCloses K) :
    ∀ n, 24 < n → ¬ Erdos647Main.Candidate n :=
  Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1_large
    (large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPCloses K hclose)

/-- Full conditional #647 theorem from a pointwise shifted-prime open-sub-AP
closure theorem. The remaining mathematical input is
`ShiftedPrimeOpenSubAPClosesBy`. -/
theorem erdos647_conditional_on_shiftedPrimeOpenSubAPClosesBy
    (K : ℕ → ℕ → ℕ → ℕ) (hclose : ShiftedPrimeOpenSubAPClosesBy K) :
    ∀ n, 24 < n → ¬ Erdos647Main.Candidate n :=
  Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1_large
    (large_openResiduesStage1_no_solution_of_shiftedPrimeOpenSubAPClosesBy K hclose)

end Erdos647ShiftedPrimeChannel
