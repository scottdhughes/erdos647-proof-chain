import Erdos647ShiftedPrimeChannel

/-!
# Shifted-prime tail mechanism-cover scaffold

This file is a theorem-interface scaffold for the shifted-prime tail route.
It deliberately proves no mechanism cover. Instead, it names the three
observed mechanism families and proves only the formal bridge from a
pointwise mechanism witness to the existing `ShiftedPrimeOpenSubAPClosesBy`
surface.

The mechanism predicates below are transparent placeholders for future
refinement. At this scaffold stage, proving one of them is exactly the
obligation to produce the corresponding divisor-rich shifted-prime kill.
-/

namespace Erdos647ShiftedPrimeChannel

/-- A Stage-1 open sub-AP coordinate, represented by the base residue `r`
and the mod-529 sub-AP residue `s`. The active/open hypotheses are kept
outside the structure so this remains a light coordinate object. -/
structure OpenSubAP where
  r : ℕ
  s : ℕ
deriving DecidableEq, Repr

/-- The shifted-prime channel value `P = F_1(r,s,u)`. -/
def P (C : OpenSubAP) (u : ℕ) : ℕ :=
  F1 C.r C.s u

/-- Project-native shifted value wrapper. -/
def Fshift (C : OpenSubAP) (k u : ℕ) : ℕ :=
  F C.r C.s u k

/-- The divisor-rich shifted-prime kill target in `d = k - 1` notation. -/
def ShiftedPrimeShiftKills (C : OpenSubAP) (u d : ℕ) : Prop :=
  d + 1 < nSubAP C.r C.s u ∧
    d + 3 < (Nat.divisors (Fshift C (d + 1) u)).card

/-- The mechanism labels surfaced by the high-tail atlas and W1-W4 review.
These are labels for future proof obligations, not proved mechanisms. -/
inductive ShiftedPrimeKillMechanism
  | accidentalWide
  | smallCofactorBoost
  | squarefulCofactor
deriving DecidableEq, Repr

/-- Accidental-wide obligation placeholder.

Future refinement should express that the reduced cofactor has enough
fresh distinct prime factors, together with the forced skeleton, to cross
the divisor threshold. -/
def KillByAccidentalWide (C : OpenSubAP) (u d : ℕ) : Prop :=
  ShiftedPrimeShiftKills C u d

/-- Small-cofactor-boost obligation placeholder.

Future refinement should express that the forced skeleton is already near
threshold and a prime/semiprime/small-composite cofactor pushes the shifted
value over budget. -/
def KillBySmallCofactorBoost (C : OpenSubAP) (u d : ℕ) : Prop :=
  ShiftedPrimeShiftKills C u d

/-- Squareful-cofactor obligation placeholder.

Future refinement should express repeated prime-power contribution in the
cofactor, with overlap against the forced skeleton controlled. -/
def KillBySquarefulCofactor (C : OpenSubAP) (u d : ℕ) : Prop :=
  ShiftedPrimeShiftKills C u d

/-- Generic mechanism wrapper. -/
def KillByMechanism
    (m : ShiftedPrimeKillMechanism) (C : OpenSubAP) (u d : ℕ) : Prop :=
  match m with
  | .accidentalWide => KillByAccidentalWide C u d
  | .smallCofactorBoost => KillBySmallCofactorBoost C u d
  | .squarefulCofactor => KillBySquarefulCofactor C u d

theorem accidentalWide_sound (C : OpenSubAP) (u d : ℕ) :
    KillByAccidentalWide C u d → ShiftedPrimeShiftKills C u d :=
  fun h => h

theorem smallCofactorBoost_sound (C : OpenSubAP) (u d : ℕ) :
    KillBySmallCofactorBoost C u d → ShiftedPrimeShiftKills C u d :=
  fun h => h

theorem squarefulCofactor_sound (C : OpenSubAP) (u d : ℕ) :
    KillBySquarefulCofactor C u d → ShiftedPrimeShiftKills C u d :=
  fun h => h

theorem killByMechanism_sound
    (m : ShiftedPrimeKillMechanism) (C : OpenSubAP) (u d : ℕ) :
    KillByMechanism m C u d → ShiftedPrimeShiftKills C u d := by
  cases m <;> intro h <;> exact h

/-- A pointwise mechanism witness at one prime-channel point.

The primary universal theorem surface is K-windowed: the witness shift is
bounded by the supplied project-native `K C.r C.s u`, not by a fixed early
window. Fixed early-window tables such as `d = 1..15` remain useful finite
diagnostics and soundness substrates, but they are not the universal cover
predicate. -/
def ShiftedPrimeMechanismWitness
    (K : ℕ → ℕ → ℕ → ℕ) (C : OpenSubAP) (u : ℕ) : Prop :=
  ∃ d : ℕ,
    1 ≤ d ∧ d + 1 ≤ K C.r C.s u ∧
      ∃ m : ShiftedPrimeKillMechanism, KillByMechanism m C u d

/-- Pointwise mechanism cover over all active Stage-1 open sub-APs. This
is the hard theorem obligation; this file does not prove it. -/
def ShiftedPrimeMechanismCoverBy (K : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ r s u,
    r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
      s < subAPMod →
        84 < nSubAP r s u →
          Nat.Prime (F1 r s u) →
            ShiftedPrimeMechanismWitness K ⟨r, s⟩ u

/-- Eventual pointwise mechanism cover, for a later finite-prefix wrapper. -/
def ShiftedPrimeMechanismCoverEventuallyBy
    (K : ℕ → ℕ → ℕ → ℕ) (U0 : ℕ → ℕ → ℕ) : Prop :=
  ∀ r s u,
    r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
      s < subAPMod →
        84 < nSubAP r s u →
          U0 r s ≤ u →
            Nat.Prime (F1 r s u) →
              ShiftedPrimeMechanismWitness K ⟨r, s⟩ u

/-- Finite-prefix verification obligation complementing an eventual cover. -/
def FinitePrefixMechanismVerifiedBy
    (K : ℕ → ℕ → ℕ → ℕ) (U0 : ℕ → ℕ → ℕ) : Prop :=
  ∀ r s u,
    r ∈ Erdos647ResiduePartitionStage1.openResiduesStage1 →
      s < subAPMod →
        84 < nSubAP r s u →
          u < U0 r s →
            Nat.Prime (F1 r s u) →
              ShiftedPrimeMechanismWitness K ⟨r, s⟩ u

/-- Eventual cover plus finite-prefix verification. -/
def ShiftedPrimeMechanismCoverWithFinitePrefixBy
    (K : ℕ → ℕ → ℕ → ℕ) (U0 : ℕ → ℕ → ℕ) : Prop :=
  ShiftedPrimeMechanismCoverEventuallyBy K U0 ∧
    FinitePrefixMechanismVerifiedBy K U0

/-- A mechanism witness produces the project-native `TailKillUpTo`. -/
theorem tailKillUpTo_of_mechanismWitness
    (K : ℕ → ℕ → ℕ → ℕ) (C : OpenSubAP) (u : ℕ)
    (hW : ShiftedPrimeMechanismWitness K C u) :
    TailKillUpTo C.r C.s u (K C.r C.s u) := by
  rcases hW with ⟨d, hd1, hdK, m, hm⟩
  have hkill : ShiftedPrimeShiftKills C u d :=
    killByMechanism_sound m C u d hm
  rcases hkill with ⟨hdn, hbudgetD⟩
  refine ⟨d + 1, ?_, hdK, ?_, ?_⟩
  · omega
  · simpa [Fshift] using hdn
  · have hbudget : (d + 1) + 2 < (Nat.divisors (F C.r C.s u (d + 1))).card := by
      simpa [Fshift] using hbudgetD
    exact hbudget

/-- Bridge from the hard mechanism-cover obligation to the existing
`ShiftedPrimeOpenSubAPClosesBy` theorem surface. -/
theorem shiftedPrimeOpenSubAPClosesBy_of_mechanismCover
    (K : ℕ → ℕ → ℕ → ℕ)
    (hCover : ShiftedPrimeMechanismCoverBy K) :
    ShiftedPrimeOpenSubAPClosesBy K := by
  intro r s u hOpen hs hlarge hprime
  exact tailKillUpTo_of_mechanismWitness K ⟨r, s⟩ u
    (hCover r s u hOpen hs hlarge hprime)

/-- Bridge from eventual cover plus finite-prefix verification to the
existing `ShiftedPrimeOpenSubAPClosesBy` theorem surface. -/
theorem shiftedPrimeOpenSubAPClosesBy_of_mechanismCoverWithFinitePrefix
    (K : ℕ → ℕ → ℕ → ℕ) (U0 : ℕ → ℕ → ℕ)
    (hCover : ShiftedPrimeMechanismCoverWithFinitePrefixBy K U0) :
    ShiftedPrimeOpenSubAPClosesBy K := by
  intro r s u hOpen hs hlarge hprime
  rcases hCover with ⟨heventual, hprefix⟩
  by_cases hU : U0 r s ≤ u
  · exact tailKillUpTo_of_mechanismWitness K ⟨r, s⟩ u
      (heventual r s u hOpen hs hlarge hU hprime)
  · have hu : u < U0 r s := by omega
    exact tailKillUpTo_of_mechanismWitness K ⟨r, s⟩ u
      (hprefix r s u hOpen hs hlarge hu hprime)

end Erdos647ShiftedPrimeChannel
