import Erdos647TailKillTauFinitePrefixMechanism

/-!
# TailKill tau finite-prefix composition lift

This module lifts the banked finite-prefix mechanism theorem from the constant
bound `10` to any pointwise larger bound function `K`.

Certified scope:
* finite prefix `u < 101`;
* arbitrary witness-bound functions `K : Nat -> Nat -> Nat -> Nat` satisfying
  `10 <= K r s u` on that finite prefix;
* the paired finite-prefix/eventual-cover interface object.

It intentionally does not prove the eventual-u mechanism cover, local-layer
theorem, finite-prefix closure beyond this interface, shifted-prime theorem,
or global theorem.
-/

namespace Erdos647TailKillTauProofChunks
namespace FinitePrefixComposition

open Erdos647ShiftedPrimeChannel
open FinitePrefixSemantic

/-- Project-native `TailKillUpTo` is monotone in its witness bound. -/
theorem tailKillUpTo_bound_mono
    {r s u k K : Nat}
    (hK : k <= K) (h : TailKillUpTo r s u k) :
    TailKillUpTo r s u K :=
  FinitePrefixSemantic.tailKillUpTo_mono hK h

/-- Mechanism witnesses are monotone in the pointwise witness-bound function. -/
theorem shiftedPrimeMechanismWitness_mono
    {K K' : Nat -> Nat -> Nat -> Nat} {C : OpenSubAP} {u : Nat}
    (hK : K C.r C.s u <= K' C.r C.s u)
    (hW : ShiftedPrimeMechanismWitness K C u) :
    ShiftedPrimeMechanismWitness K' C u := by
  rcases hW with ⟨d, hd1, hdK, m, hm⟩
  exact ⟨d, hd1, le_trans hdK hK, m, hm⟩

/--
Lift the banked constant-10 finite-prefix theorem to any pointwise larger
bound function on `u < 101`.
-/
theorem tailKillFinitePrefixMechanismVerified_of_bound
    (K : Nat -> Nat -> Nat -> Nat)
    (hK : ∀ r s u, u < 101 -> 10 <= K r s u) :
    FinitePrefixMechanismVerifiedBy K (fun _ _ => 101) := by
  intro r s u hOpen hs hlarge hu hPrime
  have hbase :
      ShiftedPrimeMechanismWitness
        (fun _ _ _ => finitePrefixWitnessBound) ⟨r, s⟩ u :=
    FinitePrefixMechanism.tailKillFinitePrefixMechanismVerified
      r s u hOpen hs hlarge (by
        simpa [finitePrefixUCount] using hu) hPrime
  have hbound :
      finitePrefixWitnessBound <= K r s u := by
    simpa [finitePrefixWitnessBound] using hK r s u hu
  exact shiftedPrimeMechanismWitness_mono hbound hbase

/--
Composition scaffold: an eventual cover for the same `K`, plus finite-prefix
domination of the banked constant bound, gives the paired cover object.
-/
theorem tailKillMechanismCoverWithFinitePrefixBy_of_eventual_and_bound
    (K : Nat -> Nat -> Nat -> Nat)
    (hK : ∀ r s u, u < 101 -> 10 <= K r s u)
    (hEventual : ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)) :
    ShiftedPrimeMechanismCoverWithFinitePrefixBy K (fun _ _ => 101) := by
  exact ⟨hEventual, tailKillFinitePrefixMechanismVerified_of_bound K hK⟩

/-- Raise a candidate eventual bound to the finite-prefix floor only on `u < 101`. -/
def patchedK (K : Nat -> Nat -> Nat -> Nat) (r s u : Nat) : Nat :=
  if u < finitePrefixUCount then max finitePrefixWitnessBound (K r s u) else K r s u

/-- The patched bound dominates the banked finite-prefix bound on `u < 101`. -/
theorem patchedK_prefix_bound
    (K : Nat -> Nat -> Nat -> Nat) {r s u : Nat}
    (hu : u < 101) :
    10 <= patchedK K r s u := by
  have hprefix : u < finitePrefixUCount := by
    simpa [finitePrefixUCount] using hu
  simp [patchedK, hprefix, finitePrefixWitnessBound]

/-- The patched bound leaves the eventual range `u >= 101` unchanged. -/
theorem patchedK_eq_of_prefix_le
    (K : Nat -> Nat -> Nat -> Nat) {r s u : Nat}
    (hu : 101 <= u) :
    patchedK K r s u = K r s u := by
  have hnot : ¬ u < finitePrefixUCount := by
    intro hprefix
    have hu101 : u < 101 := by
      simpa [finitePrefixUCount] using hprefix
    exact Nat.not_lt_of_ge hu hu101
  simp [patchedK, hnot]

/--
An eventual cover for `K` after `101` is also an eventual cover for `patchedK K`,
because the patch changes only the finite prefix.
-/
theorem tailKillMechanismCoverEventually_patchedK_of_eventual
    (K : Nat -> Nat -> Nat -> Nat)
    (hEventual : ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)) :
    ShiftedPrimeMechanismCoverEventuallyBy (patchedK K) (fun _ _ => 101) := by
  intro r s u hOpen hs hlarge hU hPrime
  have hbase := hEventual r s u hOpen hs hlarge hU hPrime
  have hEq : patchedK K r s u = K r s u :=
    patchedK_eq_of_prefix_le K hU
  exact shiftedPrimeMechanismWitness_mono (by rw [hEq]) hbase

/--
Final finite-prefix composition form: a future eventual cover for `K` composes
with the automatically patched bound `patchedK K`.
-/
theorem tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual
    (K : Nat -> Nat -> Nat -> Nat)
    (hEventual : ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)) :
    ShiftedPrimeMechanismCoverWithFinitePrefixBy (patchedK K) (fun _ _ => 101) := by
  exact tailKillMechanismCoverWithFinitePrefixBy_of_eventual_and_bound
    (patchedK K)
    (fun r s u hu => patchedK_prefix_bound K hu)
    (tailKillMechanismCoverEventually_patchedK_of_eventual K hEventual)

/-!
Remaining theorem schema, not proved here:

For a chosen eventual witness-bound function `K`, prove

```
ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)
```

where `K` may depend on `r`, `s`, and `u`.  The theorem above then combines
that future eventual-u mathematics with the banked finite prefix.
-/

end FinitePrefixComposition
end Erdos647TailKillTauProofChunks
