import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
# Computational certificate for the 12-form sieve on Erdős Problem #647

This file Lean-checks the central computational claim of the partial result:
no surviving residue class mod 46189 (under the 12-form sieve of the
strengthened modular-forcing reduction) admits a forced-prime killer
`k ∈ [1, 1000]` outside the already-covered set.

Discharged by `native_decide`.
-/

namespace Erdos647SieveCertificate

/-- The 12 form coefficients from the strengthened modular forcing
    (k = 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24). -/
def coeffs : List ℕ := [105, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520]

/-- The four sieve primes. -/
def sievePrimes : List ℕ := [11, 13, 17, 19]

/-- Modulus for the residue sieve. -/
def M : ℕ := 46189  -- = 11 * 13 * 17 * 19

/-- A residue `r` mod `M` survives the 12-form sieve iff for every coefficient
    `d` in `coeffs` and every prime `q` in `sievePrimes`, `d * r` is not
    congruent to `1` modulo `q`. -/
def survives (r : ℕ) : Bool :=
  coeffs.all fun d => sievePrimes.all fun q => decide (d * r % q ≠ 1)

/-- The 96 surviving residues mod 46189. -/
def survivingResidues : Finset ℕ :=
  (Finset.range M).filter fun r => survives r

/-- `omegaForced k r` counts the primes from `{2, 3, 5, 7, 11, 13, 17, 19}`
    forced to divide `2520 N - k` for any `N ≡ r (mod M)`. -/
def omegaForced (k r : ℕ) : ℕ :=
  ([2, 3, 5, 7].filter fun p => k % p = 0).length +
  (sievePrimes.filter fun q => (2520 * r) % q = k % q).length

/-- The k-values already discharged by the 12 modular-forcing cases. -/
def coveredK : Finset ℕ := {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 18, 24}

/-- **Verified computation.** For every surviving residue `r` mod `46189` and
    every `k` with `1 ≤ k ≤ 1000` and `k ∉ coveredK`, the forced-prime lower
    bound `2 ^ omegaForced k r` does not exceed `k + 2`. Equivalently, no
    surviving residue admits a forced-prime killer in this range.

    Discharged by `native_decide` (≈ 96 × 1000 evaluations of trivial
    arithmetic). -/
theorem no_forced_prime_killer :
    ∀ r ∈ survivingResidues,
      ∀ k, 1 ≤ k → k ≤ 1000 →
        k ∉ coveredK →
          2 ^ omegaForced k r ≤ k + 2 := by
  native_decide

/-- Sanity check: there are exactly 96 surviving residues. -/
theorem surviving_card : survivingResidues.card = 96 := by
  native_decide

end Erdos647SieveCertificate
