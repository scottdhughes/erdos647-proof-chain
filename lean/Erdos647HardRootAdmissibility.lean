import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Hardy-Littlewood admissibility for the residual hard-root prime tuples

After the verified reduction (12-shape package + 96-residue sieve +
recursive caveat refactorization), Erdős Problem #647 reduces to two
hard residue classes `r ∈ {0, 24310} (mod 46189)`. On each, writing
`N = 46189 t + r`, the `α=0` branch of the 12-shape package yields a
collection of linear forms in `t` that must each be prime. After the
shape-elimination promotion of `k=20` from budget-3 to budget-2, this is
a 13-form prime tuple per hard root.

This file Lean-checks (via `native_decide`) that the 13-form prime tuple
on each hard root passes the Hardy-Littlewood local admissibility test
at every prime `p ≤ 97`: the union of forbidden `t`-residues mod `p`
across the 13 forms has size strictly less than `p`. Hence the singular
series is positive, and any contradiction proof must use a non-elementary
input.
-/

namespace Erdos647HardRootAdmissibility

/-- The 13 coefficients `d_k` such that the form is `d_k · N − 1` for
    the original 12-shape package, plus `k=20` after shape-elim
    promotion. -/
def hardRootCoeffs : List ℕ :=
  [2520, 1260, 840, 630, 504, 420, 315, 280, 252, 210, 140, 105, 126]

/-- Mod-inverse of `a` mod prime `p` via Fermat's little theorem. -/
def modInverse (a p : ℕ) : ℕ := Nat.pow a (p - 2) % p

/-- For the form `d · N − 1` at `N = 46189 t + r`, after primitivizing,
    return the forbidden residue mod `p` if `gcd(α, p) = 1`, else `none`.
    Here `α = d · 46189 / g`, `β = (d · r − 1) / g` where
    `g = gcd(d · 46189, |d · r − 1|)`. -/
def forbiddenResidueOfForm (d r p : ℕ) : Option ℕ :=
  let raw_a : ℤ := (d * 46189 : ℤ)
  let raw_b : ℤ := (d * r : ℤ) - 1
  let g : ℕ := Nat.gcd raw_a.natAbs raw_b.natAbs
  if g = 0 then none else
    let α : ℤ := raw_a / g
    let β : ℤ := raw_b / g
    let αp : ℕ := (α.natAbs) % p
    if αp = 0 then none else
      -- α t + β ≡ 0 mod p ⟹ t ≡ −β · α⁻¹ (mod p)
      let bp : ℕ := ((-β) % (p : ℤ)).toNat
      let inv : ℕ := modInverse αp p
      some ((inv * bp) % p)

/-- Number of distinct forbidden `t`-residues mod `p` across the 13 forms. -/
def numForbiddenAt (r p : ℕ) : ℕ :=
  let bad : List ℕ := hardRootCoeffs.filterMap fun d => forbiddenResidueOfForm d r p
  bad.dedup.length

/-- Admissibility predicate: fewer than `p` forbidden residues mod `p`. -/
def admissibleAt (r p : ℕ) : Bool :=
  decide (numForbiddenAt r p < p)

/-- Primes 2 through 97. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97]

/-- **Local admissibility for r = 0 at small primes**: the 13-form prime
    tuple passes Hardy-Littlewood admissibility at every prime ≤ 97.
    For primes p > 13, admissibility is automatic by pigeonhole (13 forms
    block ≤ 13 residues, but p > 13 has room). Thus full universal
    admissibility follows from this finite check at p ≤ 13. -/
theorem hard_root_r_zero_admissible :
    smallPrimes.all (fun p => admissibleAt 0 p) = true := by
  native_decide

/-- **Local admissibility for r = 24310**: same. -/
theorem hard_root_r_24310_admissible :
    smallPrimes.all (fun p => admissibleAt 24310 p) = true := by
  native_decide

/-! ## Task 7b: Large-prime admissibility by pigeonhole -/

/-- The number of forms in the hard-root prime tuple. -/
theorem hardRootCoeffs_length : hardRootCoeffs.length = 13 := by native_decide

/-- **Large-prime admissibility.** For any prime p > 13, admissibility
    holds automatically by pigeonhole: each of the 13 forms contributes
    at most 1 forbidden residue mod p (when p ∤ α, the unique solution
    of α t ≡ −β mod p; when p | α, the form is never ≡ 0 mod p so
    contributes 0 forbidden residues). Since 13 < p, the union of
    forbidden residues has size < p, leaving at least one admissible
    residue.

    We prove this by showing `numForbiddenAt r p ≤ 13` for all r, p,
    and then concluding admissibility when p > 13. -/
private theorem list_dedup_filterMap_le {α β : Type*} [DecidableEq β]
    (f : α → Option β) (l : List α) :
    (l.filterMap f).dedup.length ≤ l.length := by
  calc (l.filterMap f).dedup.length
      ≤ (l.filterMap f).length := List.Sublist.length_le (List.dedup_sublist _)
    _ ≤ l.length := List.length_filterMap_le f l

theorem numForbiddenAt_le_length (r p : ℕ) :
    numForbiddenAt r p ≤ hardRootCoeffs.length := by
  exact list_dedup_filterMap_le _ _

/-- **Admissibility at large primes.** For p > 13, `numForbiddenAt r p < p`. -/
theorem admissibleAt_large (r p : ℕ) (hp : 13 < p) :
    numForbiddenAt r p < p := by
  calc numForbiddenAt r p
      ≤ hardRootCoeffs.length := numForbiddenAt_le_length r p
    _ = 13 := hardRootCoeffs_length
    _ < p := hp

/-- **Universal admissibility for r = 0.** The 13-form prime tuple is
    admissible at EVERY prime: at p ≤ 13 by `native_decide`, at p > 13
    by `admissibleAt_large`. -/
theorem hard_root_r_zero_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 0 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 0 p h
  · -- p ≤ 13. The primes ≤ 13 are {2, 3, 5, 7, 11, 13}.
    -- Verified by the finite check in hard_root_r_zero_admissible.
    interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility for r = 24310.** Same structure. -/
theorem hard_root_r_24310_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 24310 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 24310 p h
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility for r = 1716.** -/
theorem hard_root_r_1716_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 1716 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 1716 p h
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility for r = 4862.** -/
theorem hard_root_r_4862_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 4862 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 4862 p h
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility for r = 16302.** -/
theorem hard_root_r_16302_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 16302 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 16302 p h
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility for r = 17160.** -/
theorem hard_root_r_17160_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAt 17160 p < p := by
  by_cases h : 13 < p
  · exact admissibleAt_large 17160 p h
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-! ## Full budget-≤ 3 tuple admissibility

The definitions above (`hardRootCoeffs`, `forbiddenResidueOfForm`,
`numForbiddenAt`) cover the 13-form core sub-tuple, and the universal
admissibility theorems above (`hard_root_r_X_admissible_all`) prove
that sub-tuple is admissible at every prime for each of the 5 hard
residues.

Each hard residue actually carries a LARGER budget-≤ 3 tuple
(13, 17, 15, 15, 17 forms for r ∈ {0, 1716, 4862, 16302, 17160}
respectively) obtained by adding residue-specific extras where
`gcd(α_k, β_k^{(r)})` picks up extra factors of the sieve primes
{11, 13, 17, 19}. For the extras with `k` coprime to `2520` (notably
`k = 13` at `r ∈ {1716, 16302}` and `k = 11` at `r = 17160`), the
generic form is `α_k t + β_k` with `β_k = d_k · r − b_k` and
`b_k = k / gcd(k, 2520) ≠ 1`. We therefore need a slightly more
general `forbiddenResidueOfFormPair` that accepts the pair `(d, b)`.

Full-tuple admissibility is proved below for all 5 hard residues.
-/

/-- Generalized form coefficient pair: `(d, b)` with form
    `α = d · 46189`, `β = d · r − b`. The `b = 1` case recovers the
    original `forbiddenResidueOfForm`. -/
def forbiddenResidueOfFormPair (d b r p : ℕ) : Option ℕ :=
  let raw_a : ℤ := (d * 46189 : ℤ)
  let raw_b : ℤ := (d * r : ℤ) - b
  let g : ℕ := Nat.gcd raw_a.natAbs raw_b.natAbs
  if g = 0 then none else
    let α : ℤ := raw_a / g
    let β : ℤ := raw_b / g
    let αp : ℕ := (α.natAbs) % p
    if αp = 0 then none else
      let bp : ℕ := ((-β) % (p : ℤ)).toNat
      let inv : ℕ := modInverse αp p
      some ((inv * bp) % p)

/-- Number of distinct forbidden `t`-residues mod `p` across a general
    list of `(d, b)` form coefficients. -/
def numForbiddenAtFull (coeffs : List (ℕ × ℕ)) (r p : ℕ) : ℕ :=
  let bad : List ℕ :=
    coeffs.filterMap fun fc => forbiddenResidueOfFormPair fc.1 fc.2 r p
  bad.dedup.length

/-- Full budget-≤ 3 tuple at `r = 0` (13 forms; identical to
    `hardRootCoeffs` with `b = 1` for every entry). -/
def fullCoeffs_r0 : List (ℕ × ℕ) :=
  [(2520, 1), (1260, 1), (840, 1), (630, 1), (504, 1), (420, 1),
   (315, 1), (280, 1), (252, 1), (210, 1), (140, 1), (126, 1), (105, 1)]

/-- Full budget-≤ 3 tuple at `r = 1716` (17 forms).
    k-set = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 15, 18, 20, 24, 30, 72}.
    The entry `(2520, 13)` is the `k = 13` extra (content `221 = 13·17`). -/
def fullCoeffs_r1716 : List (ℕ × ℕ) :=
  [(2520, 1), (1260, 1), (840, 1), (630, 1), (504, 1), (420, 1),
   (315, 1), (280, 1), (252, 1), (210, 1), (2520, 13), (168, 1),
   (140, 1), (126, 1), (105, 1), (84, 1), (35, 1)]

/-- Full budget-≤ 3 tuple at `r = 4862` (15 forms).
    k-set = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 90}. -/
def fullCoeffs_r4862 : List (ℕ × ℕ) :=
  [(2520, 1), (1260, 1), (840, 1), (630, 1), (504, 1), (420, 1),
   (315, 1), (280, 1), (252, 1), (210, 1), (180, 1), (140, 1),
   (126, 1), (105, 1), (28, 1)]

/-- Full budget-≤ 3 tuple at `r = 16302` (15 forms).
    k-set = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 18, 20, 24, 30}.
    The entry `(2520, 13)` is the `k = 13` extra (content `221 = 13·17`). -/
def fullCoeffs_r16302 : List (ℕ × ℕ) :=
  [(2520, 1), (1260, 1), (840, 1), (630, 1), (504, 1), (420, 1),
   (315, 1), (280, 1), (252, 1), (210, 1), (2520, 13), (140, 1),
   (126, 1), (105, 1), (84, 1)]

/-- Full budget-≤ 3 tuple at `r = 17160` (17 forms).
    k-set = {1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 18, 20, 24, 28, 36, 45}.
    The entry `(2520, 11)` is the `k = 11` extra (content `187 = 11·17`). -/
def fullCoeffs_r17160 : List (ℕ × ℕ) :=
  [(2520, 1), (1260, 1), (840, 1), (630, 1), (504, 1), (420, 1),
   (315, 1), (280, 1), (252, 1), (2520, 11), (210, 1), (140, 1),
   (126, 1), (105, 1), (90, 1), (70, 1), (56, 1)]

/-- Structural pigeonhole: the number of distinct forbidden residues
    is bounded by the number of form coefficients. Proof identical to
    `numForbiddenAt_le_length`. -/
theorem numForbiddenAtFull_le_length (coeffs : List (ℕ × ℕ)) (r p : ℕ) :
    numForbiddenAtFull coeffs r p ≤ coeffs.length :=
  list_dedup_filterMap_le _ _

/-- **Admissibility at large primes (full tuple).** For any prime `p`
    strictly larger than the tuple length, fewer than `p` residues are
    blocked. -/
theorem admissibleAtFull_large (coeffs : List (ℕ × ℕ)) (r p : ℕ)
    (hp : coeffs.length < p) : numForbiddenAtFull coeffs r p < p :=
  lt_of_le_of_lt (numForbiddenAtFull_le_length coeffs r p) hp

/-- Length of the full 13-form tuple at `r = 0`. -/
theorem fullCoeffs_r0_length : fullCoeffs_r0.length = 13 := by native_decide

/-- Length of the full 17-form tuple at `r = 1716`. -/
theorem fullCoeffs_r1716_length : fullCoeffs_r1716.length = 17 := by native_decide

/-- Length of the full 15-form tuple at `r = 4862`. -/
theorem fullCoeffs_r4862_length : fullCoeffs_r4862.length = 15 := by native_decide

/-- Length of the full 15-form tuple at `r = 16302`. -/
theorem fullCoeffs_r16302_length : fullCoeffs_r16302.length = 15 := by native_decide

/-- Length of the full 17-form tuple at `r = 17160`. -/
theorem fullCoeffs_r17160_length : fullCoeffs_r17160.length = 17 := by native_decide

/-- **Universal admissibility of the full budget-≤ 3 tuple at r = 0.**
    For every prime `p`, fewer than `p` residues are blocked. -/
theorem hard_root_r_0_full_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAtFull fullCoeffs_r0 0 p < p := by
  by_cases h : 13 < p
  · exact admissibleAtFull_large fullCoeffs_r0 0 p
      (fullCoeffs_r0_length ▸ h)
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility of the full budget-≤ 3 tuple at r = 1716.**
    For every prime `p`, fewer than `p` residues are blocked. Small
    primes (p ≤ 17) are checked by `native_decide`; large primes use
    the pigeonhole bound with tuple length 17. -/
theorem hard_root_r_1716_full_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAtFull fullCoeffs_r1716 1716 p < p := by
  by_cases h : 17 < p
  · exact admissibleAtFull_large fullCoeffs_r1716 1716 p
      (fullCoeffs_r1716_length ▸ h)
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility of the full budget-≤ 3 tuple at r = 4862.** -/
theorem hard_root_r_4862_full_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAtFull fullCoeffs_r4862 4862 p < p := by
  by_cases h : 15 < p
  · exact admissibleAtFull_large fullCoeffs_r4862 4862 p
      (fullCoeffs_r4862_length ▸ h)
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility of the full budget-≤ 3 tuple at r = 16302.** -/
theorem hard_root_r_16302_full_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAtFull fullCoeffs_r16302 16302 p < p := by
  by_cases h : 15 < p
  · exact admissibleAtFull_large fullCoeffs_r16302 16302 p
      (fullCoeffs_r16302_length ▸ h)
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

/-- **Universal admissibility of the full budget-≤ 3 tuple at r = 17160.** -/
theorem hard_root_r_17160_full_admissible_all (p : ℕ) (hp : Nat.Prime p) :
    numForbiddenAtFull fullCoeffs_r17160 17160 p < p := by
  by_cases h : 17 < p
  · exact admissibleAtFull_large fullCoeffs_r17160 17160 p
      (fullCoeffs_r17160_length ▸ h)
  · interval_cases p <;> simp_all [Nat.Prime] <;> native_decide

end Erdos647HardRootAdmissibility
