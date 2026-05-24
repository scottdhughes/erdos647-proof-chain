import Mathlib
import Bridge2
import Erdos647SieveCertificate

/-!
# Conditional finite-window divisor bounds

This file records a positive-direction, full-value theorem:

If the linear cofactors

`((L_K / k) * t - 1)` for `1 <= k <= K`

are prime and strictly larger than `k`, then the finite window

`tau(L_K * t - k) <= k + 2`

holds for all `1 <= k <= K`.

This theorem is separate from the Stage-1 no-solution frontier. It does
not close any of the `41` open residues and does not replace the
Stage-1 axiom wrapper.
-/

namespace Erdos647ConditionalFiniteWindow

open Finset

/-- The prefix least common multiple `lcm(1, ..., K)`. -/
def prefixLcm (K : ℕ) : ℕ :=
  (Finset.Icc 1 K).lcm id

/-- The linear cofactor appearing in the `k`-th shifted factorization. -/
def primeCofactor (K t k : ℕ) : ℕ :=
  (prefixLcm K / k) * t - 1

/-- Finite-window target predicate. -/
def WindowGood (K n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K → (Nat.divisors (n - k)).card ≤ k + 2

/-- Prime-cofactor hypothesis for the finite-window construction. -/
def PrimeCofactorHyp (K t : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K →
    Nat.Prime (primeCofactor K t k) ∧ k < primeCofactor K t k

theorem dvd_prefixLcm {K k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    k ∣ prefixLcm K := by
  classical
  simpa [prefixLcm] using (Finset.dvd_lcm (s := Finset.Icc 1 K) (f := id)
    (by simpa using Finset.mem_Icc.mpr ⟨hk1, hkK⟩))

theorem sub_eq_mul_primeCofactor {K t k : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    prefixLcm K * t - k = k * primeCofactor K t k := by
  have hdvd : k ∣ prefixLcm K := dvd_prefixLcm hk1 hkK
  rw [primeCofactor]
  have hmul : (((prefixLcm K / k) * k) * t) = k * ((prefixLcm K / k) * t) := by
    ring
  calc
    prefixLcm K * t - k
        = (((prefixLcm K / k) * k) * t) - k := by
            rw [Nat.div_mul_cancel hdvd]
    _ = k * ((prefixLcm K / k) * t) - k := by
          rw [hmul]
    _ = k * (((prefixLcm K / k) * t) - 1) := by
          conv_rhs => rw [Nat.mul_sub_left_distrib, Nat.mul_one]

theorem coprime_of_primeCofactor {K t k : ℕ}
    (hk1 : 1 ≤ k) (hprime : Nat.Prime (primeCofactor K t k))
    (hgt : k < primeCofactor K t k) :
    Nat.Coprime k (primeCofactor K t k) := by
  have hnot : ¬ primeCofactor K t k ∣ k := by
    intro hdiv
    have hle : primeCofactor K t k ≤ k := Nat.le_of_dvd hk1 hdiv
    exact Nat.not_le_of_lt hgt hle
  exact Nat.Coprime.symm (hprime.coprime_iff_not_dvd.mpr hnot)

private lemma divisors_card_prime {q : ℕ} (hq : Nat.Prime q) :
    q.divisors.card = 2 := by
  rw [Nat.Prime.divisors hq]
  exact Finset.card_pair hq.one_lt.ne

/-- Under the prime-cofactor hypothesis, the shifted value has exact divisor count
`2 * tau(k)`. -/
theorem tau_eq_two_mul_divisors {K t k : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hprime : Nat.Prime (primeCofactor K t k))
    (hgt : k < primeCofactor K t k) :
    (Nat.divisors (prefixLcm K * t - k)).card = 2 * (Nat.divisors k).card := by
  have hfactor : prefixLcm K * t - k = k * primeCofactor K t k :=
    sub_eq_mul_primeCofactor hk1 hkK
  have hcop : Nat.Coprime k (primeCofactor K t k) :=
    coprime_of_primeCofactor hk1 hprime hgt
  calc
    (Nat.divisors (prefixLcm K * t - k)).card
        = (Nat.divisors (k * primeCofactor K t k)).card := by
            rw [hfactor]
    _ = (Nat.divisors k).card * (Nat.divisors (primeCofactor K t k)).card := by
          rw [Bridge2.Nat.divisors_card_mul_of_coprime hcop]
    _ = (Nat.divisors k).card * 2 := by
          rw [divisors_card_prime hprime]
    _ = 2 * (Nat.divisors k).card := by
          ring

/-- Generic finite-window theorem, parameterized by the arithmetic bound
`2 * tau(k) <= k + 2` on the small factor. -/
theorem windowGood_of_primeCofactors
    {K t : ℕ}
    (hprime : PrimeCofactorHyp K t)
    (hsmall : ∀ k, 1 ≤ k → k ≤ K → 2 * (Nat.divisors k).card ≤ k + 2) :
    WindowGood K (prefixLcm K * t) := by
  intro k hk1 hkK
  obtain ⟨hqprime, hqgt⟩ := hprime k hk1 hkK
  have htau :
      (Nat.divisors (prefixLcm K * t - k)).card = 2 * (Nat.divisors k).card :=
    tau_eq_two_mul_divisors hk1 hkK hqprime hqgt
  rw [htau]
  exact hsmall k hk1 hkK

private theorem two_mul_divisors_card_le_add_two_upto80
    {k : ℕ} (hk1 : 1 ≤ k) (hk80 : k ≤ 80) :
    2 * (Nat.divisors k).card ≤ k + 2 := by
  interval_cases k <;> native_decide

/-- Concrete deterministic `K = 80` corollary. -/
theorem windowGood80_of_primeCofactors
    {t : ℕ} (hprime : PrimeCofactorHyp 80 t) :
    WindowGood 80 (prefixLcm 80 * t) := by
  refine windowGood_of_primeCofactors hprime ?_
  intro k hk1 hk80
  exact two_mul_divisors_card_le_add_two_upto80 hk1 hk80

/-- Concrete deterministic `K = 20` corollary. -/
theorem windowGood20_of_primeCofactors
    {t : ℕ} (hprime : PrimeCofactorHyp 20 t) :
    WindowGood 20 (prefixLcm 20 * t) := by
  refine windowGood_of_primeCofactors hprime ?_
  intro k hk1 hk20
  exact two_mul_divisors_card_le_add_two_upto80 hk1 (by omega)

theorem prefixLcm20_eq : prefixLcm 20 = 232792560 := by
  native_decide

theorem prefixLcm20_div_2520_eq : prefixLcm 20 / 2520 = 92378 := by
  native_decide

theorem residue_zero_mod_M_for_K20 (t : ℕ) :
    ((prefixLcm 20 / 2520) * t) % Erdos647SieveCertificate.M = 0 := by
  rw [prefixLcm20_div_2520_eq, show 92378 = 2 * Erdos647SieveCertificate.M by native_decide]
  simp [Nat.mul_mod]

end Erdos647ConditionalFiniteWindow
