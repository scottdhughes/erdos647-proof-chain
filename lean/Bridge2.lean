import Mathlib

/-!
# Bridge 2: IsErdos647 implies the 46189-residue restriction

This file formalizes Bridge 2 for Erdős Problem #647:
If `IsErdos647(2520 * N)` and `84 < 2520 * N`, then `N % 46189` belongs to the
set of 96 "surviving" residues.

All definitions are wrapped in namespace `Bridge2` to avoid collision with
the equivalent definitions in other `Erdos647*` modules. Conversion lemmas
to the main-package forms live in `Erdos647ReductionChain.lean`.
-/

namespace Bridge2

open Finset Nat

set_option maxHeartbeats 4000000

/-- `M = 46189 = 11 * 13 * 17 * 19`, the modulus for the sieve. -/
def M : ℕ := 46189

/-- The 12 coefficients `d = 2520/k` for the 12-shape set. -/
def coeffs : List ℕ := [105, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520]

/-- The four sieve primes. -/
def sievePrimes : List ℕ := [11, 13, 17, 19]

/-- `IsErdos647 n` means every `m ∈ [1, n)` satisfies `m + τ(m) ≤ n + 2`. -/
def IsErdos647 (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m < n → m + m.divisors.card ≤ n + 2

/-- A residue `r` survives if for every `(d, q)` pair, `d * r` is not `≡ 1 (mod q)`. -/
def survives (r : ℕ) : Bool :=
  coeffs.all fun d => sievePrimes.all fun q => d * r % q != 1

/-! ## Key divisor-count lemmas -/

/-- If `a ∣ b` and `b ≠ 0`, then `τ(a) ≤ τ(b)`. -/
lemma Nat.divisors_card_le_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    a.divisors.card ≤ b.divisors.card :=
  Finset.card_mono fun x hx =>
    Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hx) hab, hb⟩

/-- Multiplicativity of divisor count for coprime arguments. -/
lemma Nat.divisors_card_mul_of_coprime {a b : ℕ}
    (hcop : Nat.Coprime a b) :
    (a * b).divisors.card = a.divisors.card * b.divisors.card := by
  rw [← ArithmeticFunction.sigma_zero_apply, ← ArithmeticFunction.sigma_zero_apply,
      ← ArithmeticFunction.sigma_zero_apply]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop

/-- If `a ∣ m`, `p` is prime, `p ∣ m`, and `gcd(p, a) = 1`, then `τ(m) ≥ 2 * τ(a)`. -/
lemma Nat.divisors_card_ge_two_mul {a p m : ℕ} (ha : a ∣ m) (hp : Nat.Prime p)
    (hpm : p ∣ m) (hpa : Nat.Coprime p a) (hm : m ≠ 0) :
    m.divisors.card ≥ 2 * a.divisors.card := by
  have h_ap_dvd : a * p ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hpa.symm ha hpm
  have h_tau_le := Nat.divisors_card_le_of_dvd h_ap_dvd hm
  have h_tau_mul := Nat.divisors_card_mul_of_coprime hpa.symm
  have h_tau_p : p.divisors.card = 2 := by
    rw [Nat.Prime.divisors hp]; exact Finset.card_pair hp.one_lt.ne
  nlinarith

/-- For our 12 `k` values, `4 * τ(k) ≥ k + 3`. -/
lemma four_tau_k_ge (k : ℕ) (hk : k ∈ [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24]) :
    4 * k.divisors.card ≥ k + 3 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

/-! ## Witness extraction and modular arithmetic -/

/-- If `¬survives r`, there exist `d ∈ coeffs` and `q ∈ sievePrimes` with `d * r % q = 1`. -/
lemma not_survives_witness {r : ℕ} (h : survives r = false) :
    ∃ d ∈ coeffs, ∃ q ∈ sievePrimes, d * r % q = 1 := by
  by_contra h'
  push_neg at h'
  have : survives r = true := by
    simp only [survives]
    rw [List.all_eq_true]
    intro d hd
    rw [List.all_eq_true]
    intro q hq
    simp only [bne_iff_ne, ne_eq]
    exact h' d hd q hq
  rw [this] at h; simp at h

/-- `gcd(k, q) = 1` for all our `(k, q)` pairs. -/
lemma coprime_k_q (k : ℕ) (hk : k ∈ [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24])
    (q : ℕ) (hq : q ∈ sievePrimes) : Nat.Coprime k q := by
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- Each sieve prime divides `M`. -/
lemma sievePrime_dvd_M (q : ℕ) (hq : q ∈ sievePrimes) : q ∣ M := by
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- Each sieve prime is prime. -/
lemma sievePrime_prime (q : ℕ) (hq : q ∈ sievePrimes) : Nat.Prime q := by
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- `k * d = 2520` for each coefficient `d`. -/
lemma k_mul_d (d : ℕ) (hd : d ∈ coeffs) : (2520 / d) * d = 2520 := by
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The `k` values corresponding to coefficients. -/
lemma k_of_d_mem (d : ℕ) (hd : d ∈ coeffs) :
    2520 / d ∈ [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 24] := by
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Each coefficient `d` satisfies `d ≥ 1`. -/
lemma d_pos (d : ℕ) (hd : d ∈ coeffs) : d ≥ 1 := by
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-
`d * r ≡ 1 (mod q)` and `q ∣ M` and `N % M = r` imply `q ∣ (d * N - 1)`.
-/
lemma mod_transfer {d q r N : ℕ} (hdq : d * r % q = 1) (hqM : q ∣ M)
    (hNr : N % M = r) (hq_pos : q ≥ 2) (hdN_pos : d * N ≥ 1) :
    q ∣ (d * N - 1) := by
  -- Since $N \equiv r \pmod{M}$ and $q \mid M$, we have $N \equiv r \pmod{q}$.
  have hN_mod_q : N % q = r % q := by
    rw [ ← hNr, Nat.mod_mod_of_dvd _ hqM ];
  rw [ ← Nat.mod_add_div ( d * N ) q, Nat.mul_mod, hN_mod_q ];
  simp +decide [ ← Nat.mul_mod, hdq ]

/-
`d ∣ (n + 1)` implies `Nat.Coprime n d`.
-/
lemma coprime_of_congr_neg_one {n d : ℕ} (hd : d ≥ 1) (h : d ∣ (n + 1)) :
    Nat.Coprime n d := by
  exact Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_left h ( by norm_num ) )

/-! ## Per-pair verification -/

/-- Computational check: for `n ≤ 400`, no valid `n` has `τ(k*n) < k+3`. -/
def pairCheck (d k q : ℕ) : Bool :=
  (List.range 400 |>.map (· + 1)).all fun n =>
    !(n % q == 0 && Nat.gcd n d == 1 && (n + 1) % d == 0 &&
      (Nat.divisors (k * n)).card < k + 3)

/-- All 48 pairs pass the finite check. -/
lemma all_pairs_check :
    ([(2520,1), (1260,2), (840,3), (630,4), (504,5), (420,6),
      (315,8), (280,9), (252,10), (210,12), (140,18), (105,24)].all fun (d, k) =>
      [11, 13, 17, 19].all fun q => pairCheck d k q) = true := by native_decide

/-! ## Main per-pair lemma -/

/-- Helper: extract the pairCheck result for a specific (d,q) pair. -/
lemma pairCheck_holds (d : ℕ) (hd : d ∈ coeffs) (q : ℕ) (hq : q ∈ sievePrimes) :
    pairCheck d (2520 / d) q = true := by
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;> native_decide

/-
For n ≤ 400 with q ∣ n, gcd(n,d)=1, d ∣ (n+1): τ(k*n) ≥ k+3.
-/
lemma tau_ge_small {d q n : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    (hn_le : n ≤ 20000) (hn : n ≥ 1) (hqn : q ∣ n) (hcop : Nat.Coprime n d)
    (hdiv : d ∣ (n + 1)) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  revert n; revert d; revert q; native_decide;

/-
If `k*n` has a prime factor not dividing `k*q`, then `τ(k*n) ≥ 4*τ(k) ≥ k+3`.
-/
lemma tau_ge_of_new_prime {d q n : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    (hn : n ≥ 1) (hqn : q ∣ n)
    {p : ℕ} (hp : Nat.Prime p) (hpn : p ∣ n) (hpkq : ¬(p ∣ (2520 / d * q))) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  -- Since $p \mid n$ and $\gcd(p, kq) = 1$, we have $\tau(k*n) \geq 2 * \tau(kq)$.
  have h_tau_kn_ge_2_tau_kq : (Nat.divisors (2520 / d * n)).card ≥ 2 * (Nat.divisors (2520 / d * q)).card := by
    apply Nat.divisors_card_ge_two_mul;
    exacts [ mul_dvd_mul_left _ hqn, hp, dvd_mul_of_dvd_right hpn _, hp.coprime_iff_not_dvd.mpr hpkq, mul_ne_zero ( Nat.ne_of_gt ( Nat.div_pos ( show 2520 ≥ d by fin_cases hd <;> trivial ) ( by linarith [ d_pos d hd ] ) ) ) ( Nat.ne_of_gt hn ) ];
  -- Since $q$ is prime, $\tau(kq) = \tau(k) \cdot \tau(q) = \tau(k) \cdot 2$.
  have h_tau_kq : (Nat.divisors (2520 / d * q)).card = (Nat.divisors (2520 / d)).card * 2 := by
    have h_tau_kq : (Nat.divisors (2520 / d * q)).card = (Nat.divisors (2520 / d)).card * (Nat.divisors q).card := by
      apply Nat.divisors_card_mul_of_coprime;
      exact coprime_k_q _ ( k_of_d_mem _ hd ) _ hq;
    fin_cases hq <;> simp_all +decide;
  have := four_tau_k_ge ( 2520 / d ) ?_ <;> simp_all +decide;
  · grind;
  · fin_cases hd <;> trivial

/-- τ(k*q^3) ≥ k+3 for all our pairs, checked by native_decide. -/
lemma tau_kq3_ge {d q : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes) :
    ((2520 / d) * q ^ 3).divisors.card ≥ (2520 / d) + 3 := by
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;> native_decide

/-
When n is coprime to k (= 2520/d) and all primes of n divide kq,
    the multiplicativity of τ gives τ(kn) = τ(k)*τ(n), and the bounds
    4τ(k) ≥ k+3 force τ(n) ≤ 3, hence n ≤ q² ≤ 361.
-/
lemma tau_ge_large_coprime {d q n : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    (hn_gt : n > 20000) (hn : n ≥ 1) (hqn : q ∣ n) (hcop : Nat.Coprime n d)
    (hdiv : d ∣ (n + 1))
    (hkn_cop : Nat.Coprime (2520 / d) n) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  by_contra h_contra;
  -- Since τ(k*n) < k+3, we have τ(n) < (k+3)/τ(k) ≤ 4. So τ(n) ≤ 3.
  have h_tau_n_le_3 : n.divisors.card ≤ 3 := by
    have h_tau_n_lt : (2520 / d).divisors.card * n.divisors.card < 2520 / d + 3 := by
      rw [ ← Nat.divisors_card_mul_of_coprime hkn_cop ] ; aesop;
    have h_tau_k_ge : 4 * (2520 / d).divisors.card ≥ 2520 / d + 3 := by
      convert four_tau_k_ge ( 2520 / d ) ( k_of_d_mem d hd ) using 1;
    nlinarith only [ h_tau_n_lt, h_tau_k_ge ];
  -- Since τ(n) ≤ 3 and n > 20000, n must be a prime power.
  have h_prime_power : ∃ p k : ℕ, Nat.Prime p ∧ n = p^k := by
    have h_prime_power : ∀ p ∈ Nat.primeFactors n, ∀ q ∈ Nat.primeFactors n, p = q := by
      intros p hp q hq; contrapose! h_tau_n_le_3; simp_all +decide [ Nat.divisors_prime_pow ] ;
      -- Since $p$ and $q$ are distinct primes dividing $n$, $n$ has at least the divisors $1$, $p$, $q$, and $pq$.
      have h_divisors : n.divisors ⊇ {1, p, q, p * q} := by
        simp +decide [ Finset.insert_subset_iff ];
        exact ⟨ hp.2.2, ⟨ hp.2.1, hp.2.2 ⟩, ⟨ hq.2, hp.2.2 ⟩, Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp.1 hq.1 ) hp.2.1 hq.2, hp.2.2 ⟩;
      refine' lt_of_lt_of_le _ ( Finset.card_mono h_divisors );
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ hp.1.ne_zero, hq.1.ne_zero, hp.1.ne_one, hq.1.ne_one, h_tau_n_le_3 ];
      exact ⟨ Ne.symm hp.1.ne_one, Ne.symm hq.1.ne_one, Nat.ne_of_lt ( one_lt_mul'' hp.1.one_lt hq.1.one_lt ) ⟩;
    -- Since n has only one prime factor p, we can write n as p^k for some k.
    obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q → q ∣ n → q = p := by
      exact ⟨ Nat.minFac n, Nat.minFac_prime ( by linarith ), Nat.minFac_dvd n, fun q hq hqn => h_prime_power _ ( Nat.mem_primeFactors.mpr ⟨ hq, hqn, by linarith ⟩ ) _ ( Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd n, by linarith ⟩ ) ⟩;
    exact ⟨ p, Nat.primeFactorsList n |> List.count p, hp.1, by nth_rw 1 [ ← Nat.prod_primeFactorsList ( by linarith : n ≠ 0 ) ] ; rw [ List.prod_eq_pow_single p ] ; aesop ⟩;
  obtain ⟨ p, k, hp, rfl ⟩ := h_prime_power;
  -- Since $q \mid p^k$ and $q$ is prime, we have $q = p$.
  have hq_eq_p : q = p := by
    exact ( Nat.prime_dvd_prime_iff_eq ( show Nat.Prime q from by fin_cases hq <;> trivial ) hp ) |>.1 ( Nat.Prime.dvd_of_dvd_pow ( show Nat.Prime q from by fin_cases hq <;> trivial ) hqn );
  simp_all +decide [ Nat.divisors_prime_pow ];
  interval_cases k <;> simp_all +decide;
  · fin_cases hq <;> norm_num at *;
  · fin_cases hq <;> norm_num at *

/-- Helper: for the 6 "easy" d-values, primes(k) ⊆ primes(d), so Coprime n d
    implies Coprime (2520/d) n. Specifically, k ∣ d² for each such d. -/
lemma easy_k_dvd_d_sq (d : ℕ) (hd : d ∈ [210, 420, 630, 840, 1260, 2520]) :
    (2520 / d) ∣ d ^ 2 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Helper 1: extract the extra prime for hard d-values -/

/-- For each hard d-value, k = 2520/d has a unique prime factor not dividing d.
    This helper packages the existence + uniqueness. -/
lemma extract_extra_prime (d : ℕ)
    (hd : d ∈ [105, 140, 252, 280, 315, 504]) :
    ∃ p : ℕ, p.Prime ∧ p ∣ (2520/d) ∧ ¬ p ∣ d := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, by decide, by decide, by decide⟩  -- d=105, k=24, p=2
  · exact ⟨3, by decide, by decide, by decide⟩  -- d=140, k=18, p=3
  · exact ⟨5, by decide, by decide, by decide⟩  -- d=252, k=10, p=5
  · exact ⟨3, by decide, by decide, by decide⟩  -- d=280, k=9,  p=3
  · exact ⟨2, by decide, by decide, by decide⟩  -- d=315, k=8,  p=2
  · exact ⟨5, by decide, by decide, by decide⟩  -- d=504, k=5,  p=5

/-! ## Helper 2: extract p dividing n from ¬Coprime (2520/d) n -/

/-- From `¬Coprime (2520/d) n` and `Coprime n d`, extract a prime p dividing both
    n and (2520/d) but NOT dividing d. -/
lemma p_dvd_n_from_not_coprime {d n : ℕ}
    (hcop : Nat.Coprime n d)
    (hkn_not_cop : ¬Nat.Coprime (2520/d) n) :
    ∃ p, p.Prime ∧ p ∣ n ∧ ¬p ∣ d ∧ p ∣ (2520/d) := by
  -- gcd(2520/d, n) ≠ 1 from hkn_not_cop; extract a prime factor
  have h_gcd_ne : Nat.gcd (2520/d) n ≠ 1 := hkn_not_cop
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_gcd_ne
  have hp_k : p ∣ (2520/d) := dvd_trans hp_dvd (Nat.gcd_dvd_left _ _)
  have hp_n : p ∣ n := dvd_trans hp_dvd (Nat.gcd_dvd_right _ _)
  have hp_coprime_d : Nat.Coprime p d := Nat.Coprime.coprime_dvd_left hp_n hcop
  have hp_not_d : ¬ p ∣ d := (hp_prime.coprime_iff_not_dvd).mp hp_coprime_d
  exact ⟨p, hp_prime, hp_n, hp_not_d, hp_k⟩

/-! ## Helper 3: if n's prime factors ⊆ {p, q}, then n = p^a * q^b -/

/-- If all prime factors of n are in {p, q}, with p | n and q | n (p ≠ q),
    then n = p^a * q^b for some a ≥ 1, b ≥ 1. -/
lemma n_eq_pa_qb {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hn : n ≥ 1)
    (h_only : ∀ r, r.Prime → r ∣ n → r = p ∨ r = q) :
    ∃ a b : ℕ, n = p^a * q^b ∧ a ≥ 1 ∧ b ≥ 1 := by
  have n_ne_zero : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  refine ⟨n.factorization p, n.factorization q, ?_, ?_, ?_⟩
  · -- n = p^(f p) * q^(f q)
    -- Show support = {p, q}, then apply factorization_prod_pow_eq_self
    have hp_in : p ∈ n.factorization.support := by
      rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpn, n_ne_zero⟩
    have hq_in : q ∈ n.factorization.support := by
      rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hq, hqn, n_ne_zero⟩
    have h_supp_subset : n.factorization.support ⊆ {p, q} := by
      intro r hr
      rw [Nat.support_factorization] at hr
      obtain ⟨hr_prime, hr_dvd, _⟩ := Nat.mem_primeFactors.mp hr
      have := h_only r hr_prime hr_dvd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h_supp_eq : n.factorization.support = {p, q} := by
      apply Finset.Subset.antisymm h_supp_subset
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hp_in
      · exact hq_in
    have h_prod : ∏ r ∈ n.factorization.support, r ^ n.factorization r = n :=
      Nat.factorization_prod_pow_eq_self n_ne_zero
    rw [h_supp_eq] at h_prod
    rw [Finset.prod_insert (by simp [hpq])] at h_prod
    rw [Finset.prod_singleton] at h_prod
    exact h_prod.symm
  · -- a ≥ 1 since p ∣ n and p prime (via support membership)
    have hp_in : p ∈ n.factorization.support := by
      rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpn, n_ne_zero⟩
    exact Nat.one_le_iff_ne_zero.mpr ((Finsupp.mem_support_iff).mp hp_in)
  · -- b ≥ 1 since q ∣ n and q prime
    have hq_in : q ∈ n.factorization.support := by
      rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hq, hqn, n_ne_zero⟩
    exact Nat.one_le_iff_ne_zero.mpr ((Finsupp.mem_support_iff).mp hq_in)

/-! ## Helper 4: τ(k · p^a · q^b) ≥ k+3 bound for hard cases -/

/-- The extra prime for each hard d-value. -/
def extra_prime_of (d : ℕ) : ℕ :=
  if d = 105 then 2
  else if d = 140 then 3
  else if d = 252 then 5
  else if d = 280 then 3
  else if d = 315 then 2
  else if d = 504 then 5
  else 0

/-- The minimum value of `a` such that `p^a * q^b ≥ 20001` for `b ∈ {1, 2}`
    (using b = 2 since that's the tighter case). Python-verified to make
    τ(k · p^a_min · q^b) ≥ k+3 hold for all hard (d, q) and b ∈ {1, 2}. -/
def a_min_of (d q : ℕ) : ℕ :=
  if d = 105 ∨ d = 315 then
    if q = 11 then 8 else if q = 13 ∨ q = 17 then 7 else if q = 19 then 6 else 0
  else if d = 140 ∨ d = 280 then
    if q = 11 ∨ q = 13 then 5 else if q = 17 ∨ q = 19 then 4 else 0
  else if d = 252 ∨ d = 504 then
    if q = 11 then 4 else if q = 13 ∨ q = 17 ∨ q = 19 then 3 else 0
  else 0

/-- At the threshold a = a_min_of d q, with b ∈ {1, 2}: τ(k · p^a · q^b) ≥ k+3.
    Verified by native_decide over all 48 combinations. -/
lemma tau_kn_at_a_min (d q b : ℕ)
    (hd : d ∈ [105, 140, 252, 280, 315, 504])
    (hq : q ∈ sievePrimes)
    (hb : b = 1 ∨ b = 2) :
    ((2520/d) * ((extra_prime_of d) ^ (a_min_of d q) * q^b)).divisors.card
      ≥ (2520/d) + 3 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hb with rfl | rfl <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    native_decide

/-- Pre-computed bound: `p^(a_min - 1) · q^2 ≤ 20000` for each hard (d, q).
    This is the key fact that lets us derive `a ≥ a_min` from `n > 20000`. -/
lemma a_min_characterization (d q : ℕ)
    (hd : d ∈ [105, 140, 252, 280, 315, 504])
    (hq : q ∈ sievePrimes) :
    (extra_prime_of d) ^ (a_min_of d q - 1) * q^2 ≤ 20000 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;> native_decide

/-- Main τ-bound for n = p^a · q^b with a ≥ a_min and b ∈ {1, 2}. -/
lemma tau_kn_bound_pa_qb (d q a b : ℕ)
    (hd : d ∈ [105, 140, 252, 280, 315, 504])
    (hq : q ∈ sievePrimes)
    (ha : a ≥ a_min_of d q)
    (hb1 : b ≥ 1) (hb2 : b ≤ 2) :
    ((2520/d) * ((extra_prime_of d) ^ a * q^b)).divisors.card ≥ (2520/d) + 3 := by
  have hb_eq : b = 1 ∨ b = 2 := by omega
  have h_threshold := tau_kn_at_a_min d q b hd hq hb_eq
  -- Divisibility: p^(a_min) * q^b | p^a * q^b
  have hpow_dvd : (extra_prime_of d) ^ (a_min_of d q) ∣ (extra_prime_of d) ^ a :=
    pow_dvd_pow _ ha
  have hdvd : (extra_prime_of d) ^ (a_min_of d q) * q^b ∣
              (extra_prime_of d) ^ a * q^b :=
    mul_dvd_mul_right hpow_dvd _
  have hkdvd : (2520/d) * ((extra_prime_of d) ^ (a_min_of d q) * q^b) ∣
               (2520/d) * ((extra_prime_of d) ^ a * q^b) :=
    mul_dvd_mul_left _ hdvd
  -- Target is nonzero
  have hkn_ne : (2520/d) * ((extra_prime_of d) ^ a * q^b) ≠ 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl <;>
      (refine Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero ?_ ?_) <;>
       exact pow_ne_zero _ (by decide))
  have h_mono := Nat.divisors_card_le_of_dvd hkdvd hkn_ne
  omega

/-- When gcd(k, n) > 1, case split on d. For the 6 "easy" d ∈ {210, 420, 630, 840,
    1260, 2520}: primes(k) ⊆ primes(d), so Coprime n d implies Coprime k n,
    contradicting `hkn_not_cop` (vacuous cases). For the remaining 6 "hard" d
    ∈ {105, 140, 252, 280, 315, 504}: k has a prime p not in d, and we use the
    case analysis of the archived proof sketch. -/
lemma tau_ge_large_noncoprime {d q n : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    (hn_gt : n > 20000) (hn : n ≥ 1) (hqn : q ∣ n) (hcop : Nat.Coprime n d)
    (hdiv : d ∣ (n + 1))
    (hkn_not_cop : ¬Nat.Coprime (2520 / d) n) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  -- For easy d values, derive contradiction via k ∣ d²
  have easy_contradiction : ∀ (dd : ℕ), dd ∈ [210, 420, 630, 840, 1260, 2520] →
      d = dd → False := by
    intros dd hdd hd_eq
    apply hkn_not_cop
    -- Coprime n d ⟹ Coprime n (d²) ⟹ Coprime n (2520/d) via k ∣ d²
    have h1 : Nat.Coprime n (d ^ 2) := hcop.pow_right 2
    have hk_dvd : (2520 / d) ∣ d ^ 2 := by
      rw [hd_eq]; exact easy_k_dvd_d_sq dd hdd
    exact (Nat.Coprime.coprime_dvd_right hk_dvd h1).symm
  -- coeffs = [105, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520]
  simp only [coeffs, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  /- HARD CASES (TODO, ~6h of per-case Lean work). For each, the
     mathematical proof is laid out in the original comment
     block. Per-case extra prime p:
       d=105, k=24, p=2
       d=140, k=18, p=3
       d=252, k=10, p=5
       d=280, k=9,  p=3
       d=315, k=8,  p=2
       d=504, k=5,  p=5
     Structure (identical across cases, modulo p and q):
       1. From hkn_not_cop ∧ hcop, derive p ∣ n.
       2. Case split: either (a) n has a prime r ∉ {p, q}, in which
          case apply `tau_ge_of_new_prime` with r; OR (b) n = p^a · q^b
          for some a ≥ 1, b ≥ 1.
       3. For (b), split on b:
          (b.i)  b ≥ 3 → k·q³ ∣ k·n → τ ≥ τ(k·q³) ≥ k+3 by `tau_kq3_ge`
                 + `Nat.divisors_card_le_of_dvd`.
          (b.ii) b ∈ {1, 2} → n ≤ p^a · q² so p^a > 20000/q² > 55
                 → a ≥ a_min(p, q) → τ(k·n) ≥ k+3 by arithmetic
                 per-pair (24 (d, q) pairs × bounded (a, b) shapes).
  -/
  -- d = 105 (hard, pilot case)
  · -- k = 24 = 2³·3, extra prime p = 2
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    -- Show p = 2 (only prime of 24 not dividing 105)
    have hp_dvd_24 : p ∣ 24 := by
      have : (2520 / 105 : ℕ) = 24 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 2 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 24 := Nat.le_of_dvd (by decide) hp_dvd_24
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_24 (by decide))
        | (exfalso; exact hp_not_d (by decide))
    subst hp_eq
    -- Now: 2 ∣ n. Case split on "n has a prime outside {2, q}".
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 2 ∧ r ≠ q
    · -- n has a new prime r
      obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_2, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 105 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      -- Show r ∤ (2520/105 · q) = 24q. Primes of 24q = {2, 3, q}.
      -- r ≠ 2, r ≠ q. Show r ≠ 3 via: 3 ∣ 105, gcd(n, 105) = 1, r ∣ n.
      intro h_r_dvd_kq
      have h24 : (2520 / 105 : ℕ) = 24 := by decide
      rw [h24] at h_r_dvd_kq
      -- r prime dividing 24q, so r ∈ primes(24q) = {2, 3, q}
      -- Since r ≠ 2 and r ≠ q, must have r = 3
      have hr_ne_3 : r ≠ 3 := by
        intro h_eq
        have h3n : (3 : ℕ) ∣ n := h_eq ▸ hr_dvd_n
        have h3d : (3 : ℕ) ∣ 105 := by decide
        have := Nat.dvd_gcd h3n h3d
        rw [show Nat.gcd n 105 = 1 from hcop] at this
        exact absurd this (by decide : ¬ (3 : ℕ) ∣ 1)
      -- r divides 24q, r is prime. Use Nat.Prime.dvd_mul
      have : r ∣ 24 ∨ r ∣ q :=
        (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_24 | hr_q
      · -- r ∣ 24 = 2³·3, r prime → r ∈ {2, 3}
        have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 24 := Nat.le_of_dvd (by decide) hr_24
        interval_cases r
        all_goals first
          | exact hr_ne_2 rfl
          | exact hr_ne_3 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_24 (by decide))
      · -- r ∣ q, r prime, q prime → r = q
        have hq_prime := sievePrime_prime q hq
        have := (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q
        exact hr_ne_q this
    · -- No new prime: n = 2^a · q^b
      -- h_new : ¬ ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 2 ∧ r ≠ q
      have h_only : ∀ r, r.Prime → r ∣ n → r = 2 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h2_ne_q : (2 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h2_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      -- Case on b ≤ 2 vs b ≥ 3
      by_cases hb_le : b ≤ 2
      · -- b ∈ {1, 2}: derive a ≥ a_min from n > 20000 via a_min_characterization
        have ha_min : a ≥ a_min_of 105 q := by
          by_contra h_neg
          push_neg at h_neg
          -- h_neg : a < a_min_of 105 q
          -- So 2^a ≤ 2^(a_min - 1), and q^b ≤ q^2
          have h_pow_a : (2 : ℕ)^a ≤ 2^(a_min_of 105 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (2 : ℕ)^a * q^b ≤ 2^(a_min_of 105 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          -- By a_min_characterization: 2^(a_min - 1) * q^2 ≤ 20000
          have h_char : (extra_prime_of 105) ^ (a_min_of 105 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 105 q (by decide) hq
          have h_extra : extra_prime_of 105 = 2 := by decide
          rw [h_extra] at h_char
          -- So n = 2^a * q^b ≤ 2^(a_min - 1) * q^2 ≤ 20000
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        -- Apply Helper 4
        rw [hn_eq]
        have h_extra : extra_prime_of 105 = 2 := by decide
        rw [show (2 : ℕ) ^ a = (extra_prime_of 105) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 105 q a b (by decide) hq ha_min hb hb_le
      · -- b ≥ 3: q^3 ∣ n, use tau_kq3_ge + monotonicity
        push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 105) * q^3 ∣ (2520 / 105) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 105) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 105 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 140 (hard)
  · -- k = 18 = 2·3², extra prime p = 3
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    have hp_dvd_18 : p ∣ 18 := by
      have : (2520 / 140 : ℕ) = 18 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 3 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 18 := Nat.le_of_dvd (by decide) hp_dvd_18
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_18 (by decide))
        | (exfalso; exact hp_not_d (by decide))
    subst hp_eq
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 3 ∧ r ≠ q
    · obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_3, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 140 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      intro h_r_dvd_kq
      have h18 : (2520 / 140 : ℕ) = 18 := by decide
      rw [h18] at h_r_dvd_kq
      -- r ∣ 18q, r prime. Primes of 18q = {2, 3, q}. r ≠ 3, r ≠ q. Must be r = 2.
      -- But 2 ∣ 140 and gcd(n, 140) = 1 → 2 ∤ n, contradicting r ∣ n.
      have hr_ne_2 : r ≠ 2 := by
        intro h_eq
        have h2n : (2 : ℕ) ∣ n := h_eq ▸ hr_dvd_n
        have h2d : (2 : ℕ) ∣ 140 := by decide
        have := Nat.dvd_gcd h2n h2d
        rw [show Nat.gcd n 140 = 1 from hcop] at this
        exact absurd this (by decide : ¬ (2 : ℕ) ∣ 1)
      have : r ∣ 18 ∨ r ∣ q :=
        (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_18 | hr_q
      · have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 18 := Nat.le_of_dvd (by decide) hr_18
        interval_cases r
        all_goals first
          | exact hr_ne_2 rfl
          | exact hr_ne_3 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_18 (by decide))
      · have hq_prime := sievePrime_prime q hq
        exact hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q)
    · have h_only : ∀ r, r.Prime → r ∣ n → r = 3 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h3_ne_q : (3 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h3_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      by_cases hb_le : b ≤ 2
      · have ha_min : a ≥ a_min_of 140 q := by
          by_contra h_neg
          push_neg at h_neg
          have h_pow_a : (3 : ℕ)^a ≤ 3^(a_min_of 140 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (3 : ℕ)^a * q^b ≤ 3^(a_min_of 140 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          have h_char : (extra_prime_of 140) ^ (a_min_of 140 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 140 q (by decide) hq
          have h_extra : extra_prime_of 140 = 3 := by decide
          rw [h_extra] at h_char
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        rw [hn_eq]
        have h_extra : extra_prime_of 140 = 3 := by decide
        rw [show (3 : ℕ) ^ a = (extra_prime_of 140) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 140 q a b (by decide) hq ha_min hb hb_le
      · push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 140) * q^3 ∣ (2520 / 140) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 140) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 140 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 210 (easy)
  · exact (easy_contradiction 210 (by decide) rfl).elim
  -- d = 252 (hard)
  · -- k = 10 = 2·5, extra prime p = 5
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    have hp_dvd_10 : p ∣ 10 := by
      have : (2520 / 252 : ℕ) = 10 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 5 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 10 := Nat.le_of_dvd (by decide) hp_dvd_10
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_10 (by decide))
        | (exfalso; exact hp_not_d (by decide))
    subst hp_eq
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 5 ∧ r ≠ q
    · obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_5, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 252 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      intro h_r_dvd_kq
      have h10 : (2520 / 252 : ℕ) = 10 := by decide
      rw [h10] at h_r_dvd_kq
      -- r ∣ 10q, primes of 10q = {2, 5, q}. r ≠ 5, r ≠ q → r = 2.
      -- But 2 ∣ 252, gcd(n, 252) = 1 → 2 ∤ n, contradicting r ∣ n.
      have hr_ne_2 : r ≠ 2 := by
        intro h_eq
        have h2n : (2 : ℕ) ∣ n := h_eq ▸ hr_dvd_n
        have h2d : (2 : ℕ) ∣ 252 := by decide
        have := Nat.dvd_gcd h2n h2d
        rw [show Nat.gcd n 252 = 1 from hcop] at this
        exact absurd this (by decide : ¬ (2 : ℕ) ∣ 1)
      have : r ∣ 10 ∨ r ∣ q := (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_10 | hr_q
      · have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 10 := Nat.le_of_dvd (by decide) hr_10
        interval_cases r
        all_goals first
          | exact hr_ne_2 rfl
          | exact hr_ne_5 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_10 (by decide))
      · have hq_prime := sievePrime_prime q hq
        exact hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q)
    · have h_only : ∀ r, r.Prime → r ∣ n → r = 5 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h5_ne_q : (5 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h5_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      by_cases hb_le : b ≤ 2
      · have ha_min : a ≥ a_min_of 252 q := by
          by_contra h_neg
          push_neg at h_neg
          have h_pow_a : (5 : ℕ)^a ≤ 5^(a_min_of 252 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (5 : ℕ)^a * q^b ≤ 5^(a_min_of 252 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          have h_char : (extra_prime_of 252) ^ (a_min_of 252 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 252 q (by decide) hq
          have h_extra : extra_prime_of 252 = 5 := by decide
          rw [h_extra] at h_char
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        rw [hn_eq]
        have h_extra : extra_prime_of 252 = 5 := by decide
        rw [show (5 : ℕ) ^ a = (extra_prime_of 252) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 252 q a b (by decide) hq ha_min hb hb_le
      · push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 252) * q^3 ∣ (2520 / 252) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 252) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 252 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 280 (hard)
  · -- k = 9 = 3², extra prime p = 3 (only prime in k)
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    have hp_dvd_9 : p ∣ 9 := by
      have : (2520 / 280 : ℕ) = 9 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 3 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 9 := Nat.le_of_dvd (by decide) hp_dvd_9
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_9 (by decide))
    subst hp_eq
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 3 ∧ r ≠ q
    · obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_3, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 280 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      intro h_r_dvd_kq
      have h9 : (2520 / 280 : ℕ) = 9 := by decide
      rw [h9] at h_r_dvd_kq
      -- r ∣ 9q, primes of 9q = {3, q}. r ≠ 3, r ≠ q → impossible.
      have : r ∣ 9 ∨ r ∣ q := (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_9 | hr_q
      · have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 9 := Nat.le_of_dvd (by decide) hr_9
        interval_cases r
        all_goals first
          | exact hr_ne_3 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_9 (by decide))
      · have hq_prime := sievePrime_prime q hq
        exact hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q)
    · have h_only : ∀ r, r.Prime → r ∣ n → r = 3 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h3_ne_q : (3 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h3_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      by_cases hb_le : b ≤ 2
      · have ha_min : a ≥ a_min_of 280 q := by
          by_contra h_neg
          push_neg at h_neg
          have h_pow_a : (3 : ℕ)^a ≤ 3^(a_min_of 280 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (3 : ℕ)^a * q^b ≤ 3^(a_min_of 280 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          have h_char : (extra_prime_of 280) ^ (a_min_of 280 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 280 q (by decide) hq
          have h_extra : extra_prime_of 280 = 3 := by decide
          rw [h_extra] at h_char
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        rw [hn_eq]
        have h_extra : extra_prime_of 280 = 3 := by decide
        rw [show (3 : ℕ) ^ a = (extra_prime_of 280) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 280 q a b (by decide) hq ha_min hb hb_le
      · push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 280) * q^3 ∣ (2520 / 280) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 280) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 280 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 315 (hard)
  · -- k = 8 = 2³, extra prime p = 2 (only prime in k)
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    have hp_dvd_8 : p ∣ 8 := by
      have : (2520 / 315 : ℕ) = 8 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 2 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 8 := Nat.le_of_dvd (by decide) hp_dvd_8
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_8 (by decide))
    subst hp_eq
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 2 ∧ r ≠ q
    · obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_2, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 315 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      intro h_r_dvd_kq
      have h8 : (2520 / 315 : ℕ) = 8 := by decide
      rw [h8] at h_r_dvd_kq
      have : r ∣ 8 ∨ r ∣ q := (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_8 | hr_q
      · have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 8 := Nat.le_of_dvd (by decide) hr_8
        interval_cases r
        all_goals first
          | exact hr_ne_2 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_8 (by decide))
      · have hq_prime := sievePrime_prime q hq
        exact hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q)
    · have h_only : ∀ r, r.Prime → r ∣ n → r = 2 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h2_ne_q : (2 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h2_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      by_cases hb_le : b ≤ 2
      · have ha_min : a ≥ a_min_of 315 q := by
          by_contra h_neg
          push_neg at h_neg
          have h_pow_a : (2 : ℕ)^a ≤ 2^(a_min_of 315 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (2 : ℕ)^a * q^b ≤ 2^(a_min_of 315 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          have h_char : (extra_prime_of 315) ^ (a_min_of 315 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 315 q (by decide) hq
          have h_extra : extra_prime_of 315 = 2 := by decide
          rw [h_extra] at h_char
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        rw [hn_eq]
        have h_extra : extra_prime_of 315 = 2 := by decide
        rw [show (2 : ℕ) ^ a = (extra_prime_of 315) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 315 q a b (by decide) hq ha_min hb hb_le
      · push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 315) * q^3 ∣ (2520 / 315) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 315) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 315 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 420 (easy)
  · exact (easy_contradiction 420 (by decide) rfl).elim
  -- d = 504 (hard)
  · -- k = 5, extra prime p = 5 (only prime in k)
    obtain ⟨p, hp_prime, hp_dvd_n, hp_not_d, hp_dvd_k⟩ :=
      p_dvd_n_from_not_coprime hcop hkn_not_cop
    have hp_dvd_5 : p ∣ 5 := by
      have : (2520 / 504 : ℕ) = 5 := by decide
      rw [this] at hp_dvd_k; exact hp_dvd_k
    have hp_eq : p = 5 := by
      have hp_ge : p ≥ 2 := hp_prime.two_le
      have hp_le : p ≤ 5 := Nat.le_of_dvd (by decide) hp_dvd_5
      interval_cases p
      all_goals first
        | rfl
        | (exfalso; exact absurd hp_prime (by decide))
        | (exfalso; exact absurd hp_dvd_5 (by decide))
    subst hp_eq
    by_cases h_new : ∃ r, r.Prime ∧ r ∣ n ∧ r ≠ 5 ∧ r ≠ q
    · obtain ⟨r, hr_prime, hr_dvd_n, hr_ne_5, hr_ne_q⟩ := h_new
      apply tau_ge_of_new_prime (by decide : 504 ∈ coeffs) hq hn hqn
        hr_prime hr_dvd_n
      intro h_r_dvd_kq
      have h5 : (2520 / 504 : ℕ) = 5 := by decide
      rw [h5] at h_r_dvd_kq
      have : r ∣ 5 ∨ r ∣ q := (Nat.Prime.dvd_mul hr_prime).mp h_r_dvd_kq
      rcases this with hr_5 | hr_q
      · have hr_ge : r ≥ 2 := hr_prime.two_le
        have hr_le : r ≤ 5 := Nat.le_of_dvd (by decide) hr_5
        interval_cases r
        all_goals first
          | exact hr_ne_5 rfl
          | (exfalso; exact absurd hr_prime (by decide))
          | (exfalso; exact absurd hr_5 (by decide))
      · have hq_prime := sievePrime_prime q hq
        exact hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp hr_q)
    · have h_only : ∀ r, r.Prime → r ∣ n → r = 5 ∨ r = q := by
        intro r hr_prime hr_dvd
        by_contra h_ne
        push_neg at h_ne
        exact h_new ⟨r, hr_prime, hr_dvd, h_ne.1, h_ne.2⟩
      have h5_ne_q : (5 : ℕ) ≠ q := by
        simp only [sievePrimes, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, hn_eq, ha, hb⟩ := n_eq_pa_qb hp_prime
        (sievePrime_prime q hq) h5_ne_q hp_dvd_n hqn hn h_only
      have hq_pos : 1 ≤ q := (sievePrime_prime q hq).one_le
      by_cases hb_le : b ≤ 2
      · have ha_min : a ≥ a_min_of 504 q := by
          by_contra h_neg
          push_neg at h_neg
          have h_pow_a : (5 : ℕ)^a ≤ 5^(a_min_of 504 q - 1) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt h_neg)
          have h_pow_b : q^b ≤ q^2 := Nat.pow_le_pow_right hq_pos hb_le
          have h_mul : (5 : ℕ)^a * q^b ≤ 5^(a_min_of 504 q - 1) * q^2 :=
            Nat.mul_le_mul h_pow_a h_pow_b
          have h_char : (extra_prime_of 504) ^ (a_min_of 504 q - 1) * q^2 ≤ 20000 :=
            a_min_characterization 504 q (by decide) hq
          have h_extra : extra_prime_of 504 = 5 := by decide
          rw [h_extra] at h_char
          have : n ≤ 20000 := hn_eq ▸ (Nat.le_trans h_mul h_char)
          omega
        rw [hn_eq]
        have h_extra : extra_prime_of 504 = 5 := by decide
        rw [show (5 : ℕ) ^ a = (extra_prime_of 504) ^ a from by rw [h_extra]]
        exact tau_kn_bound_pa_qb 504 q a b (by decide) hq ha_min hb hb_le
      · push_neg at hb_le
        have hb_gt : 3 ≤ b := hb_le
        have hq3_dvd_n : q^3 ∣ n := by
          rw [hn_eq]
          exact dvd_mul_of_dvd_right (pow_dvd_pow q hb_gt) _
        have hkq3_dvd : (2520 / 504) * q^3 ∣ (2520 / 504) * n :=
          mul_dvd_mul_left _ hq3_dvd_n
        have hkn_ne : (2520 / 504) * n ≠ 0 := by
          have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
          positivity
        have h1 := tau_kq3_ge (by decide : 504 ∈ coeffs) hq
        have h2 := Nat.divisors_card_le_of_dvd hkq3_dvd hkn_ne
        omega
  -- d = 630 (easy)
  · exact (easy_contradiction 630 (by decide) rfl).elim
  -- d = 840 (easy)
  · exact (easy_contradiction 840 (by decide) rfl).elim
  -- d = 1260 (easy)
  · exact (easy_contradiction 1260 (by decide) rfl).elim
  -- d = 2520 (easy)
  · exact (easy_contradiction 2520 (by decide) rfl).elim

/-- For n > 20000 with q ∣ n, gcd(n,d)=1, d ∣ (n+1): τ(k*n) ≥ k+3. -/
lemma tau_ge_large {d q n : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    (hn_gt : n > 20000) (hn : n ≥ 1) (hqn : q ∣ n) (hcop : Nat.Coprime n d)
    (hdiv : d ∣ (n + 1)) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  by_cases hkn : Nat.Coprime (2520 / d) n
  · exact tau_ge_large_coprime hd hq hn_gt hn hqn hcop hdiv hkn
  · exact tau_ge_large_noncoprime hd hq hn_gt hn hqn hcop hdiv hkn

/-- For each (d,q) pair, for all n ≥ 1 with q ∣ n, gcd(n,d) = 1, d ∣ (n+1):
    τ(k * n) ≥ k + 3. -/
lemma tau_ge_for_pair {d q : ℕ} (hd : d ∈ coeffs) (hq : q ∈ sievePrimes)
    {n : ℕ} (hn : n ≥ 1) (hqn : q ∣ n) (hcop : Nat.Coprime n d)
    (hdiv : d ∣ (n + 1)) :
    ((2520 / d) * n).divisors.card ≥ (2520 / d) + 3 := by
  by_cases h : n ≤ 20000
  · exact tau_ge_small hd hq h hn hqn hcop hdiv
  · exact tau_ge_large hd hq (by omega) hn hqn hcop hdiv

/-! ## Main theorem -/

/-
Bridge 2: If `IsErdos647(2520 * N)` and `84 < 2520 * N`, then
    `survives (N % M) = true`.
-/
theorem bridge_isErdos647_to_sieve (N : ℕ) (hN : 84 < 2520 * N)
    (herd : IsErdos647 (2520 * N)) :
    survives (N % M) = true := by
  simp +decide only [survives] at *;
  have hs : ∀ d ∈ coeffs, ∀ q ∈ sievePrimes, d * (N % M) % q ≠ 1 := by
    intros d hd q hq hdq
    set k := 2520 / d
    have hk : k * d = 2520 := k_mul_d d hd
    have hq_div : q ∣ (d * N - 1) := mod_transfer hdq (sievePrime_dvd_M q hq) (by
    rfl) (by
    exact Nat.Prime.two_le ( sievePrime_prime q hq )) (by
    exact Nat.mul_pos ( Nat.pos_of_ne_zero ( by rintro rfl; contradiction ) ) ( Nat.pos_of_ne_zero ( by rintro rfl; contradiction ) ))
    have h_coprime : Nat.Coprime (d * N - 1) d := by
      cases N <;> cases d <;> simp_all +decide [ Nat.succ_eq_add_one, mul_add ]
    have h_tau : (Nat.divisors (k * (d * N - 1))).card ≥ k + 3 := by
      apply tau_ge_for_pair hd hq (by
      rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
      · fin_cases hd <;> trivial;
      · exact Nat.le_sub_one_of_lt ( by nlinarith only [ show d > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ] )) hq_div h_coprime (by
      rw [ Nat.sub_add_cancel ( by nlinarith [ show N > 0 from by linarith ] ) ] ; norm_num)
    have h_contra : (Nat.divisors (2520 * N - k)).card ≤ k + 2 := by
      have h_contra : (2520 * N - k) + (Nat.divisors (2520 * N - k)).card ≤ 2520 * N + 2 := by
        apply herd;
        · exact Nat.le_sub_of_add_le ( by nlinarith [ show k ≤ 24 by fin_cases hd <;> trivial ] );
        · exact Nat.sub_lt ( by linarith ) ( Nat.div_pos ( by linarith [ show d ≤ 2520 from by fin_cases hd <;> trivial ] ) ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
      omega
    have h_final : (Nat.divisors (k * (d * N - 1))).card ≤ k + 2 := by
      convert h_contra using 2 ; rw [ Nat.mul_sub_left_distrib ] ; ring;
      rw [ hk, mul_comm ]
    linarith;
  aesop
end Bridge2
