import Mathlib

open Nat Finset Finsupp

set_option maxHeartbeats 800000

/-
If n.primeFactors has ≥ 3 elements, then n.divisors.card ≥ 8.
-/
lemma divisors_card_ge_of_primeFactors_card_ge_three (n : ℕ) (hn : n ≠ 0)
    (h3 : 3 ≤ n.primeFactors.card) :
    8 ≤ n.divisors.card := by
  -- Use Nat.card_divisors to rewrite n.divisors.card as ∏ x ∈ n.primeFactors, (n.factorization x + 1).
  have h_card : (Nat.divisors n).card = ∏ x ∈ n.primeFactors, (n.factorization x + 1) := by
    exact card_divisors hn;
  exact h_card ▸ le_trans ( by norm_num; linarith [ Nat.pow_le_pow_right ( by norm_num : 1 ≤ 2 ) h3 ] ) ( Finset.prod_le_prod' fun p hp => Nat.succ_le_succ ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) )

/-
For n = p^e with p prime and e ≥ 1, divisors.card = e + 1.
-/
lemma card_divisors_prime_pow (p e : ℕ) (hp : p.Prime) (_he : 1 ≤ e) :
    (p ^ e).divisors.card = e + 1 := by
  simp +arith +decide [ Nat.divisors_prime_pow hp ]

/-
If n > 0 and primeFactors = {p}, then n = p ^ (n.factorization p).
-/
lemma eq_prime_pow_of_primeFactors_singleton (n p : ℕ) (hn : n ≠ 0)
    (hpf : n.primeFactors = {p}) :
    n = p ^ (n.factorization p) := by
  conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self hn ];
  rw [ Finsupp.prod ] ; aesop

/-
If n > 0 and primeFactors = {p, q} with p ≠ q, then
    n = p ^ (n.factorization p) * q ^ (n.factorization q).
-/
lemma eq_prime_pow_mul_of_primeFactors_pair (n p q : ℕ) (hn : n ≠ 0)
    (hpq : p ≠ q) (hpf : n.primeFactors = {p, q}) :
    n = p ^ (n.factorization p) * q ^ (n.factorization q) := by
  conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self hn ];
  simp +decide [ *, Finsupp.prod ]

/-
If a ≥ 1 and b ≥ 1 and (a+1)*(b+1) ≤ 4, then a = 1 ∧ b = 1.
-/
lemma both_one_of_succ_mul_succ_le_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : (a + 1) * (b + 1) ≤ 4) : a = 1 ∧ b = 1 := by
  constructor <;> nlinarith

theorem shape_decomposition (n : ℕ) (hn : 0 < n)
    (h : n.divisors.card ≤ 4) :
    n = 1
    ∨ (∃ p : ℕ, p.Prime ∧ n = p)
    ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ 2)
    ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ 3)
    ∨ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q) := by
  revert h;
  -- We split into cases based on the cardinality of `n.primeFactors`.
  by_cases h_card : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 ∨ n.primeFactors.card ≥ 3;
  · rcases h_card with h | h | h | h;
    · aesop;
    · -- If n has exactly one prime factor p, then n = p^e for some prime p and integer e.
      obtain ⟨p, e, hp, he⟩ : ∃ p e : ℕ, Nat.Prime p ∧ n = p^e := by
        rw [ Finset.card_eq_one ] at h;
        obtain ⟨ p, hp ⟩ := h; exact ⟨ p, n.factorization p, Nat.prime_of_mem_primeFactors <| hp.symm ▸ Finset.mem_singleton_self _, by nth_rw 1 [ ← Nat.prod_factorization_pow_eq_self hn.ne' ] ; rw [ Finsupp.prod ] ; aesop ⟩ ;
      rcases e with ( _ | _ | _ | _ | e ) <;> simp_all +decide [ Nat.divisors_prime_pow ];
    · -- Let's write n as p^a * q^b where p and q are distinct primes and a, b ≥ 1.
      obtain ⟨p, q, a, b, hp, hq, ha, hb, hn_eq⟩ : ∃ p q a b : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ a ≥ 1 ∧ b ≥ 1 ∧ n = p^a * q^b := by
        rw [ Finset.card_eq_two ] at h;
        obtain ⟨ p, q, hpq, h ⟩ := h; exact ⟨ p, q, n.factorization p, n.factorization q, Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_self _ _ ), Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), hpq, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.prod_factorization_pow_eq_self hn.ne' ] ; rw [ Finsupp.prod ] ; aesop ⟩ ;
      -- By Nat.card_divisors, divisors.card = (a+1)*(b+1) ≤ 4.
      have h_divisors_card : (Nat.divisors n).card = (a + 1) * (b + 1) := by
        have h_divisors_card : Nat.divisors n = Finset.image (fun d => p^d.1 * q^d.2) (Finset.product (Finset.range (a + 1)) (Finset.range (b + 1))) := by
          rw [ hn_eq.2, Nat.divisors_mul, Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hq ];
          ext; rw [ Finset.mem_mul ] ; aesop;
        erw [ h_divisors_card, Finset.card_image_of_injective, Finset.card_product ];
        · norm_num;
        · exact fun x y hxy => by have := congr_arg ( fun x : ℕ => x.factorization p ) hxy; have := congr_arg ( fun x : ℕ => x.factorization q ) hxy; norm_num [ hp.ne_zero, hq.ne_zero ] at *; aesop;
      rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +arith +decide;
      · cases lt_or_gt_of_ne ha <;> [ exact Or.inr ( Or.inr <| Or.inr <| Or.inr ⟨ p, hp, q, hq, ‹_›, rfl ⟩ ) ; exact Or.inr ( Or.inr <| Or.inr <| Or.inr ⟨ q, hq, p, hp, ‹_›, by ring ⟩ ) ];
      · grind +splitImp;
    · exact fun h' => absurd h' ( by linarith [ divisors_card_ge_of_primeFactors_card_ge_three n hn.ne' h ] );
  · omega

/-
Extension: τ(n) ≤ 5 ⇒ n ∈ {1, p, p², p³, p⁴, pq}.

Proof structure mirrors `shape_decomposition`:
  - primeFactors.card = 0 → n = 1
  - primeFactors.card = 1 → n = p^e with e + 1 ≤ 5, e ∈ {1,2,3,4}
  - primeFactors.card = 2 → n = p^a · q^b with (a+1)(b+1) ≤ 5; since 5
    is prime, (a+1)(b+1) = 5 forces a = 0 or b = 0 (both excluded by
    a,b ≥ 1), so (a+1)(b+1) = 4 forcing a = b = 1, giving pq
  - primeFactors.card ≥ 3 → τ ≥ 8 > 5, contradiction
-/
theorem shape_decomposition_le_5 (n : ℕ) (hn : 0 < n)
    (h : n.divisors.card ≤ 5) :
    n = 1
    ∨ (∃ p : ℕ, p.Prime ∧ n = p)
    ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ 2)
    ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ 3)
    ∨ (∃ p : ℕ, p.Prime ∧ n = p ^ 4)
    ∨ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q) := by
  revert h;
  by_cases h_card : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 ∨ n.primeFactors.card ≥ 3;
  · rcases h_card with h | h | h | h;
    · aesop;
    · -- card = 1: n = p^e, e ∈ {1,2,3,4}
      obtain ⟨p, e, hp, he⟩ : ∃ p e : ℕ, Nat.Prime p ∧ n = p^e := by
        rw [ Finset.card_eq_one ] at h;
        obtain ⟨ p, hp ⟩ := h; exact ⟨ p, n.factorization p, Nat.prime_of_mem_primeFactors <| hp.symm ▸ Finset.mem_singleton_self _, by nth_rw 1 [ ← Nat.prod_factorization_pow_eq_self hn.ne' ] ; rw [ Finsupp.prod ] ; aesop ⟩ ;
      rcases e with ( _ | _ | _ | _ | _ | e ) <;> simp_all +decide [ Nat.divisors_prime_pow ];
    · -- card = 2: n = p^a · q^b, must have a = b = 1
      obtain ⟨p, q, a, b, hp, hq, ha, hb, hn_eq⟩ : ∃ p q a b : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ a ≥ 1 ∧ b ≥ 1 ∧ n = p^a * q^b := by
        rw [ Finset.card_eq_two ] at h;
        obtain ⟨ p, q, hpq, h ⟩ := h; exact ⟨ p, q, n.factorization p, n.factorization q, Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_self _ _ ), Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ), hpq, Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ), by nth_rw 1 [ ← Nat.prod_factorization_pow_eq_self hn.ne' ] ; rw [ Finsupp.prod ] ; aesop ⟩ ;
      have h_divisors_card : (Nat.divisors n).card = (a + 1) * (b + 1) := by
        have h_divisors_card : Nat.divisors n = Finset.image (fun d => p^d.1 * q^d.2) (Finset.product (Finset.range (a + 1)) (Finset.range (b + 1))) := by
          rw [ hn_eq.2, Nat.divisors_mul, Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hq ];
          ext; rw [ Finset.mem_mul ] ; aesop;
        erw [ h_divisors_card, Finset.card_image_of_injective, Finset.card_product ];
        · norm_num;
        · exact fun x y hxy => by have := congr_arg ( fun x : ℕ => x.factorization p ) hxy; have := congr_arg ( fun x : ℕ => x.factorization q ) hxy; norm_num [ hp.ne_zero, hq.ne_zero ] at *; aesop;
      rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +arith +decide;
      · cases lt_or_gt_of_ne ha <;> [ exact Or.inr ( Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨ p, hp, q, hq, ‹_›, rfl ⟩ ) ; exact Or.inr ( Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨ q, hq, p, hp, ‹_›, by ring ⟩ ) ];
      · grind +splitImp;
    · exact fun h' => absurd h' ( by linarith [ divisors_card_ge_of_primeFactors_card_ge_three n hn.ne' h ] );
  · omega