# Conditional Finite-Window Theorem

This note documents the separate positive-direction theorem in
[`lean/Erdos647ConditionalFiniteWindow.lean`](../lean/Erdos647ConditionalFiniteWindow.lean).

It is intentionally **not** part of the Stage-1 no-solution frontier.

## The theorem

For `K ≥ 1`, define:

* `prefixLcm K = lcm(1, ..., K)`;
* `primeCofactor K t k = (prefixLcm K / k) * t - 1`.

The Lean module defines:

* `PrimeCofactorHyp K t`
* `WindowGood K n`

and proves the deterministic theorem

* `windowGood_of_primeCofactors`

which says:

if every cofactor `primeCofactor K t k` is prime and strictly larger
than `k`, then the finite window

`(Nat.divisors (prefixLcm K * t - k)).card ≤ k + 2`

holds for every `1 ≤ k ≤ K`, provided the small-factor inequality
`2 * τ(k) ≤ k + 2` is supplied.

The file also provides concrete corollaries:

* `windowGood20_of_primeCofactors`
* `windowGood80_of_primeCofactors`

using a finite native check of `2 * τ(k) ≤ k + 2` up to `k = 80`.

## Full-value proof shape

This theorem does **not** use peeled-cofactor reasoning.

The key identity is the full-value factorization

`prefixLcm K * t - k = k * primeCofactor K t k`.

Under the hypotheses that `primeCofactor K t k` is prime and larger
than `k`, Lean proves the factors are coprime, so

`τ(prefixLcm K * t - k) = 2 * τ(k)`.

That is the whole kernel.

## K = 20 remark

The file proves:

* `prefixLcm20_eq : prefixLcm 20 = 232792560`
* `prefixLcm20_div_2520_eq : prefixLcm 20 / 2520 = 92378`
* `residue_zero_mod_M_for_K20`

Since `92378 = 2 * 46189`, the `K = 20` construction lies in residue
`0 mod 46189`.

This is only a location fact for the conditional construction. It does
**not** close the `r = 0` residue in the Stage-1 frontier.

## Scope

This theorem is a separate conditional existence-direction artifact.

It does **not**:

* close any of the `41` open Stage-1 residues;
* replace the Stage-1 open-set axiom;
* prove any Schinzel/Dickson hypothesis inside Lean.

What it gives the repo is a clean, full-value deterministic theorem
that can be paired with an external prime-tuples hypothesis without
reopening the unsound Bridge-3 lane.
