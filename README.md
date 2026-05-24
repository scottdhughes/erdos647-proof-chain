# Erdős #647 Proof Chain

**Maintainer:** Scott D. Hughes

This repository contains the curated Lean 4 formalization and
paper package for
Erdős Problem #647:

> Does there exist `n > 24` such that
> `max_{1 ≤ m < n} (m + τ(m)) ≤ n + 2`?

Equivalently:

`τ(n - k) ≤ k + 2` for every `1 ≤ k < n`.

## Current status

| Item | Status | Location |
|------|--------|----------|
| Sieve reduction to `96` survivors | theorem-grade | [`lean/Erdos647SieveCertificate.lean`](lean/Erdos647SieveCertificate.lean) |
| Stage-1 closed set `closedResiduesStage1` | theorem-grade, `55` residues | [`lean/Erdos647ResiduePartitionStage1.lean`](lean/Erdos647ResiduePartitionStage1.lean) |
| Stage-1 open set `openResiduesStage1` | explicit complement, `41` residues | [`lean/Erdos647ResiduePartitionStage1.lean`](lean/Erdos647ResiduePartitionStage1.lean) |
| Conditional reduction theorem | theorem-grade | [`lean/Erdos647ReductionChain.lean`](lean/Erdos647ReductionChain.lean) |
| Stage-1 axiom wrapper | `1` intentional axiom | [`lean/Erdos647Stage1Axiom.lean`](lean/Erdos647Stage1Axiom.lean) |
| Bridge 3 | retired from proof path | [`lean/Bridge3.lean`](lean/Bridge3.lean) |
| Conditional finite-window theorem | theorem-grade, existence-direction | [`lean/Erdos647ConditionalFiniteWindow.lean`](lean/Erdos647ConditionalFiniteWindow.lean) |

The active formal boundary is:

* `55` theorem-grade closed residues;
* `41` open residues;
* `0` source-level sorries in `lean/`;
* `1` intentional Stage-1 axiom:
  `Erdos647Stage1Axiom.openResiduesStage1_no_solution`.

For the exact axiom trail, see [AXIOM_AUDIT.md](AXIOM_AUDIT.md).

## What the repo proves

For `n > 84`, the active proof path reduces the problem to numbers of
the form `n = 2520 * N`, then to the `96` theorem-grade sieve survivors
modulo `46189`, then closes `55` of those residues by full-value
arguments:

* `42` single-overlap closures;
* `13` direct full-value closures.

The proof-critical open set is defined by complement inside the
survivors:

* `closedResiduesStage1.card = 55`
* `openResiduesStage1.card = 41`
* `closedResiduesStage1 ∪ openResiduesStage1 = survivingResidues96`

The main theorem surface is split cleanly:

* theorem-grade conditional reduction:
  `Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1`
* single-axiom wrapper:
  `Erdos647Stage1Axiom.erdos647_with_stage1_axiom`

This split is deliberate. The conditional theorem is the proof-critical
result; the wrapper only isolates the current open frontier.

## What the repo does not prove

The repository does **not** currently prove an unconditional full
solution to #647.

The remaining open mathematical content is exactly the Stage-1 axiom
over the `41` open residues. The bounded positive-footprint search lanes
that were explored against this frontier are now retired. The stop
reason is recorded in [docs/stage1_boundary.md](docs/stage1_boundary.md).

That memo closes a family of search strategies. It does **not** prove
that the `41` residues are impossible, and it does **not** rule out a
future theorem with a materially different proof shape.

## Separate conditional theorem

The repository also contains a separate positive-direction theorem:

* [`lean/Erdos647ConditionalFiniteWindow.lean`](lean/Erdos647ConditionalFiniteWindow.lean)

This theorem shows that if the linear cofactors

`((lcm(1, ..., K) / k) * t - 1)`

are prime and larger than `k`, then the finite window

`τ(lcm(1, ..., K) * t - k) ≤ k + 2`

holds for all `1 ≤ k ≤ K`.

This is **not** part of the Stage-1 no-solution frontier. It does not
close any of the `41` open residues, and it does not replace the
Stage-1 axiom wrapper. See
[docs/conditional_finite_window.md](docs/conditional_finite_window.md).

## Repository layout

```text
lean/             Lean 4 formalizations and proof-chain support modules
docs/             theorem map, frontier notes, and related memos
scripts/          reproducible computations and audits for this package
data/             compact machine-readable artifacts cited by this package
paper/            main preprint source and rendered PDF
```

Useful entry points:

* [AXIOM_AUDIT.md](AXIOM_AUDIT.md)
* [docs/stage1_boundary.md](docs/stage1_boundary.md)
* [docs/conditional_finite_window.md](docs/conditional_finite_window.md)
* [docs/relation_to_formal_conjectures.md](docs/relation_to_formal_conjectures.md)
* [docs/theorem_map.md](docs/theorem_map.md)

## Quick start

```bash
cd lean
lake exe cache get
lake build

# Build the separate conditional finite-window theorem directly.
lake build Erdos647ConditionalFiniteWindow

# Audit theorem dependencies.
bash ../scripts/axiom_audit.sh
```

## References

* T. F. Bloom, [Erdős Problem #647](https://www.erdosproblems.com/647)
* OEIS [A087280](https://oeis.org/A087280)
* DeepMind,
  [FormalConjectures/ErdosProblems/647.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/647.lean)
