# Erdős Problem 647

**Scott D. Hughes**

Erdős problem 647 asks whether there is an integer `n > 24` with
`max_{m < n} (m + τ(m)) ≤ n + 2`, equivalently `τ(n − k) ≤ k + 2` for all
`1 ≤ k < n`. The value `n = 24` works, and Erdős expected no larger example to exist.

This repository contains a reduction of the candidate set, the modular part of which
is verified in Lean 4, together with the unconditional density bounds it yields and
an analysis of why those bounds stop short of finiteness. The short paper
[`paper/main.pdf`](paper/main.pdf) is the entry point; the Lean development is in
[`lean/`](lean/), with the formal boundary recorded in
[AXIOM_AUDIT.md](AXIOM_AUDIT.md). The results are density-zero, not a resolution of
the problem.

The strongest density bound, `|C(x)| ≤ x·exp(−(log log x)^{2−o(1)})`, and the
elementary `|C(x)| ≪ x/(log x)^7` bound, are proved in companion manuscripts
(submitted; see the paper's references). The Lean development here formalizes the
modular (Stage-1) reduction — the constraint `2520 | n` and the 41 residue classes
mod 46189; the prime-chain reduction and the density bounds are established in the
paper and its companion manuscripts, not in Lean.

## Current status

This is the package referenced in the public #647 forum thread. The
current result is **not** an unconditional solution; it is a
Lean-verified structural reduction with the remaining gap isolated
explicitly.

| Item | Status | Location |
|------|--------|----------|
| Sieve reduction to `96` survivors | theorem-grade | [`lean/Erdos647SieveCertificate.lean`](lean/Erdos647SieveCertificate.lean) |
| Stage-1 closed set `closedResiduesStage1` | theorem-grade, `55` residues | [`lean/Erdos647ResiduePartitionStage1.lean`](lean/Erdos647ResiduePartitionStage1.lean) |
| Stage-1 open set `openResiduesStage1` | explicit complement, `41` residues | [`lean/Erdos647ResiduePartitionStage1.lean`](lean/Erdos647ResiduePartitionStage1.lean) |
| Conditional reduction theorem | theorem-grade | [`lean/Erdos647ReductionChain.lean`](lean/Erdos647ReductionChain.lean) |
| Stage-1 axiom wrapper | `1` intentional axiom | [`lean/Erdos647Stage1Axiom.lean`](lean/Erdos647Stage1Axiom.lean) |
| Conditional finite-window theorem | theorem-grade, existence-direction | [`lean/Erdos647ConditionalFiniteWindow.lean`](lean/Erdos647ConditionalFiniteWindow.lean) |

The active formal boundary is:

* `55` theorem-grade closed residues;
* `41` open residues;
* `0` source-level sorries in `lean/`;
* `1` intentional Stage-1 axiom:
  `Erdos647Stage1Axiom.openResiduesStage1_no_solution`.

For the exact axiom trail, see [AXIOM_AUDIT.md](AXIOM_AUDIT.md).

This repository also contains a TailKill finite-prefix certificate package.
The top-level entry point is
[`TAILKILL_FINITE_PREFIX_CERTIFICATE.md`](TAILKILL_FINITE_PREFIX_CERTIFICATE.md);
the package itself is under
[`docs/public/tailkill-finite-prefix/`](docs/public/tailkill-finite-prefix/).
It verifies the finite-prefix interface
`FinitePrefixMechanismVerifiedBy K (fun _ _ => 101)` for the TailKill
reduction, records the exact theorem map and manifests, and states its
non-claims separately from the Stage-1 boundary above.

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

Older exploratory proof-engineering modules remain in `lean/` for audit
history, but they are not the active proof boundary described above.

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
paper/            consolidation paper (main.tex, main.pdf); archive/ holds the earlier preprint
docs/public/      public certificate packages and verification entry points
```

Useful entry points:

* [AXIOM_AUDIT.md](AXIOM_AUDIT.md)
* [docs/stage1_boundary.md](docs/stage1_boundary.md)
* [docs/conditional_finite_window.md](docs/conditional_finite_window.md)
* [docs/relation_to_formal_conjectures.md](docs/relation_to_formal_conjectures.md)
* [docs/theorem_map.md](docs/theorem_map.md)
* [TAILKILL_FINITE_PREFIX_CERTIFICATE.md](TAILKILL_FINITE_PREFIX_CERTIFICATE.md)
* [docs/public/tailkill-finite-prefix/README.md](docs/public/tailkill-finite-prefix/README.md)

## Quick start

```bash
./build.sh

# Build the separate conditional finite-window theorem directly.
cd lean
lake build Erdos647ConditionalFiniteWindow

# Audit theorem dependencies.
bash ../scripts/axiom_audit.sh
```

## License

This repository is licensed under the Apache License 2.0, following the
standard practice of public Lean repositories such as
`teorth/equational_theories`, `teorth/analysis`, and `mathlib4`.

## References

* T. F. Bloom, [Erdős Problem #647](https://www.erdosproblems.com/647)
* OEIS [A087280](https://oeis.org/A087280)
* DeepMind,
  [FormalConjectures/ErdosProblems/647.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/647.lean)
