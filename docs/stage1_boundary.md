# Stage 1 Boundary

This note records the current formal boundary of the Stage-1 core and
the stop reason for the bounded positive-footprint search family.

## Current formal state

The active theorem path is now:

1. theorem-grade reduction to the `96` sieve survivors;
2. theorem-grade full-value closure of `55` residues;
3. proof-critical open set defined by complement:
   `openResiduesStage1 = survivingResidues96 \ closedResiduesStage1`;
4. theorem-grade conditional reduction:
   `Erdos647ReductionChain.erdos647_conditional_on_openResiduesStage1`;
5. single intentional axiom wrapper:
   `Erdos647Stage1Axiom.openResiduesStage1_no_solution`.

Current honest Stage-1 status:

* `55` theorem-grade closed residues
* `41` open residues
* diagnostic decomposition:
  * `27` non-`ble1`
  * `14` genuinely hard

Bridge 3 is retired from the active proof path. The current proof-grade
frontier is the `41`-residue open set, not the old Bridge-3 theorem.

## Retired bounded lanes

The following bounded theorem-search architectures are retired:

* peeled-cofactor / Bridge-3 budget transfer
* 23/29 promotion
* one-shift sweeps
* spaced-triple / same-prime overlap CSP
* fixed-support prefix-9 positive-footprint trees
* adaptive recurring-small-prime prefix-9 trees

These are retired because they failed on the current frontier, and in
the prefix-tree case there is now a structural stop reason.

## All-avoid obstruction

Fix a prefix length `K` and a finite set `P` of extra primes with:

* `p > K` for every `p ∈ P`;
* `p ∤ 2520`;
* `p` pairwise coprime and coprime to the root modulus used by the tree.

Suppose a proof-search tree refines a residue class for `N` and only
closes leaves by forcing some congruence

`2520 * N - k ≡ 0 [MOD p]`

for a shift `1 ≤ k ≤ K` and some `p ∈ P`.

Then for each fixed `p ∈ P`:

* each shift `k` excludes at most one residue class modulo `p`;
* the entire prefix `{1, ..., K}` excludes at most `K` residue classes;
* because `p > K`, at least one residue class modulo `p` avoids all of
  those exclusions.

Choosing one avoiding class modulo each `p ∈ P`, the Chinese remainder
theorem produces a simultaneous residue class that extends the root
class and avoids every positive-footprint hit from all primes in `P`.

So any finite positive-footprint tree of this type has an all-avoid
branch. It cannot be complete unless it introduces a genuinely
different leaf type.

## Scope

This note closes a search strategy, not a residue.

It does **not** prove that the `41` open residues are impossible.
It does **not** prove that no future method can close them.
It does **not** rule out a future theorem with a different leaf type.

What it does prove at the repo-design level is narrower and decisive:
more bounded work of the retired positive-footprint-tree shape should
not be reopened under a different prime pool, depth cap, or greedy
heuristic.
