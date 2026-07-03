# TailKill tau finite-prefix composition readiness

Status: `SHIFTED_PRIME_TAILKILL_TAU_FINITE_PREFIX_COMPOSITION_READY_BANKED`

Verdict: `TAILKILL_FINITE_PREFIX_COMPOSITION_READY_GREEN`

Lean module: `lean/Erdos647TailKillTauFinitePrefixComposition.lean`

This artifact makes the banked TailKillUpTo finite-prefix mechanism theorem
composition-ready for a future eventual witness-bound function.

## Theorems

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillUpTo_bound_mono`

Project-native `TailKillUpTo` is monotone in its numeric witness bound.

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.shiftedPrimeMechanismWitness_mono`

`ShiftedPrimeMechanismWitness` is monotone in the pointwise witness-bound
function at the queried `(r, s, u)`.

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillFinitePrefixMechanismVerified_of_bound`

For any `K : Nat -> Nat -> Nat -> Nat`,
if `10 <= K r s u` for every finite-prefix point with `u < 101`, then
`FinitePrefixMechanismVerifiedBy K (fun _ _ => 101)`.

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillMechanismCoverWithFinitePrefixBy_of_eventual_and_bound`

For any such `K`, an eventual cover
`ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)` combines with
the lifted finite prefix to produce
`ShiftedPrimeMechanismCoverWithFinitePrefixBy K (fun _ _ => 101)`.

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.patchedK`

For any eventual candidate `K`, `patchedK K` raises the bound to the finite
floor only on `u < 101`:

```lean
if u < 101 then max 10 (K r s u) else K r s u
```

`Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual`

An eventual cover for `K` after `101` directly yields
`ShiftedPrimeMechanismCoverWithFinitePrefixBy (patchedK K) (fun _ _ => 101)`.
Thus future users do not need to supply the finite-prefix domination hypothesis
manually.

## Boundary

`K` may depend on `r`, `s`, and `u`. The finite-prefix convention remains
`U0 := fun _ _ => 101`.

The remaining mathematical theorem is:

```lean
ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)
```

for a chosen eventual witness-bound function `K`. That theorem is not proved
or claimed here.

This artifact does not alter proof chunks, generated evidence, slice theorems,
routes, adapters, bridges, the Lake file, or protected files. It does not prove
an eventual-u theorem, local-layer theorem, finite-prefix theorem beyond this
interface lift, shifted-prime theorem, or global theorem.

## Validation

Fresh Lean compile:

```text
cd lean && /usr/bin/time -p lake env lean -o .lake/build/lib/lean/Erdos647TailKillTauFinitePrefixComposition.olean Erdos647TailKillTauFinitePrefixComposition.lean
real 164.88
user 4.70
sys 14.06
```

Source scan:

```text
rg -n "sorry|axiom|native_decide|extern|implemented_by" lean/Erdos647TailKillTauFinitePrefixComposition.lean
```

returned no hits.

`#print axioms` on all four top-level theorems reports only:

```text
[propext, Classical.choice, Quot.sound]
```

After the `patchedK` polish, `#print axioms` reports:

```text
tailKillUpTo_bound_mono: [propext, Classical.choice, Quot.sound]
shiftedPrimeMechanismWitness_mono: [propext, Classical.choice, Quot.sound]
tailKillFinitePrefixMechanismVerified_of_bound: [propext, Classical.choice, Quot.sound]
tailKillMechanismCoverWithFinitePrefixBy_of_eventual_and_bound: [propext, Classical.choice, Quot.sound]
patchedK_prefix_bound: [propext]
patchedK_eq_of_prefix_le: [propext]
tailKillMechanismCoverEventually_patchedK_of_eventual: [propext, Classical.choice, Quot.sound]
tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual: [propext, Classical.choice, Quot.sound]
```

`lean4checker` archival replay was requested but is unavailable in this local
Lake environment:

```text
cd lean && lake env lean4checker --help
could not execute external process 'lean4checker'
```
