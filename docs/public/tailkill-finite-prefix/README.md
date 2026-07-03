# TailKill Finite-Prefix Certificate Package

This directory is the public-facing index for the TailKill finite-prefix
certificate inside the Problem 647 proof-chain repository.

It is intentionally a package of pointers, manifests, and verification
commands. This release branch also carries the Lean proof objects and generated
tau proof chunks needed to verify the finite-prefix certificate from a clean
GitHub checkout. The authoritative Lean, JSON, CSV, script, and audit files
remain in their normal repository locations and are referenced from
`MANIFEST.json`.

This release pins `lean/lean-toolchain`, adds `lean/lake-manifest.json`, and
registers the certificate roots in `lean/lakefile.toml` so the named Lake
targets below are discoverable without relying on the private audit branch.

## Certified Scope

- Problem lane: Erdos Problem 647 shifted-prime / TailKill reduction.
- Finite-prefix interface:

```lean
FinitePrefixMechanismVerifiedBy K (fun _ _ => 101)
```

- Base certified bound:

```lean
K := fun _ _ _ => 10
```

- Composition-ready lift: any `K : Nat -> Nat -> Nat -> Nat` that is
  pointwise at least `10` on `u < 101`, plus the `patchedK` helper that leaves
  an eventual candidate `K` unchanged for `u >= 101`.
- Distributed slice certificate:
  - `53 / 53` TailKillUpTo full-slice theorem files.
  - `901696 / 901696` obligated rows represented.
  - Exact master partition and local-index bridges.
- Tau finite-prefix certificate:
  - `220` Lean proof chunks.
  - `2190589` finite-domain entries.
  - `450848` witness entries.
  - `1739741` complement entries.
  - `by decide` proof chunks, not `native_decide`.
  - The older partition bridge has two `native_decide` finite cardinality
    certificates; those are separate from the tau proof chunks and the
    quantified finite-prefix theorem.

## Main Lean Theorems

Base finite-prefix theorem:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixMechanism.tailKillFinitePrefixMechanismVerified :
  FinitePrefixMechanismVerifiedBy
    (fun _ _ _ => 10)
    (fun _ _ => 101)
```

Composition-ready lift:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillFinitePrefixMechanismVerified_of_bound
```

Automatic finite-prefix patch for a future eventual bound:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.patchedK
```

Final finite-plus-eventual scaffold:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual
```

See `THEOREM_MAP.md` for signatures and dependencies.

## Explicit Non-Claims

This package does not claim:

- a solution to Erdos Problem 647;
- an eventual-u theorem;
- a local-layer theorem;
- a global theorem;
- a shifted-prime theorem;
- a global constant `K`;
- a mechanism cover for all `u`;
- a monolithic aggregate theorem over all proof trees;
- axiom or assumption removal.

The remaining mathematical obligation is still:

```lean
ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)
```

for an explicit eventual witness-bound function `K`.

## How To Verify

Start with:

```bash
python3 docs/public/tailkill-finite-prefix/scripts/verify_tailkill_finite_prefix_package.py
```

Then follow `VERIFY.md` for dependency cache setup, Lean checks, source scans,
and optional cold recompilation.
