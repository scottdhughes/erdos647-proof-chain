# TailKill Finite-Prefix Certificate

This is the top-level entry point for the TailKill finite-prefix certificate
package in this repository.

Start here:

- Package index:
  [`docs/public/tailkill-finite-prefix/`](docs/public/tailkill-finite-prefix/)
- Verification guide:
  [`docs/public/tailkill-finite-prefix/VERIFY.md`](docs/public/tailkill-finite-prefix/VERIFY.md)
- Theorem map:
  [`docs/public/tailkill-finite-prefix/THEOREM_MAP.md`](docs/public/tailkill-finite-prefix/THEOREM_MAP.md)
- Manifest:
  [`docs/public/tailkill-finite-prefix/MANIFEST.json`](docs/public/tailkill-finite-prefix/MANIFEST.json)

## What This Certificate Covers

The package verifies the finite-prefix TailKill interface

```lean
FinitePrefixMechanismVerifiedBy K (fun _ _ => 101)
```

with base certified bound

```lean
K := fun _ _ _ => 10
```

and includes the composition-ready lift to any eventual bound function that
dominates `10` on `u < 101`.

The package records:

- `53 / 53` TailKillUpTo slice theorem files;
- `901696 / 901696` obligated slice rows represented;
- exact master partition and local-index bridge files;
- `220` tau proof chunks covering `2190589` finite-domain entries;
- public manifests, verification commands, and theorem names.

## What This Certificate Does Not Claim

This package does not claim:

- a solution to Erdős Problem 647;
- an eventual-u theorem;
- a local-layer theorem;
- a global theorem;
- a shifted-prime theorem;
- a global constant `K`;
- a mechanism cover for all `u`;
- a monolithic aggregate theorem over all proof trees;
- axiom or assumption removal.

The remaining mathematical obligation is still the eventual mechanism-cover
statement beyond the finite prefix.

## Quick Verification

Run the package verifier from the repository root:

```bash
python3 docs/public/tailkill-finite-prefix/scripts/verify_tailkill_finite_prefix_package.py
```

For full Lean validation and source-scan commands, follow
[`docs/public/tailkill-finite-prefix/VERIFY.md`](docs/public/tailkill-finite-prefix/VERIFY.md).
