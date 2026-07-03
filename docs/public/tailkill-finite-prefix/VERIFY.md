# TailKill Finite-Prefix Verification Guide

Run commands from the repository root unless stated otherwise.

## 1. Package Manifest Check

This checks source file existence, SHA-256 hashes, and the key banked JSON
status/count fields.

```bash
python3 docs/public/tailkill-finite-prefix/scripts/verify_tailkill_finite_prefix_package.py
```

Expected final line:

```text
TAILKILL_FINITE_PREFIX_PACKAGE_VERIFY_OK
```

## 2. JSON Sanity

```bash
python3 -m json.tool docs/public/tailkill-finite-prefix/MANIFEST.json >/tmp/tailkill_finite_prefix_manifest.check
python3 -m json.tool data/residue_attack/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_manifest_20260603.json >/tmp/tailkill_distributed_manifest.check
python3 -m json.tool data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_production_20260624.json >/tmp/tailkill_tau_chunks_manifest.check
python3 -m json.tool data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_mechanism_20260625.json >/tmp/tailkill_finite_prefix_mechanism.check
python3 -m json.tool data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_composition_ready_20260625.json >/tmp/tailkill_finite_prefix_composition.check
```

## 3. Source Scans

```bash
rg -n "sorry|axiom|native_decide|extern|implemented_by" \
  lean/Erdos647TailKillTauFinitePrefixMechanism.lean \
  lean/Erdos647TailKillTauFinitePrefixComposition.lean
```

Expected: no hits. These are the quantified finite-prefix theorem and
composition modules; they should not depend on `native_decide`.

For the bridge modules, scan separately:

```bash
rg -n "sorry|axiom|native_decide|extern|implemented_by" \
  lean/Erdos647TailKillMasterSlicePartitionBridge.lean \
  lean/Erdos647TailKillMasterSliceLocalIndexBridge.lean
```

Expected bridge hits:

```text
lean/Erdos647TailKillMasterSlicePartitionBridge.lean:132:  native_decide
lean/Erdos647TailKillMasterSlicePartitionBridge.lean:136:  native_decide
```

These two uses certify finite partition cardinality facts. They are not part of
the tau proof chunks or the quantified finite-prefix theorem.

The production tau proof chunks intentionally use `by decide`; they should not
use `native_decide`.

External chunk-family scan:

```bash
rg -n "sorry|axiom|native_decide|extern|implemented_by" \
  lean/Erdos647TailKillTauProofChunks \
  lean/Erdos647TailKillTauFinitePrefixGroup*.lean
```

Expected: no hits. This stronger generated-family scan covers the 220 tau
proof chunk modules through the 22 grouped finite-prefix interfaces, i.e. the
`u < 101`, `K = 10` finite-prefix family over all 41 open residues and 529
sub-AP indices (`2190589` finite-domain entries). Keep it separate from the
bridge-module scan above, where the two partition-bridge `native_decide` hits
are expected and quarantined.

## 4. Lean Compile Checks

Fetch the pinned mathlib cache first:

```bash
cd lean
lake exe cache get
```

Normal compile checks from `lean/`:

```bash
lake build Erdos647TailKillTauFinitePrefixMechanism
lake build Erdos647TailKillTauFinitePrefixComposition
lake build Erdos647TailKillMasterSlicePartitionBridge
lake build Erdos647TailKillMasterSliceLocalIndexBridge
```

Cold compile option for the final finite-prefix modules:

```bash
cd lean
lake clean
lake exe cache get
/usr/bin/time -p lake build Erdos647TailKillTauFinitePrefixMechanism
/usr/bin/time -p lake build Erdos647TailKillTauFinitePrefixComposition
```

A full `lake clean` is heavier and may force all generated proof chunks to
rebuild. Use it for archival release validation, not for a quick smoke check.

## 5. Axiom Census

Use small temporary Lean probe files or an interactive Lean command to run:

```lean
#print axioms Erdos647TailKillTauProofChunks.FinitePrefixMechanism.tailKillFinitePrefixMechanismVerified
#print axioms Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillFinitePrefixMechanismVerified_of_bound
#print axioms Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual
```

The banked audits record only Lean's standard baseline dependencies:

```text
propext
Classical.choice
Quot.sound
```

## 6. Distributed Certificate Verifier

This verifier independently compiles the distributed slice files and bridge
files listed in its manifest. It may take time.

```bash
python3 scripts/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_verify_20260603.py
```

Expected status:

```text
SHIFTED_PRIME_LOCAL_U0_100_S0_528_TAILKILL_DISTRIBUTED_FORMAL_CERTIFICATE_COMPLETE_BANKED
```

## 7. Release Checklist

- Package verifier passes.
- JSON sanity checks pass.
- Lean compile checks pass.
- Source scans have no hits.
- `git diff --cached --check` passes.
- `lean/lakefile.toml`, `lean/lean-toolchain`, and `lean/lake-manifest.json`
  are included in this release branch so the certificate roots and pinned
  dependencies are reproducible from a clean checkout.
