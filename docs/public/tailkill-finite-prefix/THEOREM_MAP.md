# TailKill Finite-Prefix Theorem Map

This file maps the public package claims to the exact Lean modules and banked
audit artifacts.

## Mechanism Interface

File:

```text
lean/Erdos647ShiftedPrimeTailMechanismCover.lean
```

Key definitions:

```lean
ShiftedPrimeMechanismWitness
ShiftedPrimeMechanismCoverEventuallyBy
FinitePrefixMechanismVerifiedBy
ShiftedPrimeMechanismCoverWithFinitePrefixBy
```

The bridge from a mechanism witness to the existing TailKillUpTo surface is:

```lean
Erdos647ShiftedPrimeChannel.tailKillUpTo_of_mechanismWitness
```

The bridge from eventual plus finite-prefix coverage to the existing closure
surface is:

```lean
Erdos647ShiftedPrimeChannel.shiftedPrimeOpenSubAPClosesBy_of_mechanismCoverWithFinitePrefix
```

## Distributed Row Coverage Certificate

Closeout audit:

```text
docs/audits/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_closeout_20260603.md
```

Manifest:

```text
data/residue_attack/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_manifest_20260603.json
```

Verifier:

```text
scripts/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_verify_20260603.py
```

Certified facts recorded there:

- `53 / 53` full-slice theorem entries.
- `901696 / 901696` rows represented.
- `0` rows remaining.
- Exact master partition bridge:

```text
lean/Erdos647TailKillMasterSlicePartitionBridge.lean
```

- Exact local-index bridge root:

```text
lean/Erdos647TailKillMasterSliceLocalIndexBridge.lean
```

This is a distributed certificate, not a monolithic aggregate theorem.

## Tau Proof Chunks

Production manifest:

```text
data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_production_20260624.json
```

Generator:

```text
scripts/channel_b_shifted_prime_tail_tau_proof_chunks_production_20260624.py
```

Lean chunk directory:

```text
lean/Erdos647TailKillTauProofChunks/
```

Recorded facts:

- `220` proof chunks.
- `10000` rows per full chunk.
- `2190589` total finite-domain entries.
- `450848` witness entries.
- `1739741` complement entries.
- `1739740` factor-certificate entries.
- `1` zero-or-one entry.
- Import probes were practical through the full chunk family.

## Finite-Prefix Mechanism Theorem

Lean module:

```text
lean/Erdos647TailKillTauFinitePrefixMechanism.lean
```

Audit:

```text
docs/audits/channel_b_shifted_prime_tail_tau_finite_prefix_mechanism_20260625.md
```

Manifest:

```text
data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_mechanism_20260625.json
```

Theorem:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixMechanism.tailKillFinitePrefixMechanismVerified :
  FinitePrefixMechanismVerifiedBy
    (fun _ _ _ => 10)
    (fun _ _ => 101)
```

Recorded validation:

- Lean compile of final theorem module.
- Axiom census on exported theorem:

```text
[propext, Classical.choice, Quot.sound]
```

## Composition-Ready Lift

Lean module:

```text
lean/Erdos647TailKillTauFinitePrefixComposition.lean
```

Audit:

```text
docs/audits/channel_b_shifted_prime_tail_tau_finite_prefix_composition_ready_20260625.md
```

Manifest:

```text
data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_composition_ready_20260625.json
```

Key theorem:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillFinitePrefixMechanismVerified_of_bound
```

Meaning:

For any `K : Nat -> Nat -> Nat -> Nat`, if `10 <= K r s u` for every
finite-prefix point with `u < 101`, then:

```lean
FinitePrefixMechanismVerifiedBy K (fun _ _ => 101)
```

The automatic patch:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.patchedK
```

is:

```lean
if u < 101 then max 10 (K r s u) else K r s u
```

Final scaffold:

```lean
Erdos647TailKillTauProofChunks.FinitePrefixComposition.tailKillMechanismCoverWithFinitePrefixBy_patchedK_of_eventual
```

This states that a future eventual cover for `K` after `101` combines with
the finite-prefix theorem for `patchedK K`.

## Remaining Theorem Boundary

The next mathematical theorem is not in this package:

```lean
ShiftedPrimeMechanismCoverEventuallyBy K (fun _ _ => 101)
```

The current active work is arithmetic source discovery for the eventual range,
especially real constructors for:

```lean
AlternateShiftAtomSource C u dAlt
```

or a nonlocal obstruction that rules out the no-source residual family in the
prime channel.
