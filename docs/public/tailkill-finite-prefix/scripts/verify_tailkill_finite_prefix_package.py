#!/usr/bin/env python3
"""Verify the TailKill finite-prefix public package manifest.

This is a lightweight release gate. It checks file hashes and the key banked
JSON status/count fields that the public package advertises. It does not
replace the heavier Lean compiles or the distributed certificate verifier.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
MANIFEST = PACKAGE_ROOT / "MANIFEST.json"


def find_repo_root(start: Path) -> Path:
    """Find the repository root from the package location."""
    for candidate in [start, *start.parents]:
        if (candidate / ".git").exists() and (candidate / "lean").is_dir():
            return candidate
    raise RuntimeError(f"could not find repository root above {start}")


REPO_ROOT = find_repo_root(PACKAGE_ROOT)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def check_hashes(manifest: dict[str, Any]) -> None:
    for source in manifest["sources"]:
        path = REPO_ROOT / source["path"]
        require(path.exists(), f"missing source: {source['path']}")
        observed = sha256(path)
        require(
            observed == source["sha256"],
            f"sha256 mismatch for {source['path']}: {observed} != {source['sha256']}",
        )


def check_statuses(manifest: dict[str, Any]) -> None:
    expected = manifest["expected_statuses"]

    distributed = load_json(
        REPO_ROOT
        / "data/residue_attack/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_manifest_20260603.json"
    )
    require(
        distributed["status"] == expected["distributed_certificate_manifest"],
        "distributed certificate status drift",
    )
    require(distributed["slice_count"] == manifest["scope"]["slice_count"], "slice count drift")
    require(
        distributed["row_count_sum"] == manifest["scope"]["tailkill_obligated_rows"],
        "TailKill row count drift",
    )
    require(distributed["rows_remaining"] == 0, "TailKill rows remaining drift")

    chunks = load_json(
        REPO_ROOT
        / "data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_production_20260624.json"
    )
    require(chunks["verdict"] == expected["tau_proof_chunks_verdict"], "tau chunk verdict drift")
    require(chunks["chunk_count"] == manifest["scope"]["tau_chunk_count"], "tau chunk count drift")
    require(chunks["totals"]["entries"] == manifest["scope"]["tau_domain_entries"], "tau entry count drift")
    require(chunks["totals"]["witness"] == manifest["scope"]["tau_witness_entries"], "witness count drift")
    require(
        chunks["totals"]["complement"] == manifest["scope"]["tau_complement_entries"],
        "complement count drift",
    )

    finite = load_json(
        REPO_ROOT
        / "data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_mechanism_20260625.json"
    )
    require(finite["verdict"] == expected["finite_prefix_mechanism_verdict"], "finite theorem verdict drift")
    require(finite["chunk_count"] == manifest["scope"]["tau_chunk_count"], "finite theorem chunk count drift")
    require(finite["domain_entries"] == manifest["scope"]["tau_domain_entries"], "finite theorem domain drift")
    require(finite["K"] == "fun _ _ _ => 10", "finite theorem K drift")
    require(finite["U0"] == "fun _ _ => 101", "finite theorem U0 drift")
    require(
        finite["finite_prefix_theorem"] == manifest["primary_theorems"]["finite_prefix"],
        "finite theorem name drift",
    )

    composition = load_json(
        REPO_ROOT
        / "data/residue_attack/channel_b_shifted_prime_tail_tau_finite_prefix_composition_ready_20260625.json"
    )
    require(
        composition["verdict"] == expected["finite_prefix_composition_verdict"],
        "composition verdict drift",
    )
    require(composition["base_K"] == "fun _ _ _ => 10", "composition base K drift")
    require(composition["U0"] == "fun _ _ => 101", "composition U0 drift")
    require(
        composition["remaining_eventual_theorem_schema"] == manifest["remaining_theorem"]
        or manifest["remaining_theorem"] in composition["remaining_eventual_theorem_schema"],
        "remaining theorem schema drift",
    )


def main() -> None:
    manifest = load_json(MANIFEST)
    check_hashes(manifest)
    check_statuses(manifest)
    print("TAILKILL_FINITE_PREFIX_PACKAGE_VERIFY_OK")


if __name__ == "__main__":
    main()
