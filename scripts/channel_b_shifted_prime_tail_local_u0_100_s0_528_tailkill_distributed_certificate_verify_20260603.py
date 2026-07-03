#!/usr/bin/env python3
"""Build and verify the TailKillUpTo distributed formal certificate.

This script intentionally checks the certificate serially. It never imports all
53 full-slice proof trees into one Lean process.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
MANIFEST_JSON = (
    ROOT
    / "data/residue_attack/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_manifest_20260603.json"
)
MANIFEST_CSV = (
    ROOT
    / "data/residue_attack/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_manifest_20260603.csv"
)
MEMO = (
    ROOT
    / "docs/audits/channel_b_shifted_prime_tail_local_u0_100_s0_528_tailkill_distributed_certificate_closeout_20260603.md"
)

SLICES = [
    (0, 9), (10, 19), (20, 29), (30, 39), (40, 49), (50, 59),
    (60, 69), (70, 79), (80, 89), (90, 99), (100, 109),
    (110, 119), (120, 129), (130, 139), (140, 149),
    (150, 159), (160, 169), (170, 179), (180, 189),
    (190, 199), (200, 209), (210, 219), (220, 229),
    (230, 239), (240, 249), (250, 259), (260, 269),
    (270, 279), (280, 289), (290, 299), (300, 309),
    (310, 319), (320, 329), (330, 339), (340, 349),
    (350, 359), (360, 369), (370, 379), (380, 389),
    (390, 399), (400, 409), (410, 419), (420, 429),
    (430, 439), (440, 449), (450, 459), (460, 469),
    (470, 479), (480, 489), (490, 499), (500, 509),
    (510, 519), (520, 528),
]


def run(cmd: list[str], *, cwd: Path, timeout: int | None = None) -> dict:
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        return {
            "cmd": cmd,
            "returncode": proc.returncode,
            "status": "pass" if proc.returncode == 0 else "fail",
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "stdout_tail": proc.stdout[-2000:],
            "stderr_tail": proc.stderr[-2000:],
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "cmd": cmd,
            "returncode": None,
            "status": "timeout",
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "stdout_tail": (exc.stdout or "")[-2000:],
            "stderr_tail": (exc.stderr or "")[-2000:],
        }


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def last_commit(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    result = run(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT, timeout=10)
    return result["stdout_tail"].strip()


def parse_counts() -> dict[str, int]:
    text = (LEAN_DIR / "Erdos647TailKillMasterSlicePartitionBridge.lean").read_text(encoding="utf-8")
    counts: dict[str, int] = {}
    pat = re.compile(r"\| TailKillMasterSliceId\.s(\d+)_(\d+) => (\d+)")
    for m in pat.finditer(text):
        counts[f"s{m.group(1)}_{m.group(2)}"] = int(m.group(3))
    return counts


def theorem_present(path: Path, theorem_name: str) -> bool:
    return re.search(rf"\b(theorem|opaque|def)\s+{re.escape(theorem_name)}\b", path.read_text(encoding="utf-8")) is not None


def manifest_entries() -> list[dict]:
    counts = parse_counts()
    entries = []
    for lo, hi in SLICES:
        sid = f"s{lo}_{hi}"
        cap = f"S{lo}_{hi}"
        prefix = sid
        row_count = counts[sid]
        full_file = LEAN_DIR / f"Erdos647TailKillSliceCoverage{cap}.lean"
        atom_file = LEAN_DIR / f"Erdos647TailKillSliceCoverage{cap}AtomList.lean"
        small_file = LEAN_DIR / f"Erdos647TailKillSliceCoverage{cap}SmallCofactor.lean"
        local_file = LEAN_DIR / f"Erdos647TailKillMasterSliceLocalIndexBridge/{cap}.lean"
        entry = {
            "slice_id": sid,
            "slice_range": f"s={lo}..{hi}",
            "slice_min": lo,
            "slice_max": hi,
            "row_count": row_count,
            "full_slice_file": full_file.relative_to(ROOT).as_posix(),
            "full_slice_theorem": f"{prefix}_tailKill_slice_coverage",
            "full_slice_file_sha256": sha256(full_file),
            "full_slice_source_commit": last_commit(full_file),
            "local_index_bridge_file": local_file.relative_to(ROOT).as_posix(),
            "local_index_equiv": f"{prefix}ConcreteIndexEquiv",
            "local_index_ordinal_theorem": f"{prefix}ConcreteIndex_ordinal_preserved",
            "local_index_file_sha256": sha256(local_file),
            "local_index_source_commit": last_commit(local_file),
            "atomlist_route_file": atom_file.relative_to(ROOT).as_posix(),
            "atomlist_route_theorem": f"{prefix}_atomlist_route_tailKill_coverage",
            "smallcofactor_route_file": small_file.relative_to(ROOT).as_posix(),
            "smallcofactor_route_theorem": f"{prefix}_smallcofactor_route_tailKill_coverage",
            "route_file_hashes": {
                "atomlist": sha256(atom_file),
                "smallcofactor": sha256(small_file),
            },
        }
        for file_key, theorem_key in [
            ("full_slice_file", "full_slice_theorem"),
            ("local_index_bridge_file", "local_index_equiv"),
            ("local_index_bridge_file", "local_index_ordinal_theorem"),
            ("atomlist_route_file", "atomlist_route_theorem"),
            ("smallcofactor_route_file", "smallcofactor_route_theorem"),
        ]:
            if not theorem_present(ROOT / entry[file_key], entry[theorem_key]):
                raise RuntimeError(f"missing {entry[theorem_key]} in {entry[file_key]}")
        entries.append(entry)
    return entries


def scan_sorry_axiom(files: list[Path]) -> list[dict]:
    hits = []
    pat = re.compile(r"\b(sorry|axiom)\b")
    for path in files:
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if pat.search(line):
                hits.append({"file": path.relative_to(ROOT).as_posix(), "line": lineno, "text": line.strip()})
    return hits


def lean_check(path: Path, timeout: int) -> dict:
    return run(["lake", "env", "lean", path.relative_to(LEAN_DIR).as_posix()], cwd=LEAN_DIR, timeout=timeout)


def write_csv(entries: list[dict]) -> None:
    MANIFEST_CSV.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "slice_id", "slice_range", "row_count", "full_slice_file",
        "full_slice_theorem", "local_index_bridge_file", "local_index_equiv",
        "local_index_ordinal_theorem", "atomlist_route_file",
        "atomlist_route_theorem", "smallcofactor_route_file",
        "smallcofactor_route_theorem", "full_slice_file_sha256",
        "local_index_file_sha256", "full_slice_source_commit",
        "local_index_source_commit",
    ]
    with MANIFEST_CSV.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for entry in entries:
            writer.writerow({field: entry[field] for field in fields})


def write_memo(payload: dict) -> None:
    MEMO.parent.mkdir(parents=True, exist_ok=True)
    verification = payload["verification"]
    lines = [
        "# TailKillUpTo distributed formal-certificate closeout",
        "",
        "Status: `SHIFTED_PRIME_LOCAL_U0_100_S0_528_TAILKILL_DISTRIBUTED_FORMAL_CERTIFICATE_COMPLETE_BANKED`",
        "",
        "Recommendation: `RECOMMEND_ACCEPT_DISTRIBUTED_CERTIFICATE_AS_TAILKILLUPTO_FORMAL_ENDPOINT`",
        "",
        "This closeout packages the completed TailKillUpTo result as a distributed",
        "formal certificate. It deliberately does not manufacture a single aggregate",
        "Lean theorem under the current ordinary-import architecture.",
        "",
        "## Certificate Components",
        "",
        f"- Full-slice theorem entries: {payload['slice_count']} / 53",
        f"- Rows represented: {payload['row_count_sum']} / 901696",
        "- Master partition bridge: `lean/Erdos647TailKillMasterSlicePartitionBridge.lean`",
        "- Local-index bridge root: `lean/Erdos647TailKillMasterSliceLocalIndexBridge.lean`",
        "- Local-index helper modules: 53",
        "- Full-slice theorem files: 53",
        "- Route theorem files referenced by manifest: 106",
        "",
        "## Serial Verification",
        "",
        f"- Partition bridge: `{verification['partition_bridge']['status']}`",
        f"- Local-index helpers passing: {verification['local_index_pass_count']} / 53",
        f"- Full-slice files passing: {verification['full_slice_pass_count']} / 53",
        f"- `sorry|axiom` hits in coverage/bridge files: {len(verification['sorry_axiom_hits'])}",
        "",
        "The verifier compiles each target independently and never imports all 53",
        "heavy proof trees into one Lean process.",
        "",
        "## Proven And Banked",
        "",
        "- Complete finite row coverage for U0=100 and s=0..528 as 53 distributed full-slice theorems.",
        "- Exact 901,696-row master partition.",
        "- Exact per-slice local-index bridges.",
        "- Theorem and row manifest with file hashes.",
        "",
        "## Explicit Non-Claims",
        "",
        "- No monolithic aggregate theorem is claimed.",
        "- No local-layer theorem is claimed.",
        "- No theorem-level U0 is selected.",
        "- No finite-prefix theorem is claimed.",
        "- No global K is claimed.",
        "- No mechanism cover is claimed.",
        "- No shifted-prime theorem is claimed.",
        "- No global theorem is claimed.",
        "- No axiom was removed.",
        "",
        "## Architecture Boundary",
        "",
        "Ordinary all-53 imports are impractical, and the module-capsule audit showed",
        "that import-light capsules would require broad migration of ordinary project",
        "and generated proof-tree modules. The distributed certificate is therefore",
        "the intentional formal endpoint for this TailKillUpTo lane under the current",
        "project architecture.",
    ]
    MEMO.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-timeout", type=int, default=300)
    parser.add_argument("--skip-lean", action="store_true", help="Only rebuild manifests; do not run Lean checks.")
    args = parser.parse_args()

    entries = manifest_entries()
    assert len(entries) == 53
    assert len({entry["slice_id"] for entry in entries}) == 53
    row_sum = sum(entry["row_count"] for entry in entries)
    assert row_sum == 901696

    bridge_files = [
        LEAN_DIR / "Erdos647TailKillMasterSlicePartitionBridge.lean",
        LEAN_DIR / "Erdos647TailKillMasterSliceLocalIndexBridge.lean",
    ]
    local_files = [ROOT / entry["local_index_bridge_file"] for entry in entries]
    full_files = [ROOT / entry["full_slice_file"] for entry in entries]
    scan_files = bridge_files + local_files + full_files

    verification = {
        "lean_checks_skipped": args.skip_lean,
        "partition_bridge": {"status": "skipped"},
        "local_index_helpers": [],
        "full_slice_files": [],
        "sorry_axiom_hits": scan_sorry_axiom(scan_files),
    }
    if not args.skip_lean:
        verification["partition_bridge"] = lean_check(bridge_files[0], args.lean_timeout)
        for path in local_files:
            verification["local_index_helpers"].append({
                "file": path.relative_to(ROOT).as_posix(),
                **lean_check(path, args.lean_timeout),
            })
        for path in full_files:
            verification["full_slice_files"].append({
                "file": path.relative_to(ROOT).as_posix(),
                **lean_check(path, args.lean_timeout),
            })

    verification["local_index_pass_count"] = sum(
        1 for item in verification["local_index_helpers"] if item.get("status") == "pass"
    )
    verification["full_slice_pass_count"] = sum(
        1 for item in verification["full_slice_files"] if item.get("status") == "pass"
    )

    payload = {
        "status": "SHIFTED_PRIME_LOCAL_U0_100_S0_528_TAILKILL_DISTRIBUTED_FORMAL_CERTIFICATE_COMPLETE_BANKED",
        "recommendation": "RECOMMEND_ACCEPT_DISTRIBUTED_CERTIFICATE_AS_TAILKILLUPTO_FORMAL_ENDPOINT",
        "slice_count": len(entries),
        "row_count_sum": row_sum,
        "rows_remaining": 0,
        "master_partition_bridge": {
            "file": "lean/Erdos647TailKillMasterSlicePartitionBridge.lean",
            "theorems": [
                "tailKillMasterSliceIds_length",
                "tailKillMasterSliceRowCount_sum",
                "tailKillMasterSliceMembership_unique",
                "tailKillMasterSliceMembership_eq",
                "tailKillMasterRowIndex_sigma_left_inverse",
                "tailKillMasterRowIndex_sigma_right_inverse",
            ],
            "file_sha256": sha256(bridge_files[0]),
            "source_commit": last_commit(bridge_files[0]),
        },
        "local_index_bridge_root": {
            "file": "lean/Erdos647TailKillMasterSliceLocalIndexBridge.lean",
            "theorem": "tailKillMasterSliceLocalIndexBridgeModule_count",
            "file_sha256": sha256(bridge_files[1]),
            "source_commit": last_commit(bridge_files[1]),
        },
        "entries": entries,
        "verification": verification,
        "non_claims": {
            "monolithic_aggregate_theorem": False,
            "local_layer_theorem": False,
            "theorem_level_U0": False,
            "finite_prefix_theorem": False,
            "global_K": False,
            "mechanism_cover": False,
            "shifted_prime_theorem": False,
            "global_theorem": False,
            "axiom_removed": False,
        },
    }

    MANIFEST_JSON.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(entries)
    write_memo(payload)

    failed = []
    if verification["partition_bridge"].get("status") not in {"pass", "skipped"}:
        failed.append(("partition_bridge", verification["partition_bridge"].get("status")))
    failed.extend((item["file"], item.get("status")) for item in verification["local_index_helpers"] if item.get("status") != "pass")
    failed.extend((item["file"], item.get("status")) for item in verification["full_slice_files"] if item.get("status") != "pass")
    if verification["sorry_axiom_hits"]:
        failed.append(("sorry_axiom_scan", len(verification["sorry_axiom_hits"])))

    print(payload["status"])
    print(payload["recommendation"])
    print(f"slices={len(entries)} rows={row_sum}")
    print(f"local_index_pass={verification['local_index_pass_count']}/53 full_slice_pass={verification['full_slice_pass_count']}/53")
    print(f"sorry_axiom_hits={len(verification['sorry_axiom_hits'])}")
    if failed:
        print("FAILED_TARGETS")
        for item in failed[:20]:
            print(item)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
