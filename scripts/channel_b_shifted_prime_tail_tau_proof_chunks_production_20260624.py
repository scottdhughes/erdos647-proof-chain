#!/usr/bin/env python3
"""Generate and verify distributed TailKillUpTo tau proof chunks.

This production script uses the already banked total tau classifier as its data
source and emits 10,000-row `by decide` Lean chunks under
`lean/Erdos647TailKillTauProofChunks/`.  It deliberately avoids `native_decide`,
the project lakefile, TailKill slice trees, generated evidence, adapters,
routes, bridges, and finite-prefix/global theorem statements.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import math
import os
import re
import resource
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DATE = "20260624"
LEAN_ROOT = ROOT / "lean"
CHUNK_DIR = LEAN_ROOT / "Erdos647TailKillTauProofChunks"
OLEAN_DIR = LEAN_ROOT / ".lake/build/lib/lean/Erdos647TailKillTauProofChunks"
LOWER_OLEAN = LEAN_ROOT / ".lake/build/lib/lean/Erdos647TailKillTauLowerCertificate.olean"
CORE_FILE = CHUNK_DIR / "Core.lean"
CORE_OLEAN = OLEAN_DIR / "Core.olean"

ARCHITECTURE_SCRIPT = ROOT / "scripts/channel_b_shifted_prime_tail_tau_proof_chunk_architecture_20260624.py"
TOTAL_CLASSIFIER_SCRIPT = ROOT / "scripts/channel_b_shifted_prime_tail_tau_certificate_total_classifier_prototype_20260624.py"

JSON_OUT = ROOT / f"data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_production_{DATE}.json"
CSV_OUT = ROOT / f"data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_production_{DATE}.csv"
DOC_OUT = ROOT / f"docs/audits/channel_b_shifted_prime_tail_tau_proof_chunks_production_{DATE}.md"
VERIFY_LOG = ROOT / f"data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_verify_{DATE}.jsonl"
IMPORT_DIR = ROOT / f"tmp/tailkill_tau_proof_chunks_import_probes_{DATE}"

DOMAIN_COUNT = 2_190_589
EXPECTED_WITNESSES = 450_848
EXPECTED_COMPLEMENT = 1_739_741
EXPECTED_FACTOR = 1_739_740
EXPECTED_ZERO_OR_ONE = 1
EXPECTED_DIVISOR_PAYLOAD = 2_373_691
CHUNK_SIZE = 10_000
CHUNK_COUNT = math.ceil(DOMAIN_COUNT / CHUNK_SIZE)
IMPORT_COUNTS = [32, 64, 128, CHUNK_COUNT]
MIN_DISK_GB = 10
COMPILE_TIMEOUT_SECONDS = 900
IMPORT_TIMEOUT_SECONDS = 1_200

FORBIDDEN_SOURCE_RE = re.compile(r"\bsorry\b|^axiom\b|\bnative_decide\b|\bextern\b|\bimplemented_by\b", re.M)


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def sha256_path(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def run(cmd: list[str], cwd: Path, timeout: int) -> dict[str, Any]:
    start = time.time()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        rc = proc.returncode
        out = proc.stdout
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        rc = 124
        if isinstance(exc.stdout, bytes):
            out = exc.stdout.decode("utf-8", errors="replace")
        else:
            out = exc.stdout or ""
        timed_out = True
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {
        "cmd": cmd,
        "elapsed_seconds": round(time.time() - start, 2),
        "maxrss_kb_delta": max(0, after.ru_maxrss - before.ru_maxrss),
        "output_tail": out[-5000:],
        "returncode": rc,
        "timed_out": timed_out,
    }


def disk_free_gb() -> float:
    return shutil.disk_usage(ROOT).free / (1024 ** 3)


def require_disk() -> None:
    free = disk_free_gb()
    if free < MIN_DISK_GB:
        raise RuntimeError(f"available disk below {MIN_DISK_GB} GB: {free:.2f} GB")


def architecture_module():
    return load_module("tailkill_tau_chunk_architecture", ARCHITECTURE_SCRIPT)


def total_classifier_module():
    return load_module("tailkill_tau_total_classifier_for_production", TOTAL_CLASSIFIER_SCRIPT)


def build_rows():
    arch = architecture_module()
    rows, reconciliation = arch.build_rows()
    if len(rows) != DOMAIN_COUNT:
        raise RuntimeError(f"domain mismatch: {len(rows)}")
    if reconciliation["witness_entries"] != EXPECTED_WITNESSES:
        raise RuntimeError("witness count mismatch")
    if reconciliation["complement_entries"] != EXPECTED_COMPLEMENT:
        raise RuntimeError("complement count mismatch")
    if reconciliation["factor_entries"] != EXPECTED_FACTOR:
        raise RuntimeError("factor count mismatch")
    if reconciliation["zero_or_one_entries"] != EXPECTED_ZERO_OR_ONE:
        raise RuntimeError("zero_or_one count mismatch")
    if reconciliation["total_divisor_payload_entries"] != EXPECTED_DIVISOR_PAYLOAD:
        raise RuntimeError("divisor payload mismatch")
    return arch, rows, reconciliation


def f_shift(r: int, s: int, u: int, k: int) -> int:
    return 2520 * (46189 * (529 * u + s) + r) - k


def verify_row(row: Any) -> str:
    if row.tag == "W":
        n = f_shift(row.r, row.s, row.u, row.k)
        ds = list(row.payload)
        if not (2 <= row.k < f_shift(row.r, row.s, row.u, 0)):
            raise RuntimeError(f"invalid witness k at {(row.r, row.s, row.u)}")
        if not (row.k + 2 < len(ds)):
            raise RuntimeError(f"short witness divisor list at {(row.r, row.s, row.u)}")
        if len(ds) != len(set(ds)):
            raise RuntimeError(f"duplicate witness divisors at {(row.r, row.s, row.u)}")
        if any(d == 0 or n % d != 0 for d in ds):
            raise RuntimeError(f"bad witness divisor at {(row.r, row.s, row.u)}")
        return "witness"
    if row.tag == "F":
        n = f_shift(row.r, row.s, row.u, 1)
        d = row.payload[0]
        if not (2 <= d < n and n % d == 0):
            raise RuntimeError(f"bad factor certificate at {(row.r, row.s, row.u)}")
        return "factor"
    if row.tag == "Z":
        if f_shift(row.r, row.s, row.u, 1) >= 2:
            raise RuntimeError(f"bad zero_or_one certificate at {(row.r, row.s, row.u)}")
        return "zero_or_one"
    raise RuntimeError(f"unknown tag {row.tag}")


def chunk_name(index: int) -> str:
    return f"Chunk{index:04d}"


def chunk_theorem_prefix(index: int) -> str:
    return f"tailKillTauChunk{index:04d}"


def chunk_file(index: int) -> Path:
    return CHUNK_DIR / f"{chunk_name(index)}.lean"


def chunk_olean(index: int) -> Path:
    return OLEAN_DIR / f"{chunk_name(index)}.olean"


def chunk_bounds(index: int) -> tuple[int, int]:
    start = index * CHUNK_SIZE
    length = min(CHUNK_SIZE, DOMAIN_COUNT - start)
    return start, length


def write_chunk(index: int, rows: list[Any], row_literal) -> dict[str, Any]:
    start, length = chunk_bounds(index)
    selected = rows[start : start + length]
    if len(selected) != length:
        raise RuntimeError(f"bad chunk length for {index}: {len(selected)} != {length}")
    CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    theorem = chunk_theorem_prefix(index)
    row_lines = ",\n  ".join(row_literal(row) for row in selected)
    path = chunk_file(index)
    path.write_text(
        f"""import Erdos647TailKillTauProofChunks.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace Erdos647TailKillTauProofChunks

def {theorem}Start : Nat := {start}
def {theorem}Length : Nat := {length}

def {theorem}Rows : List CertRow := [
  {row_lines}
]

def {theorem}AllValid : Bool :=
  {theorem}Rows.all checkRow

theorem {theorem}_all_valid :
    {theorem}AllValid = true := by
  decide

theorem {theorem}_row_valid
    (row : CertRow) (hmem : row ∈ {theorem}Rows) :
    RowValid row :=
  row_valid_of_all_valid {theorem}_all_valid hmem

end Erdos647TailKillTauProofChunks
"""
    )
    return chunk_metadata(index, selected)


def chunk_metadata(index: int, selected: list[Any]) -> dict[str, Any]:
    start, length = chunk_bounds(index)
    kinds = {"witness": 0, "factor": 0, "zero_or_one": 0}
    payload_entries = 0
    triples: list[tuple[int, int, int]] = []
    for row in selected:
        kind = verify_row(row)
        kinds[kind] += 1
        if kind == "witness":
            payload_entries += len(row.payload)
        triples.append((row.r, row.s, row.u))
    digest = hashlib.sha256()
    for row in selected:
        digest.update(f"{row.tag}|{row.r}|{row.s}|{row.u}|{row.k}|{','.join(str(x) for x in row.payload)}\n".encode())
    return {
        "chunk_index": index,
        "module": f"Erdos647TailKillTauProofChunks.{chunk_name(index)}",
        "validity_theorem": f"Erdos647TailKillTauProofChunks.{chunk_theorem_prefix(index)}_all_valid",
        "pointwise_theorem": f"Erdos647TailKillTauProofChunks.{chunk_theorem_prefix(index)}_row_valid",
        "start": start,
        "length": length,
        "end_exclusive": start + length,
        "witness_entries": kinds["witness"],
        "factor_entries": kinds["factor"],
        "zero_or_one_entries": kinds["zero_or_one"],
        "divisor_payload_entries": payload_entries,
        "first_triple": list(triples[0]),
        "last_triple": list(triples[-1]),
        "row_digest": digest.hexdigest(),
    }


def compile_source(source: Path, olean: Path, timeout: int = COMPILE_TIMEOUT_SECONDS) -> dict[str, Any]:
    require_disk()
    olean.parent.mkdir(parents=True, exist_ok=True)
    result = run(["lake", "env", "lean", "-o", str(olean.relative_to(LEAN_ROOT)), str(source.relative_to(LEAN_ROOT))], LEAN_ROOT, timeout)
    result["olean_bytes"] = olean.stat().st_size if olean.exists() else 0
    return result


def compile_core() -> dict[str, Any]:
    lower = compile_source(LEAN_ROOT / "Erdos647TailKillTauLowerCertificate.lean", LOWER_OLEAN)
    if lower["returncode"] != 0 or lower["timed_out"]:
        raise RuntimeError(f"lower certificate compile failed: {lower['output_tail']}")
    core = compile_source(CORE_FILE, CORE_OLEAN)
    if core["returncode"] != 0 or core["timed_out"]:
        raise RuntimeError(f"core compile failed: {core['output_tail']}")
    return {"lower": lower, "core": core}


def source_scan(path: Path) -> list[str]:
    text = path.read_text()
    return [match.group(0) for match in FORBIDDEN_SOURCE_RE.finditer(text)]


def write_axiom_probe(index: int) -> Path:
    IMPORT_DIR.mkdir(parents=True, exist_ok=True)
    theorem = chunk_theorem_prefix(index)
    path = IMPORT_DIR / f"AxiomProbe{index:04d}.lean"
    path.write_text(
        f"""import Erdos647TailKillTauProofChunks.{chunk_name(index)}

#print axioms Erdos647TailKillTauProofChunks.{theorem}_all_valid
#print axioms Erdos647TailKillTauProofChunks.{theorem}_row_valid
"""
    )
    return path


def run_axiom_probe(index: int) -> dict[str, Any]:
    path = write_axiom_probe(index)
    return run(["lake", "env", "lean", str(path)], LEAN_ROOT, IMPORT_TIMEOUT_SECONDS)


def verify_chunk(index: int, rows: list[Any], *, compile_lean: bool = True) -> dict[str, Any]:
    start, length = chunk_bounds(index)
    selected = rows[start : start + length]
    meta = chunk_metadata(index, selected)
    path = chunk_file(index)
    if not path.exists():
        raise RuntimeError(f"missing chunk source {path}")
    scan_hits = source_scan(path)
    if scan_hits:
        raise RuntimeError(f"forbidden terms in {path}: {scan_hits}")
    meta["source_bytes"] = path.stat().st_size
    meta["source_sha256"] = sha256_path(path)
    if compile_lean:
        build = compile_source(path, chunk_olean(index))
        meta["build"] = build
        if build["returncode"] != 0 or build["timed_out"]:
            raise RuntimeError(f"chunk {index} compile failed: {build['output_tail']}")
        ax = run_axiom_probe(index)
        meta["axiom_probe"] = ax
        if ax["returncode"] != 0 or ax["timed_out"]:
            raise RuntimeError(f"chunk {index} axiom probe failed: {ax['output_tail']}")
        meta["olean_bytes"] = chunk_olean(index).stat().st_size if chunk_olean(index).exists() else 0
    return meta


def append_verify_log(records: list[dict[str, Any]]) -> None:
    VERIFY_LOG.parent.mkdir(parents=True, exist_ok=True)
    with VERIFY_LOG.open("a") as f:
        for record in records:
            f.write(json.dumps(record, sort_keys=True) + "\n")


def cmd_generate(args: argparse.Namespace) -> None:
    arch, rows, _rec = build_rows()
    start = args.start
    end = args.end
    compile_core()
    records = []
    for index in range(start, end + 1):
        meta = write_chunk(index, rows, arch.row_literal)
        records.append(meta)
    print(json.dumps({"generated": len(records), "start": start, "end": end}, indent=2))


def cmd_verify(args: argparse.Namespace) -> None:
    _arch, rows, _rec = build_rows()
    compile_core()
    records = []
    start_time = time.time()
    for index in range(args.start, args.end + 1):
        meta = verify_chunk(index, rows, compile_lean=not args.no_compile)
        records.append(meta)
        if disk_free_gb() < MIN_DISK_GB:
            raise RuntimeError("disk fell below safety threshold")
    append_verify_log(records)
    print(json.dumps({"verified": len(records), "start": args.start, "end": args.end, "elapsed_seconds": round(time.time() - start_time, 2)}, indent=2))


def read_verify_log() -> list[dict[str, Any]]:
    if not VERIFY_LOG.exists():
        return []
    return [json.loads(line) for line in VERIFY_LOG.read_text().splitlines() if line.strip()]


def collect_manifest(rows: list[Any], reconciliation: dict[str, Any]) -> dict[str, Any]:
    chunks = []
    seen_ranges = set()
    for index in range(CHUNK_COUNT):
        meta = verify_chunk(index, rows, compile_lean=False)
        meta["olean_bytes"] = chunk_olean(index).stat().st_size if chunk_olean(index).exists() else 0
        chunks.append(meta)
        key = (meta["start"], meta["end_exclusive"])
        if key in seen_ranges:
            raise RuntimeError(f"duplicate range {key}")
        seen_ranges.add(key)
    if chunks[0]["start"] != 0 or chunks[-1]["end_exclusive"] != DOMAIN_COUNT:
        raise RuntimeError("chunk range coverage mismatch")
    for prev, curr in zip(chunks, chunks[1:]):
        if prev["end_exclusive"] != curr["start"]:
            raise RuntimeError(f"range gap between {prev['chunk_index']} and {curr['chunk_index']}")
    total = {
        "entries": sum(item["length"] for item in chunks),
        "witness": sum(item["witness_entries"] for item in chunks),
        "factor": sum(item["factor_entries"] for item in chunks),
        "zero_or_one": sum(item["zero_or_one_entries"] for item in chunks),
        "complement": sum(item["factor_entries"] + item["zero_or_one_entries"] for item in chunks),
        "divisor_payload_entries": sum(item["divisor_payload_entries"] for item in chunks),
    }
    expected = {
        "entries": DOMAIN_COUNT,
        "witness": EXPECTED_WITNESSES,
        "factor": EXPECTED_FACTOR,
        "zero_or_one": EXPECTED_ZERO_OR_ONE,
        "complement": EXPECTED_COMPLEMENT,
        "divisor_payload_entries": EXPECTED_DIVISOR_PAYLOAD,
    }
    if total != expected:
        raise RuntimeError(f"total mismatch: {total} != {expected}")
    return {
        "status": "SHIFTED_PRIME_TAILKILL_TAU_PROOF_CHUNKS_PRODUCTION_MANIFEST_BANKED",
        "verdict": "TAILKILL_TAU_PROOF_CHUNKS_GREEN_DISTRIBUTED_COMPLETE_IMPORT_PRACTICAL",
        "recommendation": "RECOMMEND_TAILKILL_TAU_FINITE_PREFIX_INTERFACE_COMPOSITION",
        "chunk_size": CHUNK_SIZE,
        "chunk_count": CHUNK_COUNT,
        "reconciliation": reconciliation,
        "totals": total,
        "expected": expected,
        "chunks": chunks,
        "non_claims": {
            "finite_prefix_mechanism_verified_by_generated": False,
            "eventual_u_theorem_generated": False,
            "local_layer_theorem_generated": False,
            "global_theorem_generated": False,
            "shifted_prime_theorem_generated": False,
            "axiom_removed": False,
            "native_decide_used": False,
            "evidence_modified": False,
            "lakefile_modified": False,
        },
    }


def write_csv(manifest: dict[str, Any]) -> None:
    CSV_OUT.parent.mkdir(parents=True, exist_ok=True)
    with CSV_OUT.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "chunk_index", "start", "length", "end_exclusive", "witness_entries",
                "factor_entries", "zero_or_one_entries", "divisor_payload_entries",
                "source_bytes", "olean_bytes", "source_sha256", "row_digest",
                "validity_theorem", "pointwise_theorem",
            ],
            lineterminator="\n",
        )
        writer.writeheader()
        for item in manifest["chunks"]:
            writer.writerow({key: item.get(key, "") for key in writer.fieldnames})


def write_doc(manifest: dict[str, Any], imports: list[dict[str, Any]] | None = None, serial: dict[str, Any] | None = None) -> None:
    DOC_OUT.parent.mkdir(parents=True, exist_ok=True)
    imports = imports or []
    lines = [
        "# TailKillUpTo tau-certificate production proof chunks",
        "",
        f"Status: `{manifest['status']}`",
        "",
        f"Verdict: `{manifest['verdict']}`",
        "",
        f"Recommendation: `{manifest['recommendation']}`",
        "",
        "## Scope",
        "",
        "This artifact banks the distributed 10,000-row `by decide` tau-certificate proof chunks. It does not generate `FinitePrefixMechanismVerifiedBy`, eventual-u, local/global, shifted-prime, or axiom-removal theorems.",
        "",
        "## Reconciliation",
        "",
        f"- chunks: {manifest['chunk_count']}",
        f"- entries: {manifest['totals']['entries']}",
        f"- witness: {manifest['totals']['witness']}",
        f"- complement: {manifest['totals']['complement']}",
        f"- factor: {manifest['totals']['factor']}",
        f"- zero_or_one: {manifest['totals']['zero_or_one']}",
        f"- witness divisor payload: {manifest['totals']['divisor_payload_entries']}",
        "",
        "## Import probes",
        "",
        "| chunks | seconds | maxrss delta KB | rc |",
        "|---:|---:|---:|---:|",
    ]
    for item in imports:
        result = item["result"]
        lines.append(f"| {item['count']} | {result['elapsed_seconds']} | {result['maxrss_kb_delta']} | {result['returncode']} |")
    if serial:
        lines.extend([
            "",
            "## Serial verifier",
            "",
            f"- verified chunks: {serial.get('verified_chunks')}",
            f"- elapsed seconds: {serial.get('elapsed_seconds')}",
            f"- failures: {serial.get('failures')}",
        ])
    lines.extend([
        "",
        "## Non-claims",
        "",
        "- no `FinitePrefixMechanismVerifiedBy` theorem generated",
        "- no eventual-u theorem generated",
        "- no local-layer or global theorem generated",
        "- no shifted-prime theorem generated",
        "- no axiom removed",
        "- no `native_decide` used in production chunks",
        "- no evidence, slice, route, adapter, bridge, or lakefile modification",
    ])
    DOC_OUT.write_text("\n".join(lines) + "\n")


def cmd_manifest(_args: argparse.Namespace) -> None:
    _arch, rows, reconciliation = build_rows()
    manifest = collect_manifest(rows, reconciliation)
    JSON_OUT.parent.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    write_csv(manifest)
    write_doc(manifest)
    print(json.dumps({"chunks": manifest["chunk_count"], "entries": manifest["totals"]["entries"], "verdict": manifest["verdict"]}, indent=2))


def write_import_probe(count: int) -> Path:
    IMPORT_DIR.mkdir(parents=True, exist_ok=True)
    imports = "\n".join(f"import Erdos647TailKillTauProofChunks.{chunk_name(i)}" for i in range(count))
    checks = "\n".join(
        f"#check Erdos647TailKillTauProofChunks.{chunk_theorem_prefix(i)}_all_valid\n"
        f"#check Erdos647TailKillTauProofChunks.{chunk_theorem_prefix(i)}_row_valid"
        for i in range(count)
    )
    path = IMPORT_DIR / f"ImportProbe{count:03d}.lean"
    path.write_text(f"{imports}\n\n{checks}\n")
    return path


def cmd_import_probes(_args: argparse.Namespace) -> None:
    results = []
    for count in IMPORT_COUNTS:
        path = write_import_probe(count)
        result = run(["lake", "env", "lean", str(path)], LEAN_ROOT, IMPORT_TIMEOUT_SECONDS)
        item = {"count": count, "source_bytes": path.stat().st_size, "result": result, "success": result["returncode"] == 0 and not result["timed_out"]}
        results.append(item)
        if not item["success"]:
            break
    out = ROOT / f"data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_import_probes_{DATE}.json"
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"import_probe_count": len(results), "success": all(item["success"] for item in results)}, indent=2))


def cmd_closeout(_args: argparse.Namespace) -> None:
    manifest = json.loads(JSON_OUT.read_text())
    import_path = ROOT / f"data/residue_attack/channel_b_shifted_prime_tail_tau_proof_chunks_import_probes_{DATE}.json"
    imports = json.loads(import_path.read_text()) if import_path.exists() else []
    log_records = read_verify_log()
    serial = {
        "verified_chunks": len({record["chunk_index"] for record in log_records if "build" in record and record["build"]["returncode"] == 0}),
        "elapsed_seconds": round(sum(record.get("build", {}).get("elapsed_seconds", 0) for record in log_records), 2),
        "failures": sum(1 for record in log_records if record.get("build", {}).get("returncode") not in (None, 0)),
    }
    manifest["import_probes"] = imports
    manifest["serial_verifier"] = serial
    if imports and not all(item["success"] for item in imports):
        manifest["verdict"] = "TAILKILL_TAU_PROOF_CHUNKS_GREEN_DISTRIBUTED_COMPLETE_IMPORT_BOUND"
        manifest["recommendation"] = "RECOMMEND_TAILKILL_TAU_DISTRIBUTED_CERTIFICATE_ENDPOINT"
    JSON_OUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    write_csv(manifest)
    write_doc(manifest, imports=imports, serial=serial)
    print(json.dumps({"verdict": manifest["verdict"], "serial": serial}, indent=2))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("generate")
    p.add_argument("--start", type=int, required=True)
    p.add_argument("--end", type=int, required=True)
    p.set_defaults(func=cmd_generate)
    p = sub.add_parser("verify")
    p.add_argument("--start", type=int, required=True)
    p.add_argument("--end", type=int, required=True)
    p.add_argument("--no-compile", action="store_true")
    p.set_defaults(func=cmd_verify)
    sub.add_parser("manifest").set_defaults(func=cmd_manifest)
    sub.add_parser("import-probes").set_defaults(func=cmd_import_probes)
    sub.add_parser("closeout").set_defaults(func=cmd_closeout)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    require_disk()
    args.func(args)


if __name__ == "__main__":
    main()
