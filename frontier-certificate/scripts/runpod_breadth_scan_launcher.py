#!/usr/bin/env python3
"""
RunPod multi-GPU launcher for the AP-sieve breadth scan.

This is the orchestration layer above `cover_certificate_breadth_scan_gpu_sieve.py`.

Modes:
  shard      Run one shard locally on a single GPU. Reads SHARD_INDEX,
             SHARD_COUNT env vars; uses CUDA_VISIBLE_DEVICES to pin to
             one GPU; passes a SUBAP_FILTER covering this shard's
             slice of the manifest.  Each shard writes to its OWN
             OUT_DIR (sub-directory) to avoid race conditions on the
             natural sieve output filename.
  merge      Combine N shard JSONs into one full-frontier JSON matching
             the CPU schema. Verifies manifest hash, no duplicate
             (r, s_class), full coverage of manifest open pairs.
  multigpu   Launch N shard processes in parallel on the local node,
             one per GPU device, then merge results.

Shard slicing:
  Sub-APs are sorted (r, s_class) ascending in the manifest.  Shard i
  of N gets every Nth sub-AP starting from offset i.  Stride slicing
  gives disjoint, exhaustive coverage by construction.

Hardening notes:
  - BLOCKER (race): each shard gets a private per-shard sub-directory
    under OUT_DIR; sieve writes its natural filename there with no
    cross-shard collision.
  - HARDENING: SUB_AP_LIMIT env popped before child sieve launch.
  - HARDENING: manifest_hash recorded in shard output and verified
    across shards in merge.
  - HARDENING: shard_count > n_gpus rejected (multigpu) and
    shard_count <= 0 rejected everywhere.
  - HARDENING: canonical K_COVER suffix shared with the sieve.
  - HARDENING: merged JSON includes elapsed_seconds and provenance.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DATA_DIR = REPO / 'data' / 'residue_attack'

SIEVE_DEFAULT_K_COVER = (1, 2, 3, 4, 5, 6, 7, 8)


def _canonical_k_cover(k_cover_str: str) -> tuple:
    """Mirror the sieve's `_parse_k_cover`: split, dedup, sort. Empty -> default."""
    if not k_cover_str:
        return SIEVE_DEFAULT_K_COVER
    parts = [x.strip() for x in k_cover_str.split(',') if x.strip()]
    return tuple(sorted({int(x) for x in parts}))


def _suffix_for(u_bound: int, k_cover_str: str) -> str:
    """Mirror the sieve's output filename suffix logic exactly."""
    canon = _canonical_k_cover(k_cover_str)
    suffix = f'_U{u_bound}'
    if list(canon) != [1, 2, 3, 4, 5, 6, 7, 8]:
        suffix += f'_Kmax{max(canon)}'
    return suffix


def _manifest_hash(manifest_path: Path) -> str:
    """Stable hash of the manifest's open_pairs list, used to detect
    cross-shard manifest drift."""
    m = json.loads(manifest_path.read_text())
    pairs = sorted([(int(p['r']), int(p['s_mod_529'])) for p in m['open_pairs']])
    h = hashlib.sha256()
    for r, s in pairs:
        h.update(f'{r},{s}\n'.encode())
    return h.hexdigest()[:16]


def _shard_subap_filter(manifest_path: Path, shard_index: int, shard_count: int) -> tuple[str, int]:
    """Produce a SUBAP_FILTER string covering shard `shard_index` of
    `shard_count`. Returns (filter_string, n_subaps_in_shard).
    Stride-based slicing for load balance.  Disjoint + exhaustive by
    construction (pairs[i::N] partitions for i in [0, N))."""
    if not manifest_path.exists():
        raise SystemExit(f'manifest not found: {manifest_path}')
    if shard_count <= 0:
        raise SystemExit(f'SHARD_COUNT must be positive, got {shard_count}')
    if shard_index < 0 or shard_index >= shard_count:
        raise SystemExit(
            f'SHARD_INDEX={shard_index} out of range [0, {shard_count})')
    manifest = json.loads(manifest_path.read_text())
    pairs = sorted([(int(p['r']), int(p['s_mod_529']))
                    for p in manifest['open_pairs']])
    if len(set(pairs)) != len(pairs):
        raise SystemExit('manifest open_pairs has duplicates')
    selected = pairs[shard_index::shard_count]
    if not selected:
        raise SystemExit(f'shard {shard_index}/{shard_count} got 0 sub-APs')
    return ';'.join(f'{r},{s}' for (r, s) in selected), len(selected)


def cmd_shard(args):
    """Run one shard. Reads SHARD_INDEX, SHARD_COUNT, GPU_ID from env.
    Each shard writes to a private per-shard sub-directory under OUT_DIR
    to avoid race conditions on the sieve's natural output filename."""
    shard_index = int(os.environ.get('SHARD_INDEX', '0'))
    shard_count = int(os.environ.get('SHARD_COUNT', '1'))
    if shard_count <= 0:
        raise SystemExit(f'SHARD_COUNT must be positive, got {shard_count}')
    gpu_id = os.environ.get('GPU_ID', '0')

    manifest_path = Path(os.environ.get(
        'MANIFEST_PATH', str(DATA_DIR / 'open_subap_manifest.json'))).resolve()
    shared_out_dir = Path(os.environ.get('OUT_DIR', str(DATA_DIR))).resolve()
    shard_out_dir = (shared_out_dir / f'shard{shard_index}of{shard_count}').resolve()
    shard_out_dir.mkdir(parents=True, exist_ok=True)

    subap_filter, n_subaps_in_shard = _shard_subap_filter(
        manifest_path, shard_index, shard_count)
    manifest_hash = _manifest_hash(manifest_path)

 # Linux env-var size limit (combined argv+env) is typically ~128KB.
 # For full-manifest shards (shard_count=1) at 15140 pairs the
 # SUBAP_FILTER alone exceeds this. Production sharding (8 shards →
 # ~26KB each) fits comfortably. When the filter would be too long,
 # fall back to writing it to a sidecar file consumed via SUBAP_FILTER_FILE.
    SUBAP_FILTER_LIMIT = 100_000 # leave headroom under the 128KB cap
    if len(subap_filter) > SUBAP_FILTER_LIMIT:
 # Future fallback: SUBAP_FILTER_FILE sidecar; currently aborts.
 # The sieve script does not yet read SUBAP_FILTER_FILE, so for now
 # we hard-fail with a clear message — better than silent truncation.
        raise SystemExit(
            f'SUBAP_FILTER for shard {shard_index}/{shard_count} would be '
            f'{len(subap_filter):,} bytes, over the {SUBAP_FILTER_LIMIT:,} '
            f'byte cap. Use a larger shard_count to keep each shard small.')
    env = os.environ.copy()
    env['CUDA_VISIBLE_DEVICES'] = gpu_id
    env['SUBAP_FILTER'] = subap_filter
    env['MANIFEST_PATH'] = str(manifest_path)
    env['OUT_DIR'] = str(shard_out_dir) # private per-shard dir
    env.pop('SUB_AP_LIMIT', None) # Hardening #2
    env.pop('SMALL_PRIME_BOUND', None) # Hardening

    sieve_script = REPO / 'scripts' / 'cover_certificate_breadth_scan_gpu_sieve.py'
    if not sieve_script.exists():
        raise SystemExit(f'sieve script not found: {sieve_script}')

    print(f'[shard {shard_index}/{shard_count}] GPU={gpu_id} '
          f'sub-APs={n_subaps_in_shard} U_BOUND={env.get("U_BOUND", "default")} '
          f'K_COVER={env.get("K_COVER", "default")} '
          f'manifest_hash={manifest_hash}', file=sys.stderr, flush=True)

    t0 = time.time()
 # Use the same interpreter the launcher itself runs as (so venv with
 # CuPy/sympy/etc. is preserved); falling back to system python3
 # would lose the venv.
    rc = subprocess.call(
        [sys.executable, str(sieve_script)], env=env, cwd=str(REPO))
    elapsed = time.time() - t0
    if rc != 0:
        raise SystemExit(f'[shard {shard_index}] sieve failed rc={rc}')

 # Locate the sieve's natural output and rename + move into shared OUT_DIR
    u_bound = int(env.get('U_BOUND', '50000'))
    k_cover_str = env.get('K_COVER', '')
    suffix = _suffix_for(u_bound, k_cover_str)
    natural = shard_out_dir / f'cover_certificate_breadth_scan_gpu_sieve{suffix}.json'
    target = shared_out_dir / (
        f'cover_certificate_breadth_scan_gpu_sieve_shard{shard_index}'
        f'of{shard_count}{suffix}.json')
    if not natural.exists():
        raise SystemExit(f'expected sieve output not found: {natural}')
 # Stamp manifest_hash into the shard output for cross-shard verification.
    d = json.loads(natural.read_text())
    d['_shard_index'] = shard_index
    d['_shard_count'] = shard_count
    d['_manifest_hash'] = manifest_hash
 # Atomic write: tmp then os.replace .
 # Use with_name() so the .json extension is preserved on the tmp file.
    tmp_target = target.with_name(f'{target.name}.tmp.{os.getpid()}')
    tmp_target.write_text(json.dumps(d, indent=2, default=str))
    os.replace(tmp_target, target)
    natural.unlink()
    try:
        shard_out_dir.rmdir() # only succeeds if empty
    except OSError:
        pass
    print(f'[shard {shard_index}/{shard_count}] done in {elapsed:.1f}s '
          f'-> {target.name}', file=sys.stderr)


def cmd_merge(args):
    """Merge N shard JSONs into a single full-frontier JSON."""
    shard_dir = Path(args.shard_dir)
    if args.shard_count <= 0:
        raise SystemExit(f'shard_count must be positive, got {args.shard_count}')
    suffix = _suffix_for(args.u_bound, args.k_cover)

    shard_files = []
    for i in range(args.shard_count):
        f = shard_dir / (
            f'cover_certificate_breadth_scan_gpu_sieve_shard{i}'
            f'of{args.shard_count}{suffix}.json')
        if not f.exists():
            raise SystemExit(f'missing shard: {f}')
        shard_files.append(f)

    print(f'merging {len(shard_files)} shards from {shard_dir}',
          file=sys.stderr)

    merged_results = []
    elapsed_per_shard = []
    parameters_seen = None
    manifest_summary_seen = None
    _UNSET = object()
    manifest_hash_seen = _UNSET
    provenance_per_shard = []
    for f in shard_files:
        d = json.loads(f.read_text())
        merged_results.extend(d['results'])
        elapsed_per_shard.append(d.get('elapsed_seconds', 0.0))
        provenance_per_shard.append(d.get('provenance', {}))
 # cross-shard manifest hash must agree (and must be present —
 # missing hash means a pre-fix shard file or upstream tamper).
        if '_manifest_hash' not in d:
            raise SystemExit(
                f'shard {f.name} is missing _manifest_hash; refusing to merge')
        h = d['_manifest_hash']
        if manifest_hash_seen is _UNSET:
            manifest_hash_seen = h
        elif h != manifest_hash_seen:
            raise SystemExit(
                f'manifest_hash mismatch across shards: '
                f'{manifest_hash_seen} vs {h} in {f.name}')
        if parameters_seen is None:
            parameters_seen = d.get('parameters', {})
        else:
            for k, v in d.get('parameters', {}).items():
                if k == 'SUB_AP_LIMIT':
                    continue
                if parameters_seen.get(k) != v:
                    raise SystemExit(
                        f'parameter mismatch across shards in {k}: '
                        f'{parameters_seen.get(k)} vs {v}')
        if manifest_summary_seen is None:
            manifest_summary_seen = d.get('manifest_summary', {})

 # Tail-pressure sort with deterministic tiebreak (matches sieve).
    merged_results.sort(key=lambda d: (
        d['survivor_count'],
        d['count_first_k_eq_8'],
        d['count_first_k_ge_6'],
        d['max_required_k'],
        -d['r'],
        -d['s_class'],
    ), reverse=True)

    total_u = len(merged_results) * args.u_bound
    total_survivors = sum(r['survivor_count'] for r in merged_results)
    n_zero = sum(1 for r in merged_results if r['survivor_count'] == 0)
    by_max_k = {}
    for rec in merged_results:
        by_max_k[rec['max_required_k']] = by_max_k.get(rec['max_required_k'], 0) + 1

 # Sanity: results count matches manifest open-pairs
    if manifest_summary_seen and 'n_open_pairs' in manifest_summary_seen:
        expected = manifest_summary_seen['n_open_pairs']
        if len(merged_results) != expected:
            raise SystemExit(
                f'merge count mismatch: {len(merged_results)} '
                f'records vs manifest n_open_pairs={expected}')

 # Sanity: no duplicate (r, s_class) and full coverage of manifest pairs.
 # Looks for the manifest in the shard_dir; if absent, warn and skip
 # the cross-check (the count + duplicate-key + manifest-hash checks
 # above already catch most issues, but the explicit pair-set check
 # is the strongest evidence).
    manifest_path = shard_dir / 'open_subap_manifest.json'
    if manifest_path.exists():
        m = json.loads(manifest_path.read_text())
        manifest_pairs = set(
            (int(p['r']), int(p['s_mod_529'])) for p in m['open_pairs'])
        results_pairs = set((rec['r'], rec['s_class']) for rec in merged_results)
        missing = manifest_pairs - results_pairs
        extra = results_pairs - manifest_pairs
        if missing:
            raise SystemExit(
                f'merged results missing {len(missing)} manifest pairs; '
                f'first 3: {sorted(missing)[:3]}')
        if extra:
            raise SystemExit(
                f'merged results contain {len(extra)} pairs not in manifest; '
                f'first 3: {sorted(extra)[:3]}')
    else:
        print(f'WARNING: manifest not found at {manifest_path}; '
              f'skipping coverage cross-check', file=sys.stderr)

    seen = set()
    for rec in merged_results:
        key = (rec['r'], rec['s_class'])
        if key in seen:
            raise SystemExit(f'duplicate (r,s_class) across shards: {key}')
        seen.add(key)

    out = {
        'date': time.strftime('%Y-%m-%d'),
        'task': f'K={args.k_cover or "[1..8]"} GPU AP-sieve breadth scan '
                f'(merged across {args.shard_count} shards)',
        'parameters': parameters_seen,
        'manifest_summary': manifest_summary_seen,
        'manifest_hash': manifest_hash_seen,
        'aggregate': {
            'n_sub_aps_scanned': len(merged_results),
            'total_u': total_u,
            'total_survivors': total_survivors,
            'overall_survivor_rate': total_survivors / total_u if total_u else 0,
            'n_sub_aps_zero_survivors': n_zero,
            'by_max_k': by_max_k,
        },
        'results': merged_results,
        'elapsed_seconds': max(elapsed_per_shard) if elapsed_per_shard else 0,
        'elapsed_seconds_per_shard': elapsed_per_shard,
        'provenance_per_shard': provenance_per_shard,
        'shard_count': args.shard_count,
    }
    out_path = shard_dir / (
        f'cover_certificate_breadth_scan_gpu_sieve_merged{suffix}.json')
    out_path.write_text(json.dumps(out, indent=2, default=str))
    print(f'merged -> {out_path.name}  '
          f'({len(merged_results)} sub-APs, {total_survivors} survivors, '
          f'{n_zero} zero-survivor, manifest_hash={manifest_hash_seen})',
          file=sys.stderr)


def cmd_multigpu(args):
    """Launch one shard process per available GPU and wait for all.
    By default shard_count = n_gpus; explicit --shard-count > n_gpus
    is rejected (use a queue-based launcher for that case)."""
    try:
        out = subprocess.check_output(
            ['nvidia-smi', '--query-gpu=index', '--format=csv,noheader'],
            text=True)
        gpu_indices = [line.strip() for line in out.strip().splitlines() if line.strip()]
    except Exception as e:
        raise SystemExit(f'could not detect GPUs via nvidia-smi: {e}')

    n_gpus = len(gpu_indices)
    if n_gpus == 0:
        raise SystemExit('no GPUs detected')
    print(f'detected {n_gpus} GPU(s): {gpu_indices}', file=sys.stderr)

 # Default to n_gpus if not specified; explicit 0 is rejected (not falsy fallback).
    shard_count = n_gpus if args.shard_count is None else args.shard_count
    if shard_count <= 0:
        raise SystemExit(f'shard_count must be positive, got {shard_count}')
    if shard_count > n_gpus:
        raise SystemExit(
            f'shard_count={shard_count} > n_gpus={n_gpus}; this launcher is '
            f'1-shard-per-GPU only.  Run shards sequentially or use a '
            f'queue-based launcher for over-subscription.')

    out_dir = Path(args.out_dir or str(DATA_DIR)).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
 # Always resolve manifest path: defaulting to DATA_DIR/manifest if not
 # provided. Blocker: leaving MANIFEST_PATH unset would let
 # the parent shell's MANIFEST_PATH leak into shards.
    manifest_path_resolved = (
        Path(args.manifest_path).resolve()
        if args.manifest_path
        else (DATA_DIR / 'open_subap_manifest.json').resolve())

    procs = []
    for i in range(shard_count):
        env = os.environ.copy()
        env['SHARD_INDEX'] = str(i)
        env['SHARD_COUNT'] = str(shard_count)
        env['GPU_ID'] = gpu_indices[i]
        env['U_BOUND'] = str(args.u_bound)
        env['K_COVER'] = args.k_cover
        env.pop('SUB_AP_LIMIT', None)
        env['MANIFEST_PATH'] = str(manifest_path_resolved) # always set
        env['OUT_DIR'] = str(out_dir)
        env.pop('SMALL_PRIME_BOUND', None) # let sieve compute the right bound
        log_path = out_dir / f'shard{i}of{shard_count}.log'
        log_fh = open(log_path, 'wb')
        cmd = [sys.executable,
               str(REPO / 'scripts' / 'runpod_breadth_scan_launcher.py'),
               'shard']
        print(f'[launch] shard {i}/{shard_count} on GPU {gpu_indices[i]}, '
              f'log -> {log_path.name}', file=sys.stderr)
        p = subprocess.Popen(cmd, env=env, stdout=log_fh, stderr=subprocess.STDOUT)
        procs.append((i, p, log_fh, log_path))

    failures = []
    for (i, p, log_fh, log_path) in procs:
        rc = p.wait()
        log_fh.close()
        if rc != 0:
            failures.append((i, rc, log_path))
            print(f'[FAIL] shard {i} rc={rc} (see {log_path})', file=sys.stderr)
        else:
            print(f'[done] shard {i}', file=sys.stderr)

    if failures:
        raise SystemExit(f'{len(failures)} shard(s) failed; merge skipped')

    print(f'all {shard_count} shards done; merging ...', file=sys.stderr)
    merge_args = argparse.Namespace(
        shard_dir=str(out_dir),
        u_bound=args.u_bound,
        shard_count=shard_count,
        k_cover=args.k_cover,
    )
    cmd_merge(merge_args)


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='cmd', required=True)

    p_shard = sub.add_parser('shard')
    p_shard.set_defaults(func=cmd_shard)

    p_merge = sub.add_parser('merge')
    p_merge.add_argument('--shard-dir', required=True)
    p_merge.add_argument('--u-bound', type=int, required=True)
    p_merge.add_argument('--shard-count', type=int, required=True)
    p_merge.add_argument('--k-cover', default='1,2,3,4,5,6,7,8')
    p_merge.set_defaults(func=cmd_merge)

    p_multi = sub.add_parser('multigpu')
    p_multi.add_argument('--u-bound', type=int, required=True)
    p_multi.add_argument('--k-cover', default='1,2,3,4,5,6,7,8,9,10,11,12')
    p_multi.add_argument('--shard-count', type=int, default=None,
                         help='default = nvidia-smi GPU count; > n_gpus rejected')
    p_multi.add_argument('--manifest-path', default=None)
    p_multi.add_argument('--out-dir', default=None)
    p_multi.set_defaults(func=cmd_multigpu)

    args = p.parse_args()
    args.func(args)


if __name__ == '__main__':
    main()
