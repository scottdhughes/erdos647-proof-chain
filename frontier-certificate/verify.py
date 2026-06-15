#!/usr/bin/env python3
"""
Independent verifier for the Erdős #647 finite-range cover certificate.

Re-checks the certificate — SHA-256 integrity, the residue/sub-AP partition, the
aggregates, the u=0 row, the closure expansion, and an independent re-factoring
of the adversarial and sampled cells — using ONLY the Python standard library
(no numpy / sympy / gmpy2 / PARI), so a skeptic can run `python3 verify.py` on
any laptop. It does NOT re-run the full 1.514e11-cell sweep (that is the GPU scan
in scripts/); it confirms those per-record histograms are internally consistent
and correct on every cell it re-factors from scratch.

It re-derives the aggregates from the raw per-sub-AP records, independently
re-factors the adversarial cells with a self-contained Miller-Rabin +
Pollard-rho factorizer (a code path entirely separate from the GPU sieve that
produced the certificate), and re-checks the 631 Lean congruence closures'
arithmetic from first principles.

Exit code 0 iff every check passes; nonzero otherwise.

Usage:
    python3 verify.py                 # default: thorough, ~1-2 min
    python3 verify.py --full          # re-factor every sampled cell (slower)
    python3 verify.py --adv-thresh 12 # full first-kill chains for max_required_k>=12
    python3 verify.py --sample 500    # random ordinary records to spot-check
    python3 verify.py --seed 1
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

# ---- expected constants (independently asserted, not read from the data) ----
A_EXPECT          = 61_573_632_120          # 2520 * 46189 * 529
M_BASE            = 46_189                   # 11*13*17*19
SUBAP_MOD         = 529                      # 23^2
TWENTY_FIVE_TWENTY = 2520                    # 2^3*3^2*5*7
U_BOUND           = 10_000_000
SMALL_PRIME_BOUND = 784_688_718
N_OPEN_RESIDUES   = 41
TOTAL_PAIRS       = N_OPEN_RESIDUES * SUBAP_MOD   # 21689
EXPECTED_RESIDUES = {0,858,1287,1716,2431,2574,4862,5291,6149,8151,9009,9867,
    10582,12155,12584,13013,13442,16302,17017,17160,18733,19877,20306,20735,
    21164,24310,24453,25168,27170,28028,28457,29315,29601,31603,32032,32461,
    35321,36608,37752,38896,44187}
EXPECTED_MAXK_HIST = {1:861,5:770,7:27,8:1179,9:5656,10:5389,11:772,12:401,
                      13:56,14:23,15:5,16:1}

# --------------------------- number theory ---------------------------------
def is_prime(n: int) -> bool:
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    # deterministic for n < 3.3e24
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x == 1 or x == n-1: continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def _pollard(n: int) -> int:
    if n % 2 == 0: return 2
    while True:
        c = random.randrange(1, n)
        x = y = random.randrange(2, n); d = 1
        f = lambda v: (v*v + c) % n
        while d == 1:
            x = f(x); y = f(f(y))
            d = gcd(abs(x-y), n)
        if d != n: return d

def gcd(a,b):
    while b: a,b = b, a%b
    return a

def factorize(n: int) -> dict:
    """Full prime factorization as {prime: exponent}."""
    fac = {}
    if n <= 1: return fac
    # small trial division
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        while n % p == 0:
            fac[p] = fac.get(p,0)+1; n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1: continue
        if is_prime(m):
            fac[m] = fac.get(m,0)+1; continue
        d = _pollard(m)
        stack.append(d); stack.append(m//d)
    return fac

def tau_from_fac(fac: dict) -> int:
    t = 1
    for e in fac.values(): t *= (e+1)
    return t

def tau(n: int) -> int:
    return tau_from_fac(factorize(n))

def min_tau_d_times_prime(d: int) -> int:
    """min over primes p of tau(d*p)."""
    fac = factorize(d); base = tau_from_fac(fac)
    best = 2*base                       # p not dividing d
    for q,e in fac.items():
        best = min(best, base//(e+1)*(e+2))  # p = q (increment its exponent)
    return best

# ------------------------------ harness ------------------------------------
PASS, FAIL = [], []
def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  — {detail}" if detail else ""))
    return ok

def load_json(path):
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as fh: return json.load(fh)

def find(path_noext):
    for ext in (".json", ".json.gz"):
        p = os.path.join(DATA, path_noext + ext)
        if os.path.exists(p): return p
    raise FileNotFoundError(path_noext)

# --------------------------------- main ------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--adv-thresh", type=int, default=13)
    ap.add_argument("--sample", type=int, default=300)
    ap.add_argument("--rescan", type=int, default=5000,
                    help="re-scan this many u in each of 3 sub-APs from scratch")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    random.seed(args.seed)

    print("="*72)
    print("Erdős #647 finite-range cover certificate — independent verifier")
    print("="*72)

    # ---- 0. integrity: every file matches SHA256SUMS ----
    print("\n[0] Integrity (SHA-256 of every shipped file)")
    sums = os.path.join(HERE, "SHA256SUMS")
    sha_bad = []
    if os.path.exists(sums):
        listed = set()
        for line in open(sums):
            line = line.strip()
            if not line: continue
            want, rel = line.split(None, 1)
            if rel == "SHA256SUMS": continue
            listed.add(rel)
            p = os.path.join(HERE, rel)
            if not os.path.exists(p): sha_bad.append(f"{rel}: missing"); continue
            h = hashlib.sha256(open(p, "rb").read()).hexdigest()
            if h != want: sha_bad.append(f"{rel}: hash mismatch")
        check("all files match SHA256SUMS", not sha_bad, str(sha_bad[:4]))
        # self-authentication: the manifest must list every shipped file
        present = set()
        for dp, dn, fn in os.walk(HERE):
            dn[:] = [d for d in dn if d != "__pycache__"]
            for f in fn:
                rel = os.path.relpath(os.path.join(dp, f), HERE)
                if rel in ("SHA256SUMS",) or rel.endswith(".pyc"): continue
                present.add(rel)
        check("SHA256SUMS lists every shipped file (no truncation)",
              present == listed, f"unlisted={sorted(present-listed)[:4]} extra={sorted(listed-present)[:4]}")
    else:
        check("SHA256SUMS present", False, "manifest missing")

    cert = load_json(find("cover_certificate_U1e7_Kmax16"))
    manifest = load_json(find("open_subap_manifest"))
    closures = load_json(find("closures_params"))
    P = cert["parameters"]; A = P["A_CONST"]
    recs = cert["results"]

    # ---- 1. constants & exactness invariant ----
    print("\n[1] Constants and exactness invariant")
    check("A = 2520*46189*529 = 61573632120",
          A == A_EXPECT == TWENTY_FIVE_TWENTY*M_BASE*SUBAP_MOD)
    check("A factorization = 2^3*3^2*5*7*11*13*17*19*23^2",
          factorize(A) == {2:3,3:2,5:1,7:1,11:1,13:1,17:1,19:1,23:2})
    check("M_BASE = 11*13*17*19", M_BASE == 11*13*17*19 and P["M_BASE"]==M_BASE)
    check("SUBAP_MOD = 23^2", SUBAP_MOD == 23*23 and P["SUBAP_MOD"]==SUBAP_MOD)
    Bsp = P["SMALL_PRIME_BOUND"]
    maxcand = A*P["U_BOUND"] + max(r["B"] for r in recs)   # > every scanned F_k(u)
    check("exactness: SMALL_PRIME_BOUND^2 > A*U_BOUND + max(B_sub) >= every F_k(u)",
          Bsp*Bsp > maxcand, f"B^2 - (A*U+maxB) = {Bsp*Bsp-maxcand}")
    check("every record has U = U_BOUND (the height bound applies uniformly)",
          all(r["U"] == P["U_BOUND"] for r in recs),
          f"{sum(1 for r in recs if r['U']!=P['U_BOUND'])} off")
    check("K_COVER = 1..16", P["K_COVER"] == list(range(1,17)))

    # ---- 2. partition ----
    print("\n[2] Partition of the 41-residue frontier")
    scanned = {(r["r"], r["s_class"]) for r in recs}
    check("scanned distinct (r,s_class) = 15140", len(scanned)==15140, str(len(scanned)))
    rs = {r["r"] for r in recs}
    check("distinct residues = 41 and equal the Lean open set",
          rs == EXPECTED_RESIDUES, f"|rs|={len(rs)}")
    closed = {(c["r"], c["s_mod_529"]) for c in manifest["closed_pairs"]}
    openm  = {(c["r"], c["s_mod_529"]) for c in manifest["open_pairs"]}
    check("closed_pairs = 6549", len(closed)==6549, str(len(closed)))
    universe = {(r, s) for r in EXPECTED_RESIDUES for s in range(SUBAP_MOD)}
    check("closed ∪ open = the full universe (41 residues × 529 sub-APs)",
          (closed | openm) == universe and len(universe)==TOTAL_PAIRS,
          f"missing={sorted(universe-(closed|openm))[:3]} extra={sorted((closed|openm)-universe)[:3]}")
    check("closed ∩ open = ∅", len(closed & openm)==0)
    check("all sub-AP indices in range 0..528",
          all(0 <= s < SUBAP_MOD for _,s in (closed|openm)))
    check("manifest open set == GPU-scanned set", openm==scanned)

    # parametrization (the no-gap fact): B_sub = 2520*(M*s+r), and 0 <= B_sub < A
    bad_par = [(r["r"],r["s_class"]) for r in recs
               if r["B"] != TWENTY_FIVE_TWENTY*(M_BASE*r["s_class"] + r["r"])]
    check("parametrization B_sub = 2520*(M*s + r) on all 15140 records",
          not bad_par, f"{len(bad_par)} mismatches")
    maxB = max(r["B"] for r in recs)
    check("0 <= B_sub < A on all records (every n < A*1e7 has u < 1e7)",
          0 <= min(r["B"] for r in recs) and maxB < A, f"max B_sub={maxB}, A={A}")

    # ---- 3. aggregates re-derived from raw records ----
    print("\n[3] Aggregates re-derived from the raw 15140 records")
    tot_surv = sum(r["survivor_count"] for r in recs)
    check("total survivors = 0", tot_surv==0, str(tot_surv))
    none_off = [r for r in recs if r["by_k"].get("none",0)!=0]
    check("every record by_k['none'] == 0", not none_off, f"{len(none_off)} offenders")
    bad_bk = [(_r["r"],_r["s_class"]) for _r in recs
              if sum(int(v) for k,v in _r["by_k"].items() if k!="none") + _r["by_k"].get("none",0) != _r["U"]]
    check("per record: sum(by_k)=U=1e7 (every u accounted for)", not bad_bk, f"{len(bad_bk)} bad")
    cells = sum(r["U"] for r in recs)
    check("total cells = 151,400,000,000", cells==151_400_000_000, f"{cells:,}")
    hist = {}
    for r in recs: hist[r["max_required_k"]] = hist.get(r["max_required_k"],0)+1
    check("by_max_required_k histogram matches", hist==EXPECTED_MAXK_HIST, json.dumps(hist,sort_keys=True))
    check("cover tight: max(max_required_k)=16 attained exactly once",
          max(hist)==16 and hist[16]==1)

    # ---- 4. independent re-factoring of cells ----
    print("\n[4] Independent re-factoring of cells (Miller-Rabin + Pollard-rho)")
    adv = [r for r in recs if r["max_required_k"] >= args.adv_thresh]
    print(f"    full first-kill chains for {len(adv)} records "
          f"(max_required_k >= {args.adv_thresh})")
    chain_fail = []
    for r in adv:
        B = r["B"]; mk = r["max_required_k"]
        # pick a u whose first kill is mk
        bucket = r["high_k_samples"].get(str(mk)) or []
        if not bucket: chain_fail.append((r["r"],r["s_class"],"no sample")); continue
        u = bucket[0]["u"]
        for k in range(1, mk):
            if tau(A*u + B - k) > k+2:
                chain_fail.append((r["r"],r["s_class"],f"early kill k={k}")); break
        else:
            t = tau(A*u + B - mk)
            if not (t > mk+2 and t == bucket[0]["tau"]):
                chain_fail.append((r["r"],r["s_class"],f"k={mk} tau={t} stored={bucket[0]['tau']}"))
    check(f"adversarial first-kill chains exact ({len(adv)} cells)", not chain_fail,
          str(chain_fail[:5]))

    # tau-check sampled high_k cells in adversarial + random ordinary records
    pool = adv + random.sample(recs, min(args.sample, len(recs)))
    if args.full: pool = recs
    n_checked = 0; samp_fail = []
    for r in pool:
        B = r["B"]
        for kb, lst in r["high_k_samples"].items():
            k = int(kb)
            for e in lst:
                n_checked += 1
                t = tau(A*e["u"] + B - k)
                if t != e["tau"] or not (t > k+2):
                    samp_fail.append((r["r"],r["s_class"],kb,e["u"],t,e["tau"]))
    check(f"sampled high-k cells: stored tau exact and kill real ({n_checked} cells)",
          not samp_fail, str(samp_fail[:5]))

    # the u=0 row (the GPU scan covers u=1..1e7; u=0 is certified here directly)
    u0_miss = []; u0_layerA = 0
    for r in recs:
        B = r["B"]
        if B <= 84: u0_layerA += 1; continue        # n <= 84 -> Layer A
        if not any(tau(B - k) > k+2 for k in range(1, 17)):
            u0_miss.append((r["r"], r["s_class"], B))
    check(f"u=0 row covered for all 15140 open sub-APs ({u0_layerA} noncandidate or Layer A)",
          not u0_miss, str(u0_miss[:5]))

    # contiguous re-scan from scratch (anti-fabrication: independently regenerate
    # 'no survivor' on full u-blocks of a few sub-APs, not just sampled cells)
    rescan_recs = random.sample(recs, 3)
    rescan_fail = []
    for r in rescan_recs:
        B = r["B"]
        for u in range(1, args.rescan + 1):
            if not any(tau(A*u + B - k) > k+2 for k in range(1, 17)):
                rescan_fail.append((r["r"], r["s_class"], u)); break
    check(f"contiguous re-scan u=1..{args.rescan} of 3 sub-APs: 0 survivors",
          not rescan_fail, str(rescan_fail[:5]))

    # ---- 5. the 631 Lean congruence closures, re-checked from scratch ----
    print("\n[5] Re-checking the 631 Lean closures (universal-in-s kills)")
    cl_fail = []
    for c in closures:
        k,d,Ac,b,al,c0 = c["k"],c["d"],c["A"],c["b"],c["alpha"],c["c0"]
        sm,sc,rr = c["s_mod"], c["s_class"], c["r"]
        ok = (TWENTY_FIVE_TWENTY*Ac == d*al                 # identity, x-coeff
              and TWENTY_FIVE_TWENTY*b - k == d*c0          # identity, const term
              and c0 >= 2
              and min_tau_d_times_prime(d) > k+2            # forced over-budget
              and c["tau_bound_N"] >= k+2
              and sm in (23, SUBAP_MOD)                     # structural: valid sub-AP modulus
              and 0 <= sc < sm                              # valid class
              and rr in EXPECTED_RESIDUES                   # closes an actual open residue
              and Ac == M_BASE*sm                           # the form's A' = M*s_mod
              and b == M_BASE*sc + rr)                      # the form's b = M*s_class + r
        if not ok: cl_fail.append(c["name"])
    check(f"all closures: identity + structure + c0>=2 + min_p tau(d*p)>k+2 ({len(closures)})",
          len(closures)==631 and not cl_fail, str(cl_fail[:5]))

    # derive the 6549 closed pairs FROM closures_params and match the manifest
    # (ties the two data files together — neither can drift unnoticed)
    derived = set()
    for c in closures:
        if c["s_mod"] == 529: derived.add((c["r"], c["s_class"]))
        elif c["s_mod"] == 23:
            derived.update((c["r"], s) for s in range(SUBAP_MOD) if s % 23 == c["s_class"])
    check("closures_params expands to exactly the manifest's 6549 closed pairs",
          derived == closed, f"|derived|={len(derived)}, sym_diff={len(derived ^ closed)}")

    # ---- verdict ----
    print("\n" + "="*72)
    print(f"RESULT: {len(PASS)} passed, {len(FAIL)} failed")
    if FAIL:
        print("FAILED:", ", ".join(FAIL)); print("="*72); sys.exit(1)
    print("ALL CHECKS PASSED — certificate independently verified.")
    print(f"No #647 solution with 24 < n <= {A*P['U_BOUND']:,} = A_CONST*1e7"
          " (~6.157e17).")
    print("="*72)

if __name__ == "__main__":
    main()
