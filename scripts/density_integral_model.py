#!/usr/bin/env python3
"""Density integral model for Erdős #647 case-A candidates.

This script fixes the pointwise-vs-cumulative conflation in the previous
density table. It separates two mathematically distinct objects:

  1. Pointwise omitted-pass probability p_r(t):
       P(τ(2520N - k) ≤ k+2 at every k ∈ [1,100] \\ base_enriched(r)
        | t sampled uniformly at scale t).

     Fitted from the scale-stability data as a decaying function of t.

  2. Expected cumulative case-A count E_r(X):
       E_r(X) ≈ ∫_2^X ρ_r(t) · p_r(t) dt,
     where ρ_r(t) = dN_{base,r}(t)/dt is the Bateman-Horn base-tuple
     hit-density at scale t.

The first is pointwise and may decay with t (and does). The second is
cumulative and must be non-decreasing in X.

Inputs:
  - data/scale_stability_test.json: per-B^eff pass rates at 3 t-scales
  - data/bh_per_residue_density.json: BH shape-density predictions
  - data/case_a_density_factored.json: raw-sample independence product

Outputs:
  - data/density_integral_model.json: both panels (pointwise + cumulative)
  - docs/density_integral_model.md: derivation and table
"""

import json
from math import log, exp
from pathlib import Path

REPO = Path(__file__).parent.parent


def fit_pointwise_probability(scale_stability_data, residue, base_product_at_85):
    """Fit p_r(t) from scale-stability data.

    Anchored at t = 10^8.5 with the directly-measured independence-product
    estimate (from case_a_density_factored.json), then extrapolated to other
    scales using the *ratio* of per-B rates between scales.

    Model: log p_r(t) = log p_r(10^8.5) + γ · (log10(t) - 8.5)
    where γ is computed from the scale-stability per-B rate drift.
    """
    scales = scale_stability_data["per_residue"][str(residue)]
    scale_names = list(scales.keys())

    def parse_logt(scale_name):
        parts = scale_name.split("-")
        lo = float(parts[0].split("^")[1])
        hi = float(parts[1].split("^")[1])
        return (lo + hi) / 2

    log_ts = [parse_logt(s) for s in scale_names]

    # Typical B-profile weight sums (from empirical k ∈ [1,100] \ ban).
    # Same as the indep-product it multiplies; but we only care about RATIOS
    # across scales, so we can use any consistent B-weight set.
    # Use r=0 profile as canonical:
    weights = {2: 10, 3: 7, 4: 12, 5: 10, 6: 5, 7: 8, 8: 7, 9: 6, 10: 5,
               11: 4, 12: 3, 13: 3}

    # For each scale, compute weighted-log-product (relative measure)
    log_wp = []
    for sn in scale_names:
        sd = scales[sn]
        lp = 0.0
        for B_str, info in sd.items():
            B = int(B_str)
            if B not in weights:
                continue
            if info["sample"] < 50:
                continue
            rate = info["rate"]
            if rate is None or rate <= 0:
                continue
            lp += weights[B] * log(rate)
        log_wp.append(lp)

    # Slope γ is (log_wp[last] - log_wp[0]) / (log_t[last] - log_t[0])
    # Use weighted least squares across all scale points.
    n = len(log_ts)
    sx = sum(log_ts)
    sy = sum(log_wp)
    sxx = sum(x*x for x in log_ts)
    sxy = sum(x*y for x, y in zip(log_ts, log_wp))
    denom = n * sxx - sx * sx
    slope = (n * sxy - sx * sy) / denom

    # Anchor: at log_t = 8.5, p = base_product_at_85
    log_p_85 = log(base_product_at_85)

    def p(t):
        dlog_t = log(t, 10) - 8.5
        return exp(log_p_85 + slope * dlog_t)

    fit = {"slope_gamma": slope, "anchor_log_t": 8.5,
           "anchor_p": base_product_at_85,
           "p_at_10^8.5": p(10**8.5), "p_at_10^10.5": p(10**10.5),
           "p_at_10^12.5": p(10**12.5),
           "scale_weighted_log_products": log_wp,
           "scale_log_ts": log_ts}
    return p, fit


def bh_rho(residue, t, bh_data):
    """Bateman-Horn base-tuple hit-density at scale t: ρ_r(t) = C_BH · (log(α·t))^{-m_r}.

    Uses ρ(t) = dN/dt where N_r(X) = C_BH · X / (log(α·X))^{m_r}.
    """
    info = bh_data["per_residue"][str(residue)]
    m_r = info["tuple_size"]
    C_BH = bh_data["C_BH_assumed"]
    alpha = 2520 * 46189  # A_const scale factor for N = M·t + r form
    logat = log(alpha * t)
    # ρ(t) ≈ C_BH / (log(α·t))^m_r
    return C_BH / (logat ** m_r)


def cumulative_E(residue, X, p_fn, bh_data, T_0=2.0, p_cap=1.0):
    """Integrate E_r([T_0, X]) = ∫_{T_0}^X ρ_r(t) · p_r(t) dt numerically.

    Use log-scale integration: t = exp(u), dt = exp(u) du.
    p_cap: cap p_r(t) at this value (default 1.0 since it's a probability).
    T_0: lower integration limit. Default 2.0 for backward compat; set to
    10^8 to respect the scale-model calibration floor.
    """
    u_lo = log(T_0)
    u_hi = log(X)
    if u_hi <= u_lo:
        return 0.0
    N = 500  # finer quadrature
    du = (u_hi - u_lo) / N
    E = 0.0
    for i in range(N):
        u_mid = u_lo + (i + 0.5) * du
        t = exp(u_mid)
        p_t = min(p_fn(t), p_cap)
        integrand = bh_rho(residue, t, bh_data) * p_t * t
        E += integrand * du
    return E


def main():
    try:
        scale = json.load(open(REPO / "data" / "scale_stability_test.json"))
        bh = json.load(open(REPO / "data" / "bh_per_residue_density.json"))
        factored = json.load(open(REPO / "data" / "case_a_density_factored.json"))
    except FileNotFoundError as e:
        print(f"Missing input file: {e}")
        return

    # Anchor per-residue pointwise probability at t=10^8.5 using direct measurement
    base_product_at_85 = {
        0:    3.11e-10,
        1716: 1.66e-10,
        4862: 1.16e-10,
        16302: 1.92e-10,
        17160: 1.60e-10,
    }

    print("=" * 80)
    print("Density integral model — pointwise probability AND cumulative count")
    print("=" * 80)
    results = {"description": "Proper separation of p_r(t) and E_r(X).",
               "per_residue": {}}

    for r in (0, 1716, 4862, 16302, 17160):
        print(f"\n=== r = {r} ===")
        # Fit pointwise probability, anchored at measured base product
        p_fn, fit = fit_pointwise_probability(scale, r, base_product_at_85[r])
        slope = fit["slope_gamma"]
        print(f"  Fit: p_r(t) = p_r(10^8.5) · 10^{{{slope:.3f} · (log10(t) - 8.5)}}")
        print(f"  anchor: p_r(10^8.5) = {base_product_at_85[r]:.3g}")
        # Pointwise at several t
        p_vals = {}
        for log_t in [8.5, 10.5, 12.5, 14.5, 16.5, 18.5]:
            t = 10 ** log_t
            p_vals[log_t] = p_fn(t)
        print(f"  Pointwise p_r(t):")
        for log_t, p in sorted(p_vals.items()):
            print(f"    t=10^{log_t}: p_r = {p:.3g}")
        # Cumulative E_r([T_0, X]) — with calibration floor T_0 = 10^8.
        T_0 = 10**8
        E_vals_calibrated = {}
        E_vals_unvalidated = {}  # from 2, shows effect of low-t extrapolation
        for X_exp in [12, 13, 14, 15, 16, 17, 18, 19, 20]:
            X = 10 ** X_exp
            E_vals_calibrated[X_exp] = cumulative_E(r, X, p_fn, bh, T_0=T_0)
            E_vals_unvalidated[X_exp] = cumulative_E(r, X, p_fn, bh, T_0=2.0)
        print(f"  Cumulative E_r([10^8, X]) (calibrated) vs E_r([2, X]) (full):")
        for X_exp in sorted(E_vals_calibrated):
            print(f"    X=10^{X_exp}: calibrated={E_vals_calibrated[X_exp]:.3g}, full={E_vals_unvalidated[X_exp]:.3g}")

        # Sensitivity envelope: vary γ by ±0.5.
        # γ < 0. γ_slow = γ + 0.5 (less negative slope = SLOWER decay = LARGER integral).
        # γ_fast = γ - 0.5 (MORE negative = FASTER decay = SMALLER integral).
        def p_fn_alt(t, slope_adj):
            dlog_t = log(t, 10) - 8.5
            return exp(log(base_product_at_85[r]) + (slope + slope_adj) * dlog_t)
        E_sens = {}
        for slope_adj, label in [(+0.5, "gamma_plus_0.5_slower_decay"),
                                  (0.0, "fitted_gamma"),
                                  (-0.5, "gamma_minus_0.5_faster_decay")]:
            p_alt = (lambda s=slope_adj: (lambda t, s=s: p_fn_alt(t, s)))()
            E_alt = {}
            for X_exp in [14, 17, 19]:
                X = 10 ** X_exp
                E_alt[X_exp] = cumulative_E(r, X, p_alt, bh, T_0=T_0)
            E_sens[label] = E_alt
        print(f"  Sensitivity envelope (γ ± 0.5) for E_r([10^8, X]):")
        print(f"  (γ_slow = γ + 0.5 → less negative → slower decay → larger integral)")
        for label, vals in E_sens.items():
            print(f"    {label:>32}: X=10^14: {vals[14]:.3g}, X=10^17: {vals[17]:.3g}, X=10^19: {vals[19]:.3g}")

        results["per_residue"][str(r)] = {
            "pointwise_fit": {
                "anchor_log_t": 8.5,
                "anchor_p": base_product_at_85[r],
                "slope_gamma": slope,
                "p_values": {f"10^{log_t}": p for log_t, p in p_vals.items()},
            },
            "cumulative_E_calibrated_from_10^8": {f"10^{x}": E for x, E in E_vals_calibrated.items()},
            "cumulative_E_full_range_2_to_X": {f"10^{x}": E for x, E in E_vals_unvalidated.items()},
            "sensitivity_envelope_calibrated": E_sens,
            "bh_shape_expected": bh["per_residue"][str(r)]["expected_count_at_horizon"],
        }

    with open(REPO / "data" / "density_integral_model.json", "w") as f:
        json.dump(results, f, indent=2, default=float)
    print(f"\nWrote data/density_integral_model.json")


if __name__ == "__main__":
    main()
