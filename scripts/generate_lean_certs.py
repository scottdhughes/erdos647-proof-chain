#!/usr/bin/env python3
"""
Generate Erdos647ClosureData.lean from closure_certificates_v2.json.

Certificate counts are read from the v2 JSON at generation time.

Proof strategy (verified by smoke tests):
  Level0BLe1Cert:
    - Use `where` syntax with `by decide` for both proofs
  Level0InadmCert / BranchCert.inadm:
    - covers: coversModPBool_correct _ _ (by native_decide)
    - h2, h3: intro u + rcases on membership + simp [BudgetForm.eval] + omega
      (omega handles both cases: budget matches → concrete arithmetic;
       budget mismatch → contradiction from numeric hypotheses)
    - h_budgets: rcases + subst + simp_all (simp sees 2=2 or 3=3)
"""

import json
import textwrap
from pathlib import Path

REPO = Path("/Users/scottdhughes/math_code/erdos647-github")
JSON_PATH = REPO / "data" / "closure_certificates_v2.json"
OUT_PATH  = REPO / "lean" / "Erdos647ClosureData.lean"

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def form_tuple(f):
    """Render one BudgetForm literal: ⟨a, b, budget⟩"""
    return f"⟨{f['a_red']}, {f['b_red']}, {f['budget']}⟩"


def rcases_pattern(n):
    """Build h|h|...|h with n arms."""
    return "|".join(["h"] * n)


def inadm_cert_block(forms, prime, indent="  "):
    """
    Emit the body lines of a Level0InadmCert (field := value, one per line).
    indent: prefix for each field line.

    Proof:
      h2/h3: intro u at front, then rcases + subst + simp [BudgetForm.eval] + omega.
             omega closes both:
               - budget=2 form + hb:budget=2: proves p < a*u+b (b >> p for all data)
               - budget=3 form + hb:budget=2: omega derives False from 3≠2
             Similarly for h3 with p^2.
      h_budgets: rcases + subst + simp_all (resolves budget = 2 ∨ budget = 3).
    """
    n = len(forms)
    form_lits = ", ".join(form_tuple(f) for f in forms)
    pat = rcases_pattern(n)

    # simp lemma to unfold List membership for n-element list
    simp_mem = "simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf"

    lines = [
        f"{indent}forms := [{form_lits}]",
        f"{indent}p := {prime}",
        f"{indent}p_prime := by decide",
        f"{indent}covers := coversModPBool_correct _ _ (by native_decide)",
        f"{indent}h2 := by",
        f"{indent}  intro f hf hb u",
        f"{indent}  {simp_mem}",
        f"{indent}  rcases hf with {pat} <;> subst h <;>",
        f"{indent}    simp only [BudgetForm.eval] at * <;> omega",
        f"{indent}h3 := by",
        f"{indent}  intro f hf hb u",
        f"{indent}  {simp_mem}",
        f"{indent}  rcases hf with {pat} <;> subst h <;>",
        f"{indent}    simp only [BudgetForm.eval] at * <;> omega",
        f"{indent}h_budgets := by",
        f"{indent}  intro f hf",
        f"{indent}  {simp_mem}",
        f"{indent}  rcases hf with {pat} <;> subst h <;> simp_all",
    ]
    return "\n".join(lines)


def ble1_cert_block(a, b, budget, indent="  "):
    """Render a Level0BLe1Cert using `where` syntax with `by decide`."""
    return "\n".join([
        f"{indent}form := ⟨{a}, {b}, {budget}⟩",
        f"{indent}budget_le_1 := by decide",
        f"{indent}b_ge_2 := by decide",
    ])


# ---------------------------------------------------------------------------
# certificate generators
# ---------------------------------------------------------------------------

def gen_ble1(res, cert):
    name = f"cert_r{res}"
    body = ble1_cert_block(cert["a_red"], cert["b_red"], cert["budget"])
    return f"def {name} : Level0BLe1Cert where\n{body}"


def gen_inadm(res, cert):
    name = f"cert_r{res}"
    body = inadm_cert_block(cert["witness_forms"], cert["prime"])
    return f"def {name} : Level0InadmCert where\n{body}"


def gen_branch(res, branch_idx, branch):
    name = f"cert_r{res}_c{branch_idx}"
    mech = branch["mechanism"]
    if mech == "ble1":
        body = ble1_cert_block(branch["a_red"], branch["b_red"], branch["budget"], indent="    ")
        return (
            f"def {name} : BranchCert :=\n"
            f"  .ble1 {{\n"
            f"{body}\n"
            f"  }}"
        )
    elif mech == "b23":
        body = inadm_cert_block(branch["witness_forms"], branch["prime"], indent="    ")
        return (
            f"def {name} : BranchCert :=\n"
            f"  .inadm {{\n"
            f"{body}\n"
            f"  }}"
        )
    else:
        raise ValueError(f"Unknown mechanism: {mech}")


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    with open(JSON_PATH) as f:
        data = json.load(f)

    certs = data["certificates"]

    ble1_defs   = []   # level0_ble1
    inadm_defs  = []   # level0_inadm_b2 / level0_inadm_b23
    branch_defs = []   # level1_branched branches

    for res, cert in sorted(certs.items(), key=lambda kv: int(kv[0])):
        lvl = cert["level"]
        if lvl == "level0_ble1":
            ble1_defs.append(gen_ble1(res, cert))
        elif lvl in ("level0_inadm_b2", "level0_inadm_b23"):
            inadm_defs.append(gen_inadm(res, cert))
        elif lvl == "level1_branched":
            for ci in range(30):
                branch = cert["branches"][str(ci)]
                branch_defs.append(gen_branch(res, ci, branch))
        else:
            raise ValueError(f"Unknown level {lvl} for residue {res}")

    total = len(ble1_defs) + len(inadm_defs) + len(branch_defs)
    print(f"Generated: {len(ble1_defs)} ble1, {len(inadm_defs)} inadm, "
          f"{len(branch_defs)} branch  (total {total})")

    header = textwrap.dedent(f"""\
        import Erdos647ClosureCerts

        /-!
        # Erdős #647 Closure Data

        Auto-generated by scripts/generate_lean_certs.py.
        {total} certificates: {len(ble1_defs)} Level0BLe1Cert,
        {len(inadm_defs)} Level0InadmCert, {len(branch_defs)} BranchCert.

        No sorry.
        -/

        namespace Erdos647ClosureData

        open Erdos647ClosureCerts Erdos647B23Closure

        """)

    sections = []

    sections.append(
        f"-- Level-0 budget_le_1 certificates ({len(ble1_defs)})\n\n"
        + "\n\n".join(ble1_defs)
    )

    sections.append(
        f"-- Level-0 inadmissibility certificates ({len(inadm_defs)})\n\n"
        + "\n\n".join(inadm_defs)
    )

    sections.append(
        f"-- Level-1 branch certificates ({len(branch_defs)})\n\n"
        + "\n\n".join(branch_defs)
    )

    footer = "\nend Erdos647ClosureData\n"

    content = header + "\n\n".join(sections) + footer

    OUT_PATH.write_text(content)
    print(f"Written: {OUT_PATH}")


if __name__ == "__main__":
    main()
