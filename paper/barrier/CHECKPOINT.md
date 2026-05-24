# Barrier paper checkpoint — 2026-04-25, refreshed 2026-04-26

**Status (2026-04-26):** circulation-prep cleanup complete; **left open
for integration with the main #647 preprint**. Paper is a self-contained
companion to the main preprint and Path B paper.

The original 2026-04-25 freeze ("additive only") was lifted on 2026-04-26
for circulation-prep work (Tasks 4 + 2 + 3 of the tightening audit). Paper
remains in a clean checkpoint state; further text edits should still be
additive unless an explicit redirection from the main #647 preprint
strategy requires revisions.

## Current state (2026-04-26)

- **Length:** 32 pages compiled (with full bibliography)
- **Sections drafted:** §§1–9 unchanged (intro, setup, main theorems,
  structural reduction, empirical detail, CSP audit chain, obstruction
  analysis, Lean formalization, open problems)
- **Cor 4.6 (full divisibility):** added at `04_structural_reduction.tex:167`
  to support Path B's $n = 2520 m$ framework with a clean cite target;
  Lean cert at `lean/Erdos647FullDivisibility.lean` (commit `aec6dfd`)
- **Scope-discipline audit:** clean (no overclaim regressions in this
  cleanup pass; danger list still zero matches)
- **Bibliography:** 21 entries, all verified against primary sources
  (DOIs, ISBNs, arXiv eprints), zero TODO markers. The "Project-internal
  memo cites" partition has been emptied (5 audit memos + 2 Lean / cycle3
  cites either replaced with verbal forward references or pointed to
  supplementary materials). One residual flag: `GuyB8` bib key references
  Section B8, which is "unitary aliquot sequences" in the 3rd ed. — pin
  the right subsection in a final pre-submission pass.
- **Build status:** 0 LaTeX errors, 0 undefined references, 0 undefined
  citations.
- **PDF tracking:** `main.pdf` untracked, in `.gitignore`; PDFs are
  local artifacts only.
- **Framework-attractor handoff:** `docs/audits/framework_attractor_handoff_20260425.md`,
  ~3 pages, executive synthesis for future contributors.

## Commit chain producing this checkpoint

Original (2026-04-25 freeze):
- `3891115` Draft barrier paper Lean formalization section (§8)
- `2a0c277` Draft barrier paper open-problems section (§9)
- `e637c7e` Draft barrier paper empirical-detail section (§5)
- `3bf4756` Audit barrier paper draft for scope and quantifier discipline
- `3df106d` Draft framework-attractor handoff doc

Circulation-prep cleanup (2026-04-26):
- `aec6dfd` Lean cert: `Erdos647FullDivisibility.lean` (Cor 4.6 backing)
- `64e804d` Task 4: drop project-internal memo cites + TT2022 placeholder
- `5041aa6` Tasks 2+3: resolve all remaining bib TODOs against primary sources

## North star going forward

Every subsequent attack on \#647 must answer:

> Can this prove **emptiness** of survivors, not just sparsity?

If yes — closure track, may modify §3 / §6 of the paper.
If no  — barrier/evidence track, additive to the audit chain only.

## What this checkpoint does NOT mean

- It does not mean the residual frontier is closed (it is not — that
  is still the open question).
- It does not mean further audit layers are pointless (B+D+C empirical
  sprint, exact small-k classification, and the branch-gluing attack
  remain open).
- It does not mean the paper is locked-down submission-ready in
  isolation. The barrier paper is **left open for integration with the
  main #647 preprint**: when the main preprint reaches its own
  circulation point, expect to revise the barrier paper's intro,
  cross-references, and trust-chain table to align with the main
  preprint's framing and citation graph.

## What this checkpoint DOES mean

The record is stable and bibliographically clean. The barrier paper
compiles standalone, has all citations resolved against primary
sources, and is structurally ready to function as the cited dependency
for both Path B and the main #647 preprint.

Further text edits should be additive (new audit results, new attack
outcomes) OR coordinated with the main preprint's submission strategy
— not free-form revisions.
