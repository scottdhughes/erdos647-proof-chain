# Contributing

This repository is a review package for the current Erdős #647 proof
chain. Issues and pull requests are welcome, especially for:

- checking that the Lean predicate matches the original problem;
- auditing the reduction to the `96` survivor classes;
- auditing the `55` closed residue classes;
- checking that `openResiduesStage1` is the correct remaining boundary;
- improving documentation without changing the mathematical claims.

Before opening a pull request, run:

```bash
./build.sh
bash scripts/axiom_audit.sh
```

Keep changes scoped. If a change alters theorem statements, residue
sets, data files, or axiom boundaries, explain the mathematical reason
and the verification command used.
