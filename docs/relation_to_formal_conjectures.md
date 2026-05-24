# Relation to formal conjectures

## DeepMind FormalConjectures/ErdosProblems/647.lean

The DeepMind FormalConjectures repository contains a formal statement
of Erdős Problem #647. Their formulation uses the divisor function
tau and asks whether there exists n > 24 satisfying the domination
condition.

## Predicate equivalence

Our formalization uses `Candidate n := forall m, m < n -> m + sigma 0 m <= n + 2`
where `sigma 0` is Mathlib's divisor-count function (the arithmetic
function sigma evaluated at 0, which equals tau). This matches the
standard formulation.

The accompanying formalization proves `property_iff_div_bound`, an
explicit equivalence between the two formulations (max-form and
forall-form).

## Scope comparison

The DeepMind statement is a bare conjecture statement. This
repository provides:
- A computational reduction (96 residues -> 2 hard residues)
- Formal verification of the reduction steps
- Universal admissibility of the resulting prime tuples
- A barrier theorem limiting elementary approaches
- Conditional resolution under Dickson's conjecture
- Quantitative predictions (Bateman-Horn)

The results here do not resolve the DeepMind conjecture but provide
the most detailed structural analysis of the problem to date.
