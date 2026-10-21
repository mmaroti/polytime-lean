# Exact rational linear programming

Status: longer-term proposal. [Task index](../README.md#proposed-next-tasks).

## Outcome

Solve rational linear programs with exact mathematical outcomes: infeasibility,
a finite optimum with an optimizer, or unboundedness with a feasible point and
an improving ray. Include appropriate infeasibility or optimality certificates
for the chosen standard form.

This is a substantial project. A polynomial-time ellipsoid or interior-point
method needs geometric invariants and precision control in addition to exact
arithmetic. Ordinary simplex does not supply the required polynomial guarantee.

## Prerequisites and first milestone

Start with the [arithmetic](../Arithmetic/README.md),
[encoding](../Encoding/README.md), and [matrix](../Matrices/README.md) guides.
Review rational and linear-algebra infrastructure before adding codecs or
arithmetic. Public carriers should be rational matrices and vectors;
normalization and temporary precision belong inside the implementation.

Prefer completing [difference constraints](bellman-ford.md) and [maximum
flow](maximum-flow.md) first. They provide smaller inequality-solving and
optimization projects, but do not replace general LP.

The first milestone is to fix a standard form and all three outcome contracts,
then select an algorithm with a complete bit-complexity argument. Audit bounded
feasibility, reductions from general LP, rounding, and exact solution recovery
before implementation. Certificate checking alone is not a solver milestone.

## Acceptance

- Expose independent variable count, constraint count, and coefficient bit
  width; derive all precision and working capacities internally.
- Cover arbitrary rational inputs of the chosen form, including empty and
  lower-dimensional feasible regions and all three outcomes.
- Prove correctness and polynomial bounds for intermediate representations,
  iteration counts, precision, and exact witness extraction.
- Include preparation, navigation, arithmetic, and output construction in the
  complete bit-level runtime bound.
- Export public realizability and standalone TM0 certificates.

Split the chosen method into concrete follow-up tasks only after reviewing the
algorithm and precision requirements. Optimal practical performance and strongly
polynomial running time are not requirements.
