# Smith normal form

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Implement certified Smith normal form for rectangular integer matrices,
retaining the diagonal matrix and both unimodular transformations. The
mathematical contract, size parameters, and subsequent membership applications
are specified in [target example 3][target]; do not maintain another copy here.

[target]: ../../EXAMPLES.md#smith-normal-form

## Prerequisites and first milestone

Signed arithmetic and extended gcd already have realizability certificates;
start with the [arithmetic guide](../Arithmetic/README.md). Existing matrix row
operations specialize finite scalar tables. Review what can be reused from
[matrix access and traversal](../Matrices/README.md) before extending them to
runtime integer operations.

The first milestone is a mathematical integer row/column operation with derived
entry bounds, a realization by composition, and a concrete matrix example.
State its input, output, and preconditions before choosing the machine layout.
Choose the full normal-form algorithm only after reviewing its coefficient
bounds and polynomial progress argument.

## Acceptance

- Meet the linked rectangular normal-form contract, including transformations.
- Prove polynomial intermediate and output bit bounds and polynomial iteration
  counts in the mathematical dimensions and input bit length.
- Compose certified integer operations; include navigation, storage preparation,
  and output construction in the machine bound.
- Cover the linked zero-dimension, singular, sign, and rank-deficiency cases.
- Provide public realizability and standalone TM0 certificates.
- Follow with augmented-matrix membership, witness recovery, and coordinate
  transport as separate certified consumers of the normal form.

Count proof and infrastructure changes together, migrate motivating callers
when adding shared rules, and update the local guides as milestones finish.
