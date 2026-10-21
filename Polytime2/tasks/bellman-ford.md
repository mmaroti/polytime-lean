# Bellman–Ford and difference constraints

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Certify Bellman–Ford and use it to solve finite integer difference constraints
`x_v - x_u ≤ c_uv`. Return either an integer assignment satisfying every
constraint or a directed cycle with negative total bound. Prove that the cycle
certifies infeasibility, including over the reals.

This is the recommended first graph task and a manageable step toward linear
programming. It supplies weighted paths and negative-cycle witnesses for
subsequent algorithms.

## Prerequisites and first milestone

Review the [array](../Arrays/README.md), [arithmetic](../Arithmetic/README.md),
and [composition](../Computation/README.md) guides. Choose ordinary finite graph
and path carriers, reusing Mathlib where suitable. Keep unreachable-distance
markers and predecessor storage internal.

First certify a bounded relaxation pass and its invariant relating distances to
walks of bounded length. Then implement shortest paths from a source and
negative-cycle recovery. For difference constraints, prepare an internal source
reaching every vertex so disconnected infeasible components are detected.

## Acceptance

- Expose vertex count, constraint count, and coefficient bit width as
  independent mathematical sizes; derive distance and witness storage
  internally.
- Return actual assignments or cycles without public search sentinels, and prove
  feasibility iff the constraint graph has no negative cycle.
- Bound intermediate integers, relaxation rounds, witness recovery, and complete
  machine costs polynomially in dimensions and coefficient bit width.
- Exercise negative weights, disconnected graphs, self-loops, empty systems,
  zero variables, and negative cycles in disconnected components.
- Export realizability and standalone TM0 certificates through shared rules.

Prefer bounded array scans over more elaborate graph data structures unless
concrete callers need them. General LP is a [separate
task](linear-programming.md).
