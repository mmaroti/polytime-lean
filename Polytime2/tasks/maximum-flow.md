# Edmonds–Karp maximum flow

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Given a finite directed network with nonnegative integer capacities and distinct
source and sink, return an integral maximum flow and a minimum cut of equal
value. The flow and cut together certify optimality.

This is a larger graph task supporting matching, reductions, and further
combinatorial optimization before general LP.

## Prerequisites and first milestone

Review the [array](../Arrays/README.md), [arithmetic](../Arithmetic/README.md),
and [composition](../Computation/README.md) guides. Reuse graph and path
infrastructure, including any developed for [Bellman–Ford](bellman-ford.md).
Choose a residual representation that distinguishes reverse arcs from original
arcs, including networks with antiparallel edges.

First certify a shortest augmenting-path search and one residual augmentation.
Then establish the Edmonds–Karp progress bound. Arbitrary augmenting paths are
insufficient: a bound proportional to the numerical capacity value would not
establish polynomial time for binary capacities.

## Acceptance

- Use mathematical network dimensions and capacity bit width as sizes; derive
  residual and accumulated-flow widths internally.
- Prove capacity constraints, flow conservation, and equality of flow and cut
  values, with the source inside and sink outside the returned cut.
- Bound augmentation count independently of capacity magnitudes, and include all
  searches, updates, cut extraction, and bit costs in the machine proof.
- Exercise zero capacities, disconnected terminals, antiparallel edges, and
  augmentations that cancel earlier flow.
- Export realizability and standalone TM0 certificates.
- Derive [bipartite matching](bipartite-matching.md) by a certified reduction if
  that task has not already been implemented.

Use straightforward bounded scans; optimal graph running time is not required.
