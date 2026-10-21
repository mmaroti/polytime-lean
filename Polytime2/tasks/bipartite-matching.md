# Maximum bipartite matching

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Given a finite bipartite graph, return a maximum matching and a vertex cover of
the same cardinality. Prove that these witnesses certify optimality and
establish the constructive form of Kőnig's theorem.

This is a moderate combinatorial optimization task with reusable alternating
paths and explicit optimality certificates.

## Prerequisites and first milestone

Review the [array](../Arrays/README.md) and
[composition](../Computation/README.md) guides and any graph traversal
introduced by [Bellman–Ford](bellman-ford.md). Use ordinary finite edge sets and
matchings; keep unmatched-vertex markers and traversal storage internal.

First certify alternating-path search and augmentation. A straightforward
augmenting-path algorithm suffices; Hopcroft–Karp is unnecessary for the
polynomial-time goal. If [maximum flow](maximum-flow.md) is available, prefer
its unit-capacity reduction and witness transport over another implementation.

## Acceptance

- Expose independent left and right vertex counts and the mathematical graph.
- Prove every returned matching edge exists and no two share an endpoint.
- Construct a cover meeting every edge, with cardinality equal to the matching.
- Prove polynomial search, augmentation, storage, and machine bounds; include
  cover extraction in the complete algorithm.
- Exercise empty parts, isolated vertices, disconnected graphs, perfect
  matchings, and examples requiring reassignment along an alternating path.
- Export realizability and standalone TM0 certificates by composition.

General nonbipartite matching and weighted matching are separate extensions.
