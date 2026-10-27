# Polynomial reduction from 3-SAT to CLIQUE

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Certify the standard reduction: create one vertex per literal occurrence and
connect occurrences from different clauses when they are not contradictory. A
formula with `m` clauses is satisfiable iff the graph has a clique of size `m`.
Use clauses with exactly three literals, allowing repetitions.

This is a relatively small first task for certified polynomial reductions,
instance construction, and witness transport.

## Prerequisites and first milestone

Review the [encoding](../Encoding/README.md), [array](../Arrays/README.md), and
[composition](../Computation/README.md) guides. Use the shared clause carriers
and satisfaction predicates in [SAT/ThreeSAT.lean](../SAT/ThreeSAT.lean).
Reuse existing graph interfaces before introducing new ones. State the
reduction and witness correspondence mathematically before choosing encodings.

First certify graph construction and transport a satisfying assignment to a
clique by selecting a true occurrence in each clause. Then recover a satisfying
assignment from a clique, assigning unused variables arbitrarily.

## Acceptance

- Preserve independent variable and clause counts, deriving occurrence and graph
  sizes internally with exact canonical encodings.
- Prove the graph is simple and the satisfiability equivalence in both
  directions, including constructive witness conversions.
- Bound construction, output size, and witness transport polynomially; include
  their complete realizability and standalone TM0 certificates.
- Exercise zero clauses, repeated literals, contradictory occurrences, and
  variables absent from every clause.
- Use shared composition rules to support subsequent reductions.

This certifies a reduction, not a polynomial solver for either problem. A full
NP-completeness theorem additionally requires a precise NP interface, CLIQUE
membership, and an established hardness starting point for 3-SAT. Cook–Levin is
a separate, substantially larger project.
