# Constructive 2-SAT

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Solve Boolean formulas whose clauses have at most two literals. Return either a
satisfying assignment or a variable with implication paths from it to its
negation and back, certifying unsatisfiability. When an empty clause causes
failure, return that clause as the witness.

This connects Boolean CSP solving to reusable directed reachability and strongly
connected components.

## Prerequisites and first milestone

Review the [encoding](../Encoding/README.md), [array](../Arrays/README.md), and
[composition](../Computation/README.md) guides and existing clause interfaces
before adding formula carriers or codecs. Reuse graph machinery introduced by
[Bellman–Ford](bellman-ford.md) where its interfaces apply.

First certify the implication-graph construction and its interpretation for
assignments. Then compute components and construct an assignment from the
condensation order. A polynomial reachability method is acceptable; linear-time
DFS algorithms are not required. Handle empty and unit clauses explicitly.

## Acceptance

- Expose variable and clause counts as mathematical sizes, deriving graph
  dimensions and working storage internally.
- Prove satisfiability iff no variable shares a strongly connected component
  with its negation, after handling any empty clause.
- Return an assignment on success, contradictory implication paths on ordinary
  failure, or an actual empty-clause witness when one exists.
- Certify graph construction, assignment or witness extraction, and the complete
  polynomial machine bound, not just the satisfiability criterion.
- Exercise empty formulas, zero variables, unit clauses, repeated literals,
  tautologies, and contradictory implication cycles.
- Export realizability and standalone TM0 certificates.

Keep graph traversal reusable for later CSP and reduction tasks.
