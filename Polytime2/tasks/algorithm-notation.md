# Algorithm notation

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Pilot higher-level Lean notation for recurring mathematical composition
patterns. Keep the existing `Computation` and realizability interfaces; machine
witnesses, tape layouts, and runtime polynomials remain internal.

## Prerequisites and first milestone

Start with the [composition guide](../Computation/README.md) and review concrete
callers in signed arithmetic and SMP preparation. Identify repeated argument
selection or binding patterns before designing syntax. The first milestone is
one small notation form together with migrations of at least two motivating
proofs, rather than a separate algorithm language.

## Acceptance

- Elaborate to existing certified composition rules with ordinary mathematical
  input and output types.
- Preserve admissibility obligations and make intermediate result sharing
  explicit when it matters.
- Support dependent sizes and result types needed by the motivating examples.
- Keep failures and remaining proof obligations understandable to callers.
- Remove superseded local helpers and compare total proof lines, including the
  notation infrastructure.
- Preserve the migrated public contracts and pass the relevant Lean checks.

Expand only when additional concrete callers justify it. Update the composition
examples and guide with the preferred usage, and remove completed task entries.
