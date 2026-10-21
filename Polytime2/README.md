# Polytime2

A framework for polynomial-time algorithms with mathematical specifications,
correctness proofs, and finite Turing-machine realizations.

## Start here

Choose the guide for your task, then follow its interface and example links.
Exact contracts belong in Lean module and declaration docstrings; these guides
explain how to find and combine them.

| Task | Guide |
| --- | --- |
| Compose algorithms or specialize mathematical domains | [Computation][comp] |
| Choose carriers, canonical encodings, or size parameters | [Encoding][enc] |
| Use integer or binary arithmetic | [Arithmetic][arith] |
| Access, transform, fold, or pack arrays | [Arrays][arrays] |
| Access matrices or transform rows | [Matrices][matrices] |
| Use or extend finite-field elimination | [Gauss–Jordan][gj] |
| Export a computation to a standalone Turing machine | [TM0][tm0] |
| Change execution semantics or calling conventions | [Machine][machine] |
| Implement a missing foundational operation | [Primitives][primitives] |
| Find a worked application | [Examples][examples] |
| Prepare or consume an SMP instance | [SMP][smp] |

[comp]: Computation/README.md
[enc]: Encoding/README.md
[arith]: Arithmetic/README.md
[arrays]: Arrays/README.md
[matrices]: Matrices/README.md
[gj]: GaussJordan/README.md
[tm0]: TM0/README.md
[machine]: Machine/README.md
[primitives]: Primitives/README.md
[examples]: Examples/README.md
[smp]: Examples/SMP/README.md

## Build

From the repository root, run `lake build Polytime2`; use `import Polytime2`
in Lean. See the [root README](../README.md) for setup and pinned versions.

Using `lake comparator` is possible, but is not currently pursued during
development because theorem statements may still need to be adapted.

## Proposed next tasks

1. [Smith normal form](tasks/smith-normal-form.md): build integer-matrix
   operations and a certified algorithm using existing signed arithmetic.
2. [A prepared-SMP consumer](tasks/prepared-smp-consumer.md): connect a concrete
   certified solver to the preparation interface, preserving explicit rejection.
3. [Algorithm notation](tasks/algorithm-notation.md): pilot notation on existing
   composition proofs and retain their mathematical interfaces.

These are proposals, not completed features. Each task records its prerequisites
and acceptance criteria; remove completed entries and update the relevant guide.

Project requirements live in [GOAL.md](../GOAL.md), and target mathematical
problems live in [EXAMPLES.md](../EXAMPLES.md). Read only the linked sections
needed for the current task. Documentation maintenance follows
[AGENTS.md](../AGENTS.md#documentation).
