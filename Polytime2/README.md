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
| Use relational CSP mathematical contracts | [CSP][csp] |
| State polynomial reductions and NP contracts | [Complexity][complexity] |

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
[csp]: CSP/README.md
[complexity]: Complexity/README.md

## Build

From the repository root, run `lake build Polytime2`; use `import Polytime2`
in Lean. See the [root README](../README.md) for setup and pinned versions.

Using `lake comparator` is possible, but is not currently pursued during
development because theorem statements may still need to be adapted.

## Proposed next tasks

1. [A prepared-SMP consumer](tasks/prepared-smp-consumer.md): connect a concrete
   certified solver to the preparation interface, preserving explicit rejection.
2. [Algorithm notation](tasks/algorithm-notation.md): pilot notation on existing
   composition proofs and retain their mathematical interfaces.
3. [Bellman–Ford and difference constraints](tasks/bellman-ford.md): build graph
   foundations and return feasible assignments or negative-cycle certificates.
4. [Maximum bipartite matching](tasks/bipartite-matching.md): return a matching
   and a vertex cover certifying optimality.
5. [Constructive 2-SAT](tasks/2-sat.md): return an assignment or an explicit
   unsatisfiability witness.
6. [Edmonds–Karp maximum flow](tasks/maximum-flow.md): certify integral flows
   and minimum cuts with polynomial bit costs.
7. [3-SAT to CLIQUE](tasks/3-sat-to-clique.md): certify a polynomial reduction
   and both witness conversions.
8. [Exact rational linear programming](tasks/linear-programming.md): a
   longer-term solver project requiring a full precision and bit-cost analysis.
9. [CSP Taylor hardness](tasks/csp-taylor-hardness.md): formalize fixed-template
   NP-completeness for rigid cores without Taylor polymorphisms.
10. [Infrastructure next steps](tasks/NEXTSTEPS.md): finish the flexible
    computed-size result rules identified by the CSP review.

These are proposals, not completed features. Each task records its prerequisites
and acceptance criteria; remove completed entries and update the relevant guide.

Project requirements live in [GOAL.md](../GOAL.md), and target mathematical
problems live in [EXAMPLES.md](../EXAMPLES.md). Read only the linked sections
needed for the current task. Documentation maintenance follows
[AGENTS.md](../AGENTS.md#documentation).
