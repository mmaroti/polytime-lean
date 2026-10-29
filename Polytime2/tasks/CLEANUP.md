# Cook–Levin infrastructure cleanup

Status: proposed. [Task index](../README.md#proposed-next-tasks).

Each change must both extend the core infrastructure and substantially reduce
total Lean source lines after migrating its concrete callers. Count all new
infrastructure and replacement proofs. Generality or shorter application files
alone does not justify a change. Preserve mathematical contracts, canonical
encodings, and polynomial-time certificates, with no measurable checking
regression.

The savings below are acceptance budgets, not demonstrated reductions.

## 1. Certify bounded natural polynomial expressions once

### Prerequisites and evidence

Read the [arithmetic guide](../Arithmetic/README.md), then inspect
[NaturalArithmetic.lean](../Arithmetic/NaturalArithmetic.lean),
[WitnessEndpoints.lean](../Complexity/WitnessEndpoints.lean),
[BlockBase.lean](../Complexity/CookLevin/BlockBase.lean), and
[WireArithmetic.lean](../Circuit/WireArithmetic.lean).

The endpoint realization occupies about 130 lines to compute just
`2n + 1`, `2n + k + 2`, and `2n + 2k + 2`. Much of the proof manages binary
widths, intermediate bounds, increments, and conversion back to coordinates.
The same work recurs in block addresses and elementary wire arithmetic.

The initial replacement pool is roughly 340 lines of realization proofs across
endpoints, block addresses, initial addresses, and elementary wire arithmetic.
Mathematical address identities and final fit theorems remain necessary.

### Proposed capability

Certify evaluation of a fixed Mathlib `MvPolynomial` on bounded runtime natural
values, including mathematical size values. Derive sufficient internal widths
from the input bounds and certify intermediate arithmetic internally. Expose
the ordinary polynomial value; require only the final mathematical bound when
returning a coordinate in a requested interval.

Reuse existing bounded-natural codecs and arithmetic realizers. Do not
introduce another expression hierarchy or promote input values to public size
parameters. Initially support nonnegative polynomial expressions; subtraction
and conditional addressing are outside this pilot.

### Impact and acceptance

This extends core arithmetic from individual word operations to bounded
polynomial evaluation on runtime values. Applications can state their address
formulas and final bounds without rebuilding private width calculations.

- Migrate the motivating endpoint and address proofs together with the core
  evaluator; remove superseded local arithmetic helpers.
- Remove at least 100 net Lean source lines, including the evaluator and every
  replacement wrapper.
- Preserve public coordinate carriers, mathematical preconditions, and exact
  canonical encodings. Keep implementation widths private.
- Check affected modules and run `lake build Polytime2`.
- Compare checking costs before and after migration under the same conditions.

The main risk is building an evaluator whose infrastructure exceeds the
application savings. Reject the change if the complete migration misses the
net-line acceptance gate.

## Measured checking costs

Before the direct verifier import, profiling with cached imports gave these
single-run measurements:

| Module | Elapsed | Kernel type checking |
| --- | ---: | ---: |
| `Complexity/CookLevin/Reduction.lean` | 11.1 s | 7.9 s |
| `Complexity/CookLevin/FixedFormulaProgram.lean` | 5.8 s | 3.8 s |
| `Complexity/WitnessEndpoints.lean` | 2.6 s | 0.1 s |

These are diagnostics, not benchmark guarantees. They were collected by running
`lake env lean -Dprofiler=true -Dprofiler.threshold=100` on each source file.
Nested profiling of `Reduction.lean` used `-Dtrace.profiler=true` and
`-Dtrace.profiler.threshold=200`.

The nested trace shows large expansions of composed computations during the
short final reduction proofs. Shortening the endpoint arithmetic alone would
not address that measured slowdown. Use the existing
`Computation.specification` reduction boundary during migrations and preserve
explicit mathematical result contracts. Adding opacity wrappers alone is not
a qualifying infrastructure improvement: the core already has that capability.

For either proposal, compare repeated runs under the same conditions and
inspect both kernel checking and elapsed time. A source-line reduction must
not hide a checking regression or merely move the proof burden elsewhere.
