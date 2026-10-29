# Infrastructure cleanup review

Keep a change only when it both extends reusable core capabilities and
substantially reduces total Lean source after migrating existing callers.
Count new infrastructure, adapters, and replacement proofs together. Shorter
application files alone do not establish a benefit. Preserve mathematical
contracts, canonical encodings, and polynomial-time certificates.

The two highest-ranked opportunities below are already implemented in the
current repository. Their measured reductions provide concrete precedents;
they are not outstanding implementation tasks.

## 1. Reuse a certified verifier directly

The Cook–Levin application formerly reconstructed evaluation infrastructure
for a verifier whose polynomial-time certificate already existed. Local trace,
gate, circuit, and verifier evaluation proofs repeated foundational work.

[DirectVerifier.lean](../Complexity/DirectVerifier.lean) now imports the
certified word verifier through `wordVerifier_realizable`. Shared finite-window
machine observation and trace infrastructure belongs in
[TM0](../TM0/README.md), while the reduction uses the resulting certificate.
The migration also consolidated the array operations needed by these callers.

Impact: an existing polynomial-time word verifier can be reused through a core
bridge instead of receiving another application-specific evaluator. This was
the strongest opportunity because it removed an entire duplicated proof path.

Commit `5f786f7` added 829 and removed 1,082 Lean lines: **253 fewer lines**,
including all accompanying infrastructure changes. This is the whole commit's
reduction, not an isolated measurement of the verifier theorem.

Drawback: the shared bridge must preserve the precise word encoding, machine
semantics, and acceptance contract. Its foundational proof remains necessary;
the benefit comes from sharing it and deleting the superseded implementation.

## 2. Certify bounded polynomial arithmetic once

Witness endpoints, block addresses, and circuit wire addresses repeatedly
assembled additions, multiplications, intermediate bounds, and width changes.
Their mathematical formulas were short, but their realization proofs were not.

[NaturalPolynomial.lean](../Arithmetic/NaturalPolynomial.lean) now certifies a
fixed Mathlib `MvPolynomial` over mathematical sizes and runtime coordinates.
`polynomialPosition` exposes the ordinary value and its final fit condition;
the realization derives intermediate widths internally. Concrete callers
include [WitnessEndpoints.lean](../Complexity/WitnessEndpoints.lean),
[BlockBase.lean](../Complexity/CookLevin/BlockBase.lean), and
[WireArithmetic.lean](../Circuit/WireArithmetic.lean).

Impact: core arithmetic supports whole bounded polynomial expressions, while
applications supply formulas and final bounds. Commit `daa83c0` added 228 and
removed 336 Lean lines: **108 fewer lines**, including the evaluator and all
migrations. This ranks second because its scope is narrower, although its
replacement pattern is particularly direct.

Drawback: nonnegative polynomial expressions do not cover subtraction,
branching, or arbitrary indexing. Extending the evaluator to those operations
needs a separate concrete replacement pool and another net-savings check.

## Computed-size transport: investigate before implementing

The remaining candidate is repeated transport of computed-size frames, not
promotion of input-derived counts itself. Existing computed-size calls already
perform that promotion. Narrowing an array to its actual count is a distinct
operation and need not share the same proof.

Inspect [ComputedRecord.lean](../Computation/ComputedRecord.lean),
[ComputedProjection.lean](../Computation/ComputedProjection.lean),
[RetainBoolean.lean](../Computation/RetainBoolean.lean), and
[RetainUnary.lean](../Computation/RetainUnary.lean), starting with the
[computed-size guide](../Computation/README.md#sizes-and-loops).
These proofs repeatedly manipulate frame headers, substituted widths, padded
payloads, and encoding equalities. A shared encoding-transport rule for
dependent payloads could subsume parts of them.

Commonality is limited: singleton records preserve payload bits, Boolean
results have fixed width, unary results absorb padding into a larger capacity,
and frame projection changes the retained size assignment. A general rule may
leave almost all these obligations with its callers. No substantial net saving
has yet been demonstrated, so this candidate ranks below the completed work.

Before adopting it, prototype the rule and migrate those concrete callers in
the same change. Require at least 50 net Lean lines removed, counting every new
lemma and adapter, plus a reusable capability beyond the existing rules.
Reject the prototype if either requirement fails. Do not add a new result
interface merely to unify names or hide obligations behind wrappers.

## Verification and acceptance

For any further cleanup, record the exact replaced declarations and count Lean
lines before and after the complete migration. Check affected modules and run
`lake build Polytime2`. Compare repeated checking runs with cached imports under
the same conditions, using elapsed time and kernel profiling; investigate any
consistent regression before accepting the change. Source reduction alone does
not demonstrate faster checking. Keep tape wiring and codec proofs in the core,
and retain ordinary mathematical contracts in applications.
