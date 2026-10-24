# Smith normal form consolidation review

Reviewed commit `104bc64` against `085ac82`: 268 Lean files, 38,142 lines added
and 37 removed. This review concerns infrastructure pain points and reuse
opportunities in that change.

The largest reduction opportunity is the adapter code around the algorithm.
Existing primitives are mostly sufficient, but composition through dependent
sizes, products, and bounded carriers requires repeated proof work.

The estimates below are net savings, allowing for new shared infrastructure
and preserving mathematical contracts and examples. They remain estimates
until the proposed migrations compile. The ranges overlap and should not be
added directly. They exclude cosmetic removal of comments or file boilerplate.

| Rank | Net Lean lines removed | Consolidation opportunity |
| --- | ---: | --- |
| 1 | 700–1,000 | Computed-size and host-domain transport |
| 2 | 350–600 | Argument selection and product mapping |
| 3 | 300–450 | Redundant, unused intermediate corollaries |
| 4 | 200–350 | Certified-step-to-fold simulation |
| 5 | 150–250 | Constructor laws for bounded arrays and matrices |
| 6 | 120–220 | Fixed-workspace narrowing wrappers |
| 7 | 80–160 | Row/column dualization through transposition |
| 8 | 60–120 | Width formulas shared across scalar domains |
| 9 | 20–80 | Stable computation/specification boundaries |

## 1. Computed-size and host-domain transport

The four `AtSize` modules and four `StoredRank` modules occupy about 1,936
lines. They repeatedly prepare a rank frame, rename domains, convert matrices,
invoke a callee, reconstruct host values, and remove the internal header. The
Hermite and cleanup versions are particularly similar. See
[IntegerRectangularHermiteAtSize.lean][hermite-size] and
[IntegerRectangularHermiteStoredRank.lean][hermite-stored].

Extend `ComputedFrame` and `ComputedCall` with a reusable host-payload call and
header-removal rule, supported by constructor transport lemmas. Migrate
insertion, compaction, Hermite reduction, and cleanup together. Mathematical
admissibility and correctness remain specific; frame encoding and cast
bookkeeping should be shared.

## 2. Argument selection and product mapping

The touched files contain 213 uses of `pairProjection_realizable`. Repeated
`onResults` proofs enumerate finite names merely to select arguments or fields.
The full [Smith realization][smith] illustrates the nested projection chains.

Add small compositional rules for selecting arguments, projecting a computed
product, and mapping computations over products. Existing `pairOutputs`,
`withArguments`, and `onResults` provide the foundation. Arbitrary argument
selection can use the certified record machinery when duplicate selections
require copies.

## 3. Redundant intermediate corollaries

A source scan found 26 candidate declarations spanning approximately 493 lines.
A separate check of compiled declaration dependencies confirmed that they have
no dependents in the imported Polytime2 graph. This does not establish whether
external users depend on them.

Examples include `integerBezoutRowsWithLeft_preserves` in
[IntegerBezoutTracking.lean][bezout-tracking] and
`integerHermiteRowStage_preserves` in [IntegerHermiteStage.lean][stage]. These
restate mathematical preservation results through an existing exact-value
theorem.

Retain the principal Smith, solver, witness, and coordinate contracts. Review
the intermediate corollaries individually and remove those whose intended
uses are already served by exact-value correctness plus the pure mathematical
theorem. This is the most concrete, lowest-risk initial reduction.

## 4. Certified-step-to-fold simulation

Several controllers turn a computation with a logical precondition into a
total update using `if valid then … else state`, certify that update, then
prove encoded prefixes agree with mathematical prefixes. See
[HermiteStageController.lean][stage-controller],
[HermiteRowsController.lean][rows-controller], and
[HermiteAlternatingController.lean][alternating-controller].

`arrayFold_realizable` already supplies invariant reasoning. The missing
convenience layer combines a certified partial step, its total extension, and
a mathematical prefix simulation. Domain-specific growth and admissibility
arguments would remain.

## 5. Constructor laws for bounded arrays and matrices

`reinterpretInputs`, `refineOutput`, and `reinterpretOutput` exist, but
distributing bounds through containers still requires manual codec work.
[IntegerNarrow.lean][narrow] is a clear example: moving a whole-matrix bound to
individual entries requires a substantial preparation proof.

Add encoding-preserving laws for restrictions through arrays, matrices, and
products. Then derive bounded matrix maps, narrowing, and related adapters
from scalar operations. Reuse Mathlib's subtype equivalences.

## 6. Fixed-workspace narrowing wrappers

[HermiteWorkspace.lean][workspace],
[HermiteStageWorkspace.lean][stage-workspace],
incoming stages, and alternating stages each strengthen a precondition,
execute a larger-width operation, narrow its result, and restate its
mathematical value.

A shared rule for executing and narrowing under a proved output bound could
express this. Keep each mathematical bound proof; share the computation,
realization, and value-preservation wrapper.

## 7. Transposition duality

Column Bézout, column remainder, row Hermite, and column addition each prepare
transposed inputs and transpose outputs back. See
[IntegerBezout.lean][bezout] and [IntegerHermiteRow.lean][hermite-row].

A common conjugation adapter, combined with product mapping from finding 2,
should replace much of this wiring.

## 8. Width formulas shared across scalar domains

The scalar-polymorphic `hermiteSweepBasisIncrement` in
[HermiteSweepMath.lean][sweep] already demonstrates a useful approach. Other
formulas require repeated evaluation and renaming proofs, including the two
`outputWidth_rename` lemmas in the Hermite and cleanup adapters.

Define suitable formulas once over a semiring and provide evaluation and
renaming lemmas. This reduces algebraic bookkeeping without changing
capacities.

## 9. Stable computation/specification boundaries

[IntegerSystemCoordinates.lean][coordinates] needs a 16-million-heartbeat
budget for short composition proofs. There are also 136 `withSpecification`
occurrences in the touched files. Conversion cost was a major development
pain, with smaller direct line savings.

Stable observer/evaluation lemmas and controlled unfolding boundaries should
make correctness transport more predictable. This deserves attention for
development speed, but its line savings overlap with earlier findings and
should be counted conservatively.

## Recommended sequence

Start with finding 3 for an immediate measurable reduction, then implement
finding 1 as the main infrastructure improvement. After overlap, a reasonable
first consolidation target is 1,500–2,500 net Lean lines.

For each consolidation, count new infrastructure together with migrated
callers, retain the required contracts and examples, and report the verified
net Lean line change. The review itself changed no Lean code.

[hermite-size]: Polytime2/Matrices/IntegerRectangularHermiteAtSize.lean
[hermite-stored]: Polytime2/Matrices/IntegerRectangularHermiteStoredRank.lean
[smith]: Polytime2/Matrices/IntegerSmithReduction.lean
[bezout-tracking]: Polytime2/Matrices/IntegerBezoutTracking.lean
[stage]: Polytime2/Matrices/IntegerHermiteStage.lean
[stage-controller]: Polytime2/Matrices/HermiteStageController.lean
[rows-controller]: Polytime2/Matrices/HermiteRowsController.lean
[alternating-controller]: Polytime2/Matrices/HermiteAlternatingController.lean
[narrow]: Polytime2/Matrices/IntegerNarrow.lean
[workspace]: Polytime2/Matrices/HermiteWorkspace.lean
[stage-workspace]: Polytime2/Matrices/HermiteStageWorkspace.lean
[bezout]: Polytime2/Matrices/IntegerBezout.lean
[hermite-row]: Polytime2/Matrices/IntegerHermiteRow.lean
[sweep]: Polytime2/Matrices/HermiteSweepMath.lean
[coordinates]: Polytime2/Matrices/IntegerSystemCoordinates.lean
