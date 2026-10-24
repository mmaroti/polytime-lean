# Smith normal form consolidation review

Reviewed commit `104bc64` against `085ac82`: 268 Lean files, 38,142 lines added
and 37 removed. This review concerns infrastructure pain points and reuse
opportunities in that change.

The largest reduction opportunity is the adapter code around the algorithm.
Existing primitives are mostly sufficient, but composition through dependent
sizes, products, and bounded carriers requires repeated proof work.

The estimates below are net savings, allowing for new shared infrastructure
and preserving mathematical contracts and examples. Implemented findings report
measured savings; the others remain estimates until their migrations compile.
The ranges overlap and should not be added directly. They exclude cosmetic
removal of comments or file boilerplate.

Estimates for findings 5–9 were reassessed against `c818b58`, after findings
1–3. They allow for the remaining caller-specific proofs and the cost of new
shared rules. These are source-based estimates, not verified migrations;
findings 1–3 retain their measured savings of 1,387 lines in total.

| Finding | Net Lean lines removed | Consolidation opportunity |
| --- | ---: | --- |
| 1 | 107 (actual) | Computed-size and host-domain transport |
| 2 | 495 (actual) | Argument selection and product mapping |
| 3 | 785 (actual) | Redundant, unused intermediate corollaries |
| 4 | 55 (actual) | Certified-step-to-fold simulation |
| 5 | 40–100 | Constructor laws for bounded arrays and matrices |
| 6 | 30–80 | Fixed-workspace narrowing wrappers |
| 7 | 20–70 | Row/column dualization through transposition |
| 8 | 0–30 | Width formulas shared across scalar domains |
| 9 | 0–20 | Stable computation/specification boundaries |

## 1. Computed-size and host-domain transport

At review time, the four `AtSize` and four `StoredRank` modules occupied about
1,936 lines. They repeatedly prepared a rank frame, renamed domains, converted
matrices, invoked a callee, reconstructed host values, and removed the internal
header. The Hermite and cleanup versions were particularly similar. See
[IntegerRectangularHermiteAtSize.lean][hermite-size] and
[IntegerRectangularHermiteStoredRank.lean][hermite-stored].

Implemented in [ComputedHost.lean][computed-host]: shared count reading,
renamed record arguments, computed-size calls, and host-result header removal.
Insertion, compaction, Hermite reduction, cleanup, bounded-array append, and
packed-array call preparation use these rules. Shared matrix presentation
transport lives in [IntegerRename.lean][integer-rename]. Genuinely dependent
results retain their computed counts.

Including new infrastructure and migrated examples, this removes 676 Lean
lines and adds 569: **107 net lines removed**. The original 700–1,000 estimate
was too optimistic; mathematical admissibility and correctness remain specific.
The full `lake build Polytime2` passed (3,846 jobs), and the migrated contracts
use only Lean’s standard axioms.

## 2. Argument selection and product mapping

The reviewed files contained 213 uses of `pairProjection_realizable`, with
repeated finite case splits merely to select arguments or fields.

Implemented `Realizable.fst`, `snd`, `prodMk`, and `prodMap` in
[Records.lean][records], and arbitrary static `onArguments` selection in
[RecordArguments.lean][record-arguments]. These reuse the existing composition,
copy, and record certificates. Callers across arithmetic, arrays, matrices,
and SMP use the shared rules; the [Smith realization][smith] now expresses
nested projections directly. Codec conversions and computed argument producers
retain `onResults`.

Including the new infrastructure, this removes 1,085 Lean lines and adds 590:
**495 net lines removed** relative to `22997db`. The full
`lake build Polytime2` passed (3,846 jobs); the new rules and audited Smith
contracts use only Lean’s standard axioms.

## 3. Redundant intermediate corollaries

Implemented across the library: removed 46 redundant intermediate corollaries.
Compiled declaration dependencies and source references were checked together;
wrappers used by examples were retained. The audit went beyond the original
26 candidates and included a second pass for newly unused corollaries.

Exact-value contracts remain, including
`integerBezoutRowsWithLeft_compute` in
[IntegerBezoutTracking.lean][bezout-tracking] and
`integerHermiteRowStage_correct` in [IntegerHermiteStage.lean][stage].
Combine these with the corresponding pure `IntegerMatrix` theorems. Principal
Smith, solver, witness, and coordinate contracts and all examples are retained.

Relative to `646df2e`, this removes 787 Lean lines and adds two import lines:
**785 net lines removed**. Imports used only by deleted wrappers were removed
or moved to their remaining callers. The full `lake build Polytime2` passed
(3,846 jobs); the retained principal contracts use only Lean’s standard axioms.

## 4. Certified-step-to-fold simulation

Implemented in [Fold.lean][fold]: `arrayFoldPartialStep` accepts a
proof-dependent update, `ArrayFold.extend` supplies its total extension, and
`arrayFoldStep_of_partial_realizable` reuses its certificate under the same
admissibility condition. Ordinary total steps specialize the same constructor.
`ArrayFold.prefix_invariant` defaults to the complete traversal while retaining
explicit arbitrary-prefix support.

Migrated ten update paths across Hermite controllers, remainder sweeps,
diagonal cleanup, pivot permutations, stable packing, and integer dot products.
Removed the superseded unary cleanup certificate. Runtime guards, mathematical
contracts, canonical encodings, and exact widths are retained.

Relative to `c818b58`, this removes 207 Lean lines and adds 152:
**55 net lines removed**. The 100–200 estimate remained optimistic: initial
conditions, growth bounds, admissibility, and mathematical recurrences still
need their specific proofs, and the shared rules have a cost of their own.
The full library build passed (3,847 jobs), including the module outside the
root import graph. The shared rules, migrated controllers, and audited Smith
and solver contracts use only Lean's standard axioms.

## 5. Constructor laws for bounded arrays and matrices

`reinterpretInputs`, `refineOutput`, and `reinterpretOutput` exist, but
distributing bounds through containers still requires manual codec work.
[IntegerNarrow.lean][narrow] is a clear example: moving a whole-matrix bound to
individual entries requires a substantial preparation proof.

Add encoding-preserving laws for restrictions through arrays, matrices, and
products. Then derive bounded matrix maps, narrowing, and related adapters
from scalar operations. Reuse Mathlib's subtype equivalences.

The main example's realization theorem is only 42 lines, and
`entryBoundEquiv` and `matrix_encode_bits_congr` already supply part of the
infrastructure. The revised range includes related widening and transposition
adapters, after paying for the container laws; narrowing alone cannot justify
the original estimate.

## 6. Fixed-workspace narrowing wrappers

[HermiteWorkspace.lean][workspace],
[HermiteStageWorkspace.lean][stage-workspace],
incoming stages, and alternating stages each strengthen a precondition,
execute a larger-width operation, narrow its result, and restate its
mathematical value.

A shared rule for executing and narrowing under a proved output bound could
express this. Keep each mathematical bound proof; share the computation,
realization, and value-preservation wrapper.

Paired narrowing already uses `prodMap`, and the three ordinary Hermite
workspace wrappers have short composition proofs. Most remaining work proves
that results fit. The revised estimate also includes repeated resizing of
matrix/basis triples, without counting their bound proofs or finding 5's codec
savings again.

## 7. Transposition duality

Column Bézout, column remainder, row Hermite, and column addition each prepare
transposed inputs and transpose outputs back. See
[IntegerBezout.lean][bezout] and [IntegerHermiteRow.lean][hermite-row].

A common conjugation adapter could replace more input preparation and
conjugation wiring. Paired output transposition already uses `prodMap` from
finding 2. The revised estimate allows for distinct argument layouts, retained
mathematical contracts, and the new adapter; it excludes savings already
measured in finding 2.

## 8. Width formulas shared across scalar domains

The scalar-polymorphic `hermiteSweepBasisIncrement` in
[HermiteSweepMath.lean][sweep] already demonstrates a useful approach. Other
formulas require repeated evaluation and renaming proofs, including the two
`outputWidth_rename` lemmas in the Hermite and cleanup adapters.

Define suitable formulas once over a semiring and provide evaluation and
renaming lemmas. This reduces algebraic bookkeeping without changing
capacities.

The two cited `outputWidth_rename` lemmas total only 17 lines, including their
statements. Most other evaluation proofs already use short `simp` calls.
Shared formula and evaluation lemmas would cost lines themselves, so this
finding may improve maintenance without producing a net reduction.

## 9. Stable computation/specification boundaries

[IntegerSystemCoordinates.lean][coordinates] needs a 16-million-heartbeat
budget for short composition proofs. Conversion cost was a major development
pain, with smaller direct line savings. The many `withSpecification` calls
are not themselves evidence of redundancy: they often expose the intended
mathematical function.

Stable observer/evaluation lemmas and controlled unfolding boundaries should
make correctness transport more predictable. This deserves attention for
development speed, but its line savings overlap with earlier findings and
should be counted conservatively.

Finding 1 already introduced a reduction boundary for computed host results.
The coordinate proofs remain short, and additional observer lemmas may add
lines. The revised range therefore allows for no net reduction; assess this work
primarily by proof-checking cost and reliability.

## Recommended sequence

Findings 1–4 are implemented. The remaining findings await a separate decision.
Validate their estimates with concrete migrations before setting a combined
reduction target; findings 8–9 need not reduce lines to be useful.

For each consolidation, count new infrastructure together with migrated
callers, retain the required contracts and examples, and report the verified
net Lean line change.

[hermite-size]: Polytime2/Matrices/IntegerRectangularHermiteAtSize.lean
[hermite-stored]: Polytime2/Matrices/IntegerRectangularHermiteStoredRank.lean
[smith]: Polytime2/Matrices/IntegerSmithReduction.lean
[bezout-tracking]: Polytime2/Matrices/IntegerBezoutTracking.lean
[stage]: Polytime2/Matrices/IntegerHermiteStage.lean
[fold]: Polytime2/Arrays/Fold.lean
[narrow]: Polytime2/Matrices/IntegerNarrow.lean
[workspace]: Polytime2/Matrices/HermiteWorkspace.lean
[stage-workspace]: Polytime2/Matrices/HermiteStageWorkspace.lean
[bezout]: Polytime2/Matrices/IntegerBezout.lean
[hermite-row]: Polytime2/Matrices/IntegerHermiteRow.lean
[sweep]: Polytime2/Matrices/HermiteSweepMath.lean
[coordinates]: Polytime2/Matrices/IntegerSystemCoordinates.lean

[computed-host]: Polytime2/Computation/ComputedHost.lean
[integer-rename]: Polytime2/Matrices/IntegerRename.lean

[records]: Polytime2/Computation/Records.lean
[record-arguments]: Polytime2/Computation/RecordArguments.lean
