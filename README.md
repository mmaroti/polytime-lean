# polytime

A Lean library for developing a reusable framework for polynomial-time
algorithms and their complexity certificates.

See [GOAL.md](GOAL.md) for the framework design and [EXAMPLES.md](EXAMPLES.md)
for the initial three targets and five additional examples with their
mathematical contracts.

The Lake package is named `polytime`; its Lean library, root module, and
namespace are named `Polytime1`. The project lives at the repository root and
provides a library without an executable.

## Setup and build

Install Lean through Elan, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
```

Lean and Mathlib are pinned to `v4.34.0`. The `lake-manifest.json`
records the resolved dependency revisions. Mathlib's cache command downloads
compiled artifacts to avoid rebuilding Mathlib from source.

For an existing checkout with its manifest, `lake exe cache get` followed by
`lake build` is sufficient; `lake update` resolves dependencies again.

Run `python3 scripts/check_lean.py --build` to check project headers, named scopes,
and proof placeholders before building. For a targeted build, add
`--target Polytime1.Examples.MatrixAccess`. These lightweight source checks
complement Lean's verification; omit `--build` to run only the source checks.

## Using the library

Within this project, or another Lake project that depends on `polytime`, use:

```lean
import Polytime1
```

The library currently provides:

- `Polytime1.Size`: finite contexts of named size parameters, arbitrary natural
  assignments and executable capacity expressions with derived polynomial witnesses.
- `Polytime1.Domain`: recursive Fixed, Product, Sum, and Power domains; their
  mathematical values, exact-width bit encodings, canonical decoders, and
  polynomial-size certificates. Fixed and Power views hide carrier casts;
  shared encoded-block lemmas handle lookup and replacement.
- `Polytime1.GaussJordan`: executable rectangular elimination, with proved
  reduced row-echelon form and an invertible row-transformation witness.
- `Polytime1.Realization` and `RealizationLoop`: composable mathematical
  contracts with relational representations, preserved caller context, and
  existential scratch. Guarded loops, traversals, searches, and folds hide controllers
  and runtime polynomial witnesses.
- `Polytime1.WhileMachine`: guarded tape loops with invariant, termination, and
  transition-bound proofs, exercised by a finite-controller counter loop.
- `Polytime1.FiniteTableMachine`: fixed operation tables with constant
  tape-transition bounds and canonical-codec correctness.
- `Polytime1.MatrixStorage`: indexed table operations with mathematical updates,
  existential scalar scratch, and a preserved caller suffix.
- `Polytime1.Examples.CatalogueMap`: fixed catalogue maps on active coordinates,
  including two calls sharing a frame, preserving active counts and inactive slots.
- `Polytime1.BinaryAddition`: exact addition in a runtime-width bit-pair buffer,
  with a final carry, linear tape cost, and preservation of both caller regions.
- `Polytime1.InPlaceTableMachine`: scalar-slot operations preserving neighboring
  regions, including multiplication by an adjacent runtime coefficient.
- `Polytime1.Examples.Matrices`: K-by-L matrices over a fixed finite carrier,
  including the field `ZMod 5`, with independent dimensions K and L.
- `Polytime1.Examples.MatrixAccess`: indexed scalar-entry lookup and writes
  with canonical encoding correctness and polynomial tape-transition bounds;
  reads can compute addresses from runtime row and column counters; reserved
  scratch is required.
- `Polytime1.Examples.MatrixWrite`: runtime row and column counters select a
  canonical entry update, preserving the replacement and restoring the header
  after clearing evaluator scratch, with a polynomial tape bound; reads, fixed
  scalar operations, and writes compose in one frame.
- `Polytime1.Examples.AddressPreparation`: binary increment and blank-window
  initialization, composed with unary address conversion and scalar lookup;
  retained evaluator fields survive the conversion and lookup. A bounded unary
  address and reserved scratch remain entry requirements. Initialization accepts
  consumed all-one counters as well as fresh blank windows.
- `Polytime1.RetainedLookupMachine` and `RetainedWriteMachine`: shared calls
  that compute addresses in reserved frames, preserving both caller regions and
  extra runtime counters.
- `Polytime1.HeaderReturnMachine`: restores a fixed counter header after access,
  erases evaluator scratch into an explicit blank margin, and preserves both
  caller regions, the scalar result, and the matrix suffix;
  one composition rule serves ordinary and saved-counter reads and writes.
- `Polytime1.HeaderIncrementMachine`: increments a selected unary counter using
  a reserved blank cell, preserving caller storage on both sides; entry updates compose
  with column-counter advancement and a polynomial tape bound.
- `Polytime1.HeaderGuardMachine`: compares bounded counters using one reserved
  result cell; consuming the result restores that cell and preserves caller storage.
- `Polytime1.HeaderResetMachine`: resets a selected unary counter, preserving
  preceding fields and following storage, with a polynomial tape bound.
- `Polytime1.HeaderMoveMachine`: relocates a runtime header field to the front,
  preserving the frame suffix, with a quadratic tape bound; moving the second
  field exchanges source and target row indices.
- `Polytime1.Examples.MatrixRowMap`: a complete guarded row traversal applies a
  fixed unary scalar operation, preserves other rows, and restores the header,
  with a polynomial tape bound; zero-column matrices are included.
- `Polytime1.Examples.MatrixRowScale`: one finite machine scales a row by a
  coefficient read from a leading scalar slot, with a polynomial bound uniform
  over runtime coefficients; the consumed slot is cleared and the column counter
  is reset to zero.
- `Polytime1.Examples.MatrixNormalizeRow`: reads and inverts a runtime pivot,
  copies its inverse to the coefficient input, and scales the row, with a
  polynomial tape bound; nonzero pivots become one and preserve row equivalence.
- `Polytime1.Examples.MatrixNormalizeRowSaved`: normalizes a runtime target
  pivot while retaining both row indices, the pivot column, and caller counters.
- `Polytime1.Examples.MatrixEntryCombine`: combines source and target entries in
  one column, updates the target, and restores both runtime row counters, with
  a polynomial tape bound. Paired read/write contracts retain both counters.
- `Polytime1.Examples.MatrixRowCombine`: a guarded traversal combines two
  runtime-selected rows entry by entry, preserving all other rows.
- `Polytime1.Examples.MatrixRowAdd`: adds a runtime multiple of the source row
  to the target, resets the column counter, and preserves row equivalence for
  distinct rows, with a polynomial tape bound uniform over coefficients.
- `Polytime1.Examples.MatrixRowSwap`: swaps distinct runtime-selected rows
  through three row traversals, restoring the counters and preserving row
  equivalence, with a polynomial tape bound; a guarded version includes identical
  rows for ordered runtime indices; both variants preserve extra caller counters.
- `Polytime1.Examples.MatrixClearRow`: reads and negates the target entry,
  then adds that runtime multiple of the source row. A normalized source pivot
  clears the target entry; distinct rows preserve row equivalence.
- `Polytime1.Examples.MatrixClearRowSaved`: clears a target row while preserving
  a separate runtime pivot-column counter. `HeaderColumnSwapMachine` exchanges
  the saved and traversal columns with a quadratic tape bound.
- `Polytime1.NamedHeader`: derives Gauss–Jordan header relocations from named
  layouts.
- `Polytime1.HeaderMoves`: compiles fixed header relocations with a quadratic
  tape bound, including the guard and row-update layouts for column elimination.
- `Polytime1.Examples.MatrixClearTargetStep`: clears one target row, retains the
  loop limit and pivot column, restores the guard layout, and advances the target.
- `Polytime1.Examples.MatrixClearRange` and `MatrixClearColumn`: guarded row
  intervals compose into complete column clearing, agreeing with the mathematical
  operation and preserving row equivalence, with a polynomial tape bound.
- `Polytime1.Examples.MatrixPivotStep`: composes ordered row swapping, pivot
  normalization, and complete column clearing, agrees with the mathematical
  pivot step, and proves row equivalence and a polynomial tape bound. Its restoring
  variant returns the four-counter frame and advances the next pivot row.
- `Polytime1.Examples.MatrixEntryTest` and `MatrixPivotGuard`: return a scalar
  predicate before the restored header and short-circuit pivot testing at the
  row-count sentinel, with polynomial tape bounds.
- `Polytime1.Examples.MatrixPivotSearch`: a guarded row traversal returns the
  first eligible nonzero entry or the row-count sentinel, agrees with the
  mathematical `findPivot`, and preserves the matrix and additional caller
  counters with a polynomial tape bound. `MatrixSearch` supplies its mathematical
  contract through the shared search rule, with existential scalar scratch.
- `Polytime1.Examples.MatrixPivotDispatch` and `MatrixColumnStep`: pivot search
  composes with elimination or a no-pivot branch, agrees with mathematical
  `columnStep`, and restores the four-counter frame with a polynomial tape bound,
  including zero-row matrices and exhausted pivot rows.
- `Polytime1.Examples.MatrixEliminate`: a guarded column traversal computes
  complete Gauss–Jordan elimination in a prepared frame, with reduced row-echelon
  form, an invertible row-transformation witness, and a polynomial tape bound.
  Its algorithm-level contract uses a mathematical fold; `MatrixTraversal`
  hides tape layouts and scalar scratch. Zero-row and zero-column matrices are included.
- `Polytime1.Examples.MatrixPrepareFrame`: constructs the complete elimination
  frame from the runtime dimension header and input bits, with a polynomial tape
  bound and no supplied scratch. `HeaderInsertMachine` formats its scalar slot
  and counter delimiter; `FrameExtractMachine` erases the working storage.
- `Polytime1.Examples.GaussJordan.realizes`: the complete external theorem
  composes preparation, elimination, and extraction into one finite controller.
  It returns canonical matrix bits, preserves a trailing caller suffix, and
  proves reduced row-echelon form, row equivalence, and a polynomial transition
  bound in both dimensions.
- `MatrixFrameAccess`, `MatrixFrameWrite`, `MatrixFrameCombine`, and
  `MatrixFrameRowCombine` retain additional polynomially bounded header counters.
  A complete two-row traversal now preserves a separate runtime pivot-column
  counter; the original paired APIs use the same proofs with no extra counters.
- Complete runtime matrix-entry reads accept the previous output and counter
  windows; two consecutive reads have a composed polynomial tape bound.
- `Polytime1.Examples.MatrixAddress`: runtime row-major address calculation,
  with a finite controller and a polynomial bound in matrix dimensions.
- `Polytime1.Examples.Domains`: checked boundary cases and binary layouts.
- `Polytime1.Tuple`: Boolean tuple lookup/update and bounded natural counters
  with canonical padded binary representations.
- `Polytime1.Integer`: unsigned and signed binary presentations and exact
  bounded arithmetic with proved output capacities and a Euclidean division
  contract.
- `Polytime1.SizeMachine`: constant allocation, field copying, and unary
  addition with reserved blank cells and preservation of both caller regions.
- `Polytime1.UnaryMachine`: unary multiplication, optionally plus one, with
  finite reserved workspace and preservation of both caller regions.
- `Polytime1.SizeFrame`: reserved-frame evaluation of every size expression;
  composition hides workspace bounds and preserves both caller regions.
- `Polytime1.SizeEvaluation`: finite-controller tape realization of every size
  expression, with polynomial transition bounds and preservation of the size
  header and input.
- `Polytime1.Frame`: executable size-header parsing and frame preparation, with
  input preservation and polynomial storage proofs.
- `Polytime1.Examples.TupleLookup`: a complete lookup/update tape example,
  including frame preparation and a quadratic machine-runtime proof.
- `Polytime1.Examples.TupleComposition`: two indexed exchanges in one prepared
  frame, with result transfer, preservation contracts, and a quadratic runtime proof.

`DomainExpression` directly defines its mathematical values (`Value`), exact bit
width (`bitWidth`), codecs (`encode` and `decode`), and polynomial upper bound
(`sizeBound`) by recursion on the expression. The size-bound proof is separate
from the width computation.

Each constructor has one canonical encoding through `BitCodec`, directly to and
from `BitVec` of the exact width. Fixed domains retain their `FixedPresentation`
to identify mathematical values with binary labels.

For example:

```lean
import Polytime1

open Polytime1.Examples.Matrices

example : (domain field5).bitWidth (assignment 2 3) = 18 := by
  simp

example : ∃ p : Polytime1.SizePolynomial context, ∀ a,
    (domain field5).bitWidth a ≤ p.eval a :=
  polynomial_size field5
```

`SizeContext` contains the type of parameter names and a `Fintype` instance.
`SizeAssignment ctx` is a map from those names to natural numbers.
`SizeExpression ctx` is executable syntax for constants, parameters, addition,
multiplication, and fixed natural powers. `SizePolynomial ctx` supplies the
derived Mathlib polynomial witnesses. All names have the same
role: a context may name N, K, and L, with no distinguished N and no imposed
bounds between their values. Power exponents may be any such polynomial,
including constants.

A complete assignment determines the exact bit width. The library derives a
polynomial upper bound in all declared parameters, valid for every assignment.
For example, K-by-L matrices over `ZMod 5` need exactly `3*K*L` bits.
Algorithm certificates measure runtime in one plus the sum of size parameters.

The size parameters are external indices, not fields encoded in each value.
Encodings concatenate blocks in order from low to high bits; alternatives use
a tag and zero padding.
Unused labels and noncanonical padding are rejected.

Capacity expressions evaluate directly; their derived polynomials agree with
that evaluation. Exact domain widths are executable, including `max` for sums.
The tuple example uses Mathlib's deterministic `TM0`, with 32 states and eight
symbols independent of N. Its framed input has a unary size header, replacement
bit, N-bit binary index, field separator, dense tuple bits, and end delimiter.
It prepares its own cursor and returns the selected old bit followed by the
updated tuple within `32 * (N + 1)^2` tape transitions. Zero length admits no
valid index. The composition example transfers the first selected bit into the
second exchange while preserving the first updated tuple and surrounding storage,
within `384 * (K + L + 1)^2` transitions. A general program language and compiler
remain future work.

`Frame.prepare` reads a self-delimiting unary size header followed by canonical
input bits, retains the header, and reserves blank scratch slots of their exact
widths. Its correctness and polynomial storage bound are proved. The generic
preparer and integer arithmetic still require tape-runtime realization proofs;
they are not registered as certified program primitives. Integer storage is
bounded by bit length, rather than numeric magnitude.
See [GOAL.md](GOAL.md) for the broader specification.

The projects under `temp/` are reference material only. They are excluded from
version control and are not dependencies of this library.

## License

Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>.
Licensed under the [Apache License, Version 2.0](LICENSE).
