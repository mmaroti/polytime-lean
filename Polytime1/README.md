# Polytime1

A single-tape implementation of polynomial-time algorithms using Mathlib's
`TM0`, canonical bounded-domain encodings, and prepared working frames.

Build from the repository root with `lake build Polytime1`.
Use `import Polytime1`. See [GOAL.md](../GOAL.md) for the shared specification
and [EXAMPLES.md](../EXAMPLES.md) for target algorithms and building-block
libraries.

## Implemented and proved

- `Polytime1.Size`: finite contexts of named size parameters, arbitrary natural
  assignments and executable capacity expressions with derived polynomial
  witnesses.
- `Polytime1.Domain`: recursive Fixed, Product, Sum, and Power domains; their
  mathematical values, exact-width bit encodings, canonical decoders, and
  polynomial-size certificates. Fixed and Power views hide carrier casts;
  shared encoded-block lemmas handle lookup and replacement.
- `Polytime1.GaussJordan`: executable rectangular elimination, with proved
  reduced row-echelon form and an invertible row-transformation witness.
- `Polytime1.Realization` and `RealizationLoop`: composable mathematical
  contracts with relational representations, preserved caller context, and
  existential scratch. Guarded loops, traversals, searches, and folds hide
  controllers and runtime polynomial witnesses.
- `Polytime1.WhileMachine`: guarded tape loops with invariant, termination, and
  transition-bound proofs, exercised by a finite-controller counter loop.
- `Polytime1.FiniteTableMachine`: fixed operation tables with constant
  tape-transition bounds and canonical-codec correctness.
- `Polytime1.MatrixStorage`: indexed table operations with mathematical updates,
  existential scalar scratch, and a preserved caller suffix.
- `Polytime1.Examples.CatalogueMap`: fixed catalogue maps on active coordinates,
  including two calls sharing a frame, preserving active counts and inactive
  slots.
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
  a reserved blank cell, preserving caller storage on both sides; entry updates
  compose with column-counter advancement and a polynomial tape bound.
- `Polytime1.HeaderGuardMachine`: compares bounded counters using one reserved
  result cell; consuming the result restores that cell and preserves caller
  storage.
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
  equivalence, with a polynomial tape bound; a guarded version includes
  identical rows for ordered runtime indices; both variants preserve extra
  caller counters.
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
  loop limit and pivot column, restores the guard layout, and advances the
  target.
- `Polytime1.Examples.MatrixClearRange` and `MatrixClearColumn`: guarded row
  intervals compose into complete column clearing, agreeing with the
  mathematical operation and preserving row equivalence, with a polynomial tape
  bound.
- `Polytime1.Examples.MatrixPivotStep`: composes ordered row swapping, pivot
  normalization, and complete column clearing, agrees with the mathematical
  pivot step, and proves row equivalence and a polynomial tape bound. Its
  restoring variant returns the four-counter frame and advances the next pivot
  row.
- `Polytime1.Examples.MatrixEntryTest` and `MatrixPivotGuard`: return a scalar
  predicate before the restored header and short-circuit pivot testing at the
  row-count sentinel, with polynomial tape bounds.
- `Polytime1.Examples.MatrixPivotSearch`: a guarded row traversal returns the
  first eligible nonzero entry or the row-count sentinel, agrees with the
  mathematical `findPivot`, and preserves the matrix and additional caller
  counters with a polynomial tape bound. `MatrixSearch` supplies its
  mathematical contract through the shared search rule, with existential scalar
  scratch.
- `Polytime1.Examples.MatrixPivotDispatch` and `MatrixColumnStep`: pivot search
  composes with elimination or a no-pivot branch, agrees with mathematical
  `columnStep`, and restores the four-counter frame with a polynomial tape
  bound, including zero-row matrices and exhausted pivot rows.
- `Polytime1.Examples.MatrixEliminate`: a guarded column traversal computes
  complete Gauss–Jordan elimination in a prepared frame, with reduced
  row-echelon form, an invertible row-transformation witness, and a polynomial
  tape bound. Its algorithm-level contract uses a mathematical fold;
  `MatrixTraversal` hides tape layouts and scalar scratch. Zero-row and
  zero-column matrices are included.
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
  `MatrixFrameRowCombine` retain additional polynomially bounded header
  counters. A complete two-row traversal now preserves a separate runtime
  pivot-column counter; the original paired APIs use the same proofs with no
  extra counters.
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
  frame, with result transfer, preservation contracts, and a quadratic runtime
  proof.

## Domains and encodings

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
second exchange while preserving the first updated tuple and surrounding
storage, within `384 * (K + L + 1)^2` transitions. A general program language
and compiler remain future work.

`Frame.prepare` reads a self-delimiting unary size header followed by canonical
input bits, retains the header, and reserves blank scratch slots of their exact
widths. Its correctness and polynomial storage bound are proved. The generic
preparer and integer arithmetic still require tape-runtime realization proofs;
they are not registered as certified program primitives. Integer storage is
bounded by bit length, rather than numeric magnitude.
See [GOAL.md](../GOAL.md) for the shared specification.

## Working-frame design

General frame preparation and compilation remain goals; the routines above
implement particular instances of this design.

A composite program may use one fixed domain expression as a working frame,
with slots for loop counters, intermediate results, and subprogram arguments
and results. Fixing P, S, and a complete size assignment determines exact slot
widths and offsets. The frame expression is fixed across runs of `P_S`, while
its physical dimensions vary with the assignment. Auxiliary navigation and
scratch storage must also have polynomial bounds. Bounded-value invariants hold
at program-operation boundaries; physical scratch and partially written slots
need not encode complete values. Vacant storage uses explicit tags or physical
initialization invariants, without assuming default elements or adding errors.

Use one fixed finite tape alphabet for this implementation, independent of P, S,
and the size assignment. A possible symbol combines a data component (`blank`,
`zero`, or `one`) with a fixed collection of marker flags. Flags may coexist on
a cell and identify boundaries, source and destination cursors, or positions
needed by counter routines. Current routines use `TupleMachine.Symbol`, an
eight-symbol alphabet; generalized marker flags remain a design option. Do not
introduce one alphabet symbol per slot or input position. Slot numbers, lengths,
offsets, and saved navigation information can be ordinary tape data.

The finite controller may depend on P and S, but not on the size assignment.
Its states describe phases such as decrementing a counter, finding a cursor,
advancing it, or returning to scratch. It knows the specialized domain
expressions and constants; assignment-dependent widths and offsets are
computed and stored on tape. Growing indices and whole tuples must not be
stored in an input-size-dependent collection of controller states.

An indexed lookup can preserve the index by copying it to a scratch counter,
place a cursor at the array start, and repeatedly decrement the counter and
advance the cursor by one element. A varying element width can itself be a
tape-stored counter, or the routine can compute and follow a bit offset.
Binary decrement uses a finite borrow-handling controller. Unary routing
scratch is also permitted when the represented offset is polynomially
bounded; short binary encodings alone would not justify this conversion for
arbitrarily large numeric values. Index validity belongs to the lookup's
mathematical hypothesis.

Copying between disjoint slots can shuttle between source and destination
cursors, remembering one bit in the controller, writing it, and advancing
both cursors until the stored length is exhausted. Overlapping copies need a
proved direction or scratch-buffer strategy. Navigation, copying, updating,
scratch management, and marker restoration require reusable correctness and
polynomial-cost proofs. Repeated scans need not give constant-time access;
polynomial overhead in a polynomially bounded frame is sufficient.

Canonical `BitVec` value encodings remain separate from the machine's working
tape layout. Marker tracks, delimiters, frame metadata, and scratch space are
initialized and managed by the realization layer, with their costs included
in its proof. Program authors use mathematical lookup, update, and copying
operations and supply shape invariants, without manipulating tape markers.

Separate a bare algorithm operating on an already prepared working frame from
the external machine wrapper that prepares that frame. The bare algorithm's
entry contract specifies valid boundaries and navigation metadata, its assigned
region and scratch capacity, input slots containing valid representations,
and an initial head position. Its exit contract specifies the output slots,
preservation of caller-owned data and metadata outside its assigned region,
and the final head position and marker configuration needed by subsequent
routines. Navigation invariants identify the current region and support
locating positions within it through reusable certified routines.

Mathematical lookup preserves its arguments; physical routines may consume
scratch copies or overwrite slots. The realization must preserve source values
needed afterward, with copying and preservation justified by concrete subroutine
contracts. No ownership type system is required initially. Tape navigation and
step-count proofs should be reused through these contracts, with polynomial
bounds in the enclosing frame size and explicit runtime polynomials kept
internal.

A composite frame reserves regions for its subroutines. Calls copy arguments
into the callee's designated slots, execute the callee within its assigned
region, and copy results into the caller's destination slots. Region
identifiers, offsets, and saved navigation information are ordinary metadata
over the same universal alphabet. Loop iterations can reuse prepared regions.
With the initial finite call structure and no recursive self-calls, capacities
for the whole frame can be determined in advance from P, S, and the size
assignment, including fixed polynomial reparameterizations at call sites.
Capacity is reserved storage, not the amount of data actively used during a
run. Composition proves entry/exit compatibility and preservation of frame
invariants; navigation and copying costs remain included in the library's
polynomial realization proofs.

## Limits and next steps

`Algorithm` currently records specialization requirements, size contexts, and
input/output domains; it does not yet specify execution. General program
notation, polynomial reparameterization of subprogram calls, and the generic
frame preparer's tape realization remain future work.

The shared `Realization` contracts, derived search/traversal/fold rules, named
headers, active catalogue-map example, and binary addition are implemented.
The Gauss–Jordan outer traversal now uses a mathematical fold with hidden
scratch, controllers, and runtime witnesses. Extend this interface to the
lower-level matrix routines before adding another large example:

- Consolidate ordinary and saved-counter routines behind shared contracts.
- Prove regional calling-convention adapters where routines still require a
  blank left side rather than arbitrary preserved caller storage.
- Keep positional header bookkeeping inside named-layout helpers.
- Implement certified binary multiplication, division, remainder, and gcd with
  runtime bit capacities. Existing integer specifications prove mathematical
  correctness and output capacities, not tape runtime.

The catalogue-map example is a small storage operation, not the complete SMP
preparation algorithm. Smith normal form and the other target algorithms in
EXAMPLES.md remain to be implemented.
