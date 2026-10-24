# Matrices and row operations

[Project guide](../README.md) · [Arrays](../Arrays/README.md)

Public carriers are ordinary matrices or finite row functions. The codecs reuse
row-major array storage. Start with [Operations.lean](Operations.lean) for
coordinate-pair access, or [EntryOperations.lean](EntryOperations.lean) for
separate row and column arguments.

For intermediate operations, transfer preservation and entry properties using
the exact `_correct` or `_compute` theorem and the corresponding mathematical
`IntegerMatrix` theorem. For example, combine
`integerBezoutRowsWithLeft_compute` with `bezoutRowsWithLeft_equation` from
[BezoutTrackingMath.lean](BezoutTrackingMath.lean).

## Choose an interface

| Need | Source |
| --- | --- |
| Lookup/update by coordinate pair | [Operations.lean][op] |
| Entry access and replacement using separate coordinates | [entry] |
| A specialization-fixed row transformation | [RowsOperations.lean][rows] |
| Scalar field identities used by row algorithms | [FieldRow.lean][field] |
| Integer row/column pair action with separate widths | [pair] |
| Runtime integer row/column addition | [IntegerOperations.lean][integer] |
| Map or tabulate a matrix | [Map.lean][map], [tabulate] |
| Transpose a matrix | [Transpose.lean][transpose] |
| Construct an integer identity matrix | [Identity.lean][identity] |
| Negate an integer row or column | [IntegerNegate.lean][negate] |
| Euclidean remainder reduction with basis tracking | [euclidean] |
| Reduce a positive-pivot integer row | [row reduction] |
| Reduce a positive-pivot integer column | [IntegerHermiteColumn.lean][column] |
| Interleave Hermite elimination and remainder normalization | [stage] |
| Preserve minors through incoming-row stages | [incoming minors] |
| Derive original witnesses and pivot-block widths | [block bounds] |
| Bound supported blocks by original minors | [MinorBoundsMath.lean][minor] |
| Runtime row/column Bézout elimination | [IntegerBezout.lean][elim] |
| Accumulate integer row/column transformations | [tracking] |
| Bounded determinant-one Bézout elimination | [BezoutMath.lean][bezout] |
| Certified two-entry diagonal cleanup with transformations | [pair machine] |
| Normalize a pair and update both accumulated bases | [basis step] |
| Select a repair and update bases within a fixed workspace | [selected step] |
| Store repaired entries and perform the guarded state update | [cleanup step] |
| Normalize a positive bounded natural diagonal | [positive cleanup] |
| Repeat cleanup with a fixed polynomial workspace | [controller] |
| Narrow integer matrices after proving entry bounds | [narrow] |
| Find an adjacent divisibility failure | [search], [signed search] |
| Repair coordinates or stopping guard | [repair], [chain] |
| Mathematical diagonal divisibility cleanup | [cleanup], [pair cleanup] |
| Accumulated cleanup bases and polynomial bounds | [cleanup bases], [bounds] |
| Construct a rectangular integer diagonal matrix | [rectangular matrix] |
| Extend an active basis by identity | [extend basis] |
| Clean up an active rectangular diagonal | [rectangular cleanup] |
| Full Smith reduction with both transformation matrices | [runtime Smith] |
| Decide integer feasibility or return a solution | [feasibility], [solve] |
| Cyclic span decisions and coefficient witnesses | [cyclic span] |
| Compute actual cyclic/free quotient coordinates | [system quotient] |
| Smith contract and integer feasibility criterion | [SmithMath.lean][smith] |
| Quotient coordinates and cokernel | [SmithCoordinates.lean][quot] |
| Reduction from cyclic-coordinate membership | [AugmentedMath.lean][aug] |
| Mathematical row transformations | [RowsMath.lean](RowsMath.lean) |

[op]: Operations.lean
[entry]: EntryOperations.lean
[rows]: RowsOperations.lean
[field]: FieldRow.lean
[integer]: IntegerOperations.lean
[pair]: IntegerRowPair.lean
[map]: Map.lean
[tabulate]: Tabulate.lean
[transpose]: Transpose.lean
[smith]: SmithMath.lean
[bezout]: BezoutMath.lean
[elim]: IntegerBezout.lean
[column]: IntegerHermiteColumn.lean
[row reduction]: IntegerHermiteRow.lean
[stage]: HermiteStageMath.lean
[minor]: MinorBoundsMath.lean
[block bounds]: HermiteBlockBoundsMath.lean
[incoming minors]: HermiteIncomingMath.lean
[tracking]: IntegerBezoutTracking.lean
[euclidean]: IntegerEuclideanReduction.lean
[cleanup]: DiagonalCleanupMath.lean
[pair cleanup]: DiagonalPairMath.lean
[pair machine]: IntegerDiagonalPair.lean
[basis step]: DiagonalBasisStep.lean
[narrow]: IntegerNarrow.lean
[basis narrow]: DiagonalBasisNarrow.lean
[selected step]: DiagonalSelectedRepair.lean
[cleanup step]: DiagonalCleanupStep.lean
[controller]: DiagonalCleanupController.lean
[positive cleanup]: PositiveDiagonalCleanup.lean
[search]: NaturalDiagonalSearch.lean
[repair]: DiagonalRepairCoordinates.lean
[chain]: DiagonalChain.lean
[signed search]: DiagonalSearch.lean
[cleanup bases]: DiagonalTrackingMath.lean
[bounds]: DiagonalBoundsMath.lean
[rectangular]: RectangularDiagonalMath.lean
[extend basis]: ExtendIntegerBasis.lean
[rectangular cleanup]: RectangularDiagonalCleanup.lean
[rectangular matrix]: IntegerRectangularDiagonal.lean
[identity]: Identity.lean
[negate]: IntegerNegate.lean
[aug]: AugmentedMath.lean
[quot]: SmithCoordinates.lean

Public entry and row operations expose row and column counts as sizes. Their
coordinates express mathematical admissibility; extra counter capacity and
unary headers are prepared internally. Replacement returns a separate matrix.
Row transformations take ordinary scalar functions fixed by specialization.
Read the operation's contract before assuming behavior for coincident rows.

## Composition and examples

Entry access composes the array access rules for rows and entries. Reuse this
route when adding a matrix operation rather than proving another flattened
address machine. [MatrixAccess.lean](../Examples/MatrixAccess.lean) exercises
matrix access; [MatrixRows.lean](../Examples/MatrixRows.lean) and
[MatrixRowField.lean](../Examples/MatrixRowField.lean) show row transformations.

For elimination, continue with the [Gauss–Jordan
guide](../GaussJordan/README.md).
Integer row and column addition use bounded ordinary integer matrices and
runtime integer coefficients; sufficient output width is derived internally.
[IntegerRename.lean](IntegerRename.lean) views host matrices at renamed
polynomial dimensions for computed-size calls, preserving canonical bits.
Its inverse returns matrices to the original carrier with a realizability
certificate; the shared carrier equivalence proves exact round trips.
[IntegerMatrices.lean](../Examples/IntegerMatrices.lean) includes signed,
singular, rectangular, and empty examples and standalone TM0 certificates.
[MatrixInitialization.lean](../Examples/MatrixInitialization.lean) checks basis
initialization, sign changes, and accumulated Bézout steps, including empty
and one-by-one matrices. [IntegerBezoutTracking.lean][tracking] retains one
coefficient result and applies it to the current matrix and its accumulated
basis. Row and column steps preserve the transformation equation and
unimodularity, with derived local output widths and TM0 certificates. These
local bounds do not yet establish polynomial bounds for complete sweeps.
[Euclidean remainder reductions][euclidean] reuse a single quotient for the
working matrix and its basis. They preserve the presentation and unimodularity;
divisible entries vanish without changing the pivot row or column.
[EuclideanReduction.lean](../Examples/EuclideanReduction.lean) checks negative
entries, exact divisibility, column orientation, and earlier zero columns.
[Fixed-pivot sweeps](EuclideanSweepMath.lean) have a closed formula,
presentation and unimodularity proofs, and additive width bounds independent
of the number of distinct targets. They are mathematical constituents of a
Hermite sweep.
[Changing-pivot column sweeps](HermiteStepMath.lean) clear the selected column
and retain a positive pivot and the actual unimodular left basis. Divisible
entries use quotient cancellation; other steps halve the pivot. The number of
actual gcd changes is less than the initial pivot bit width.
[Column-sweep bounds](HermiteColumnBounds.lean) add at most `n(2w+2)` bits
to the original matrix and basis widths for `n` distinct targets and original
column width `w`, including every intermediate suffix sweep.
[The certified Hermite row step](IntegerHermiteStep.lean) selects quotient
cancellation or Bézout elimination at runtime, retaining both actual matrices
and a TM0 certificate; its mathematical output and basis equation are proved.
[Fixed-workspace updates](HermiteWorkspace.lean) narrow both matrices after
using the logical prefix bound. [Pair narrowing](IntegerPairNarrow.lean) is
shared with diagonal cleanup. [Canonical traversal prefixes][column traversal]
match an increasing array fold that skips the source row, with inherited
zero-entry and polynomial prefix bounds. [The complete column traversal][column]
now composes these certified operations and prepares its workspace internally.
Its only input precondition is a positive selected pivot;
[IntegerHermiteColumn.lean](../Examples/IntegerHermiteColumn.lean) checks a
rectangular middle-source reduction, a one-row source skip, and the dual
[row reduction] with the actual right basis.
[Pair transposition][pair transpose] is shared with Bézout and remainder
tracking. Use the mathematical protected-block theorems in
[HermiteProtectedMath.lean](HermiteProtectedMath.lean) to retain completed
blocks.
[HermiteProtected.lean](../Examples/HermiteProtected.lean) checks an earlier
diagonal entry and a nonidentity protected basis row.
Hermite sweeps use the mathematical [interleaved stage][stage], reducing earlier
entries after each incoming-row elimination.
The [complete runtime stage][runtime stage] now handles any admissible array
of earlier rows, including an empty array, with exact mathematical output,
canonical remainders, basis preservation, realizability, and a standalone TM0
certificate. Its [fixed-workspace controller][stage controller] proves every
prefix fits `4 * w + 3` bits, with preparation and traversal costs included.
Runtime [prefix guards][runtime prefix] and selected stage updates keep storage
fixed while allowing inactive tokens to bypass stage preconditions.
The [runtime prefix stage][prefix stage] now accepts an ordinary prefix length
and full row array, with no admissibility requirement on its inactive suffix.
Preparation, selected updates, and skipped states have realizability and TM0
certificates.
[HermiteStage.lean](../Examples/HermiteStage.lean) checks its remainders, prior
columns, basis equation, and separate width bounds. [Minor bounds][minor]
factor supported reduced blocks through original minors, with polynomial
determinant widths. The complete runtime schedule is implemented below.
[Fixed-pivot normalization](EuclideanSweepMath.lean) also separates the source
row width: a source of width `S` and targets of width `H` need `H + S + 1`
bits, even when quotient widths grow with `H`. The full sweep must establish
the small-source invariant before using this estimate.
[Incoming-row prefixes][incoming minors] now retain one input minor through
successive stages and preserve unvisited matrix and basis rows. Positive
echelon input pivots yield positive visited pivots, cleared incoming entries,
and canonical remainders above them, with zeros below each visited pivot.
Completed prefixes derive their extended block triangularity. Truncated
minors containing only visited pivots and the incoming row bound future
incoming entries at intermediate prefixes, without a caller-supplied shape
witness. The completed-prefix bound specializes this result.
[Incoming-prefix widths](HermiteIncomingBounds.lean) derive uniform incoming-row
bounds by constructing truncated minors. Small-pair elimination and
small-source normalization then give polynomial matrix and actual basis
widths for one incoming traversal from its original input width.
[Pivot-block extension](HermiteExtendMath.lean) normalizes earlier rows against
a positive residual pivot, preserving old pivot columns and extending the
positive, triangular, reduced block.
[HermiteStage.lean](../Examples/HermiteStage.lean) checks actual basis tracking
and the original-input width bound after rank growth. Residual-pivot selection
and sign normalization are available in
[HermitePivotMath.lean](HermitePivotMath.lean):
the shared finite-array search returns a new nonzero coordinate or certifies
a zero residual row, and sign-aware extension retains the normalized block,
actual basis, and polynomial width bounds. [HermitePivot.lean][pivot examples]
checks negative pivots, rank zero, and zero residuals, including no columns.
[Runtime residual search][residual runtime] and
[sign normalization][sign runtime] have realizability and TM0 certificates.
Search returns an optional nonzero column or certifies a zero row. Sign
normalization preserves both matrix widths and the actual basis equation.
[One incoming stage](HermiteIncomingStage.lean) composes coordinate lookup
and prefix normalization, preserving the actual presentation and basis. See
[its example](../Examples/HermiteIncomingStage.lean) for the TM0 certificate.
[Fixed-workspace updates](HermiteIncomingWorkspace.lean) reuse pair narrowing;
the original-input bounds cover both matrices at every incoming prefix. The
[incoming controller](HermiteIncomingController.lean) now certifies the full
traversal and actual bases; [its examples][incoming controller examples] check
a gcd update and zero pivots. [Original-width incoming reduction][incoming]
prepares storage internally and certifies positive pivots and incoming zeros;
see [its example][incoming example].
[Complete runtime insertion](IntegerHermiteInsertRow.lean) now composes this
with residual finishing and agrees with the mathematical insertion.
[Its examples][runtime insertion example] check both rank outcomes with zero
or one old pivot and include a TM0 certificate.
[Mathematical row insertion](HermiteInsertMath.lean) now combines the incoming
traversal, residual search, and sign-aware extension. It retains the actual
presentation and basis, derives polynomial output widths, and returns either
a zero residual or a new normalized pivot. Unselected matrix and basis rows
remain unchanged. [HermiteInsert.lean][insert examples] checks independent and
dependent rows, unselected rows, and no columns. Runtime realization remains
open.
[Processed-prefix bounds](HermiteProcessedMath.lean) restrict the presentation
using preserved basis support and recover unimodularity through the existing
identity extension. They bound normalized processed rows in the original input
width even when future input rows are nonzero;
[HermiteProcessed.lean][processed examples] checks this before the final row.
Transition lemmas now preserve basis support, future identity rows, and
processed zero rows across the next insertion, including either rank outcome.
[Outer row traversal](HermiteSweepMath.lean) now iterates over all input rows,
carrying rank, embeddings, normalization, presentation, and support proofs.
Original-input matrix and actual basis widths are polynomial at every outer
prefix. [HermiteSweep.lean][sweep examples] checks full rank, singular inputs
with inactive leading rows, and zero or empty dimensions.
[Compact row and column normalization](CompactHermiteMath.lean) now moves the
pivots into the leading block, returns both actual bases, and retains polynomial
entry widths. [Pivot permutations](PivotPermutationMath.lean) use deterministic
swaps; [permutation tracking](PermutationTrackingMath.lean) preserves the full
presentation. [CompactHermite.lean][compact examples] checks nontrivial left
and right permutations, rectangular column normalization, and empty dimensions.
[PivotPermutation.lean](PivotPermutation.lean) now realizes the deterministic
pivot-permutation image tables by canonical coordinate enumeration, two
lookups, pointwise swaps, and a certified fold. Its full table equals the
mathematical permutation and is bijective. [Its examples][permutation example]
check noncanonical pivots and empty selections.
[IntegerGather.lean](IntegerGather.lean) realizes finite-map matrix selection.
[IntegerReindex.lean](IntegerReindex.lean) composes three gathers for the matrix
and both bases, preserving their independent widths and, for permutations,
the presentation and unimodularity.
[IntegerCompactSelected.lean](IntegerCompactSelected.lean) composes permutation
tables and this action for injective pivot arrays, with exact mathematical
agreement and preservation of the presentation and both unit determinants.
[IntegerCompactAtSize.lean](IntegerCompactAtSize.lean) connects metadata to
this operation at a named rank. Its only precondition is rank equality; the
coordinate reader preserves injectivity and canonical encodings.
[IntegerCompactStoredRank.lean](IntegerCompactStoredRank.lean) decodes the
rank, prepares the computed-size frame, and returns the three original host
matrices without a caller-supplied rank. Realizability and a
[standalone TM0 certificate](../Examples/IntegerCompactStoredRank.lean) are
checked, together with exact host-level correctness and presentation
preservation. [IntegerCompactHermiteRows.lean](IntegerCompactHermiteRows.lean)
composes the full sweep and automatic compaction. Its mathematical output is
the rank, compact matrix, and both actual bases; realizability, TM0, exact
agreement, and the compact-row specification are checked.
[IntegerCompactHermiteColumns.lean](IntegerCompactHermiteColumns.lean) realizes
the transpose-dual column pass, exchanging both bases, with exact agreement,
the full specification, and TM0 certification. Initial stabilization and the
alternating loop use both accumulated bases. Initial stabilization is now
realized by
[IntegerCompactHermiteInitial.lean](IntegerCompactHermiteInitial.lean),
with exact agreement, presentation, unimodularity, inactive strips, rank
equality, and a standalone TM0 certificate.
[IntegerIsDiagonal.lean](IntegerIsDiagonal.lean) realizes the
exact diagonal stopping test. Empty matrices and
negative off-diagonal entries are checked in
[the guard examples](../Examples/IntegerIsDiagonal.lean).
[IntegerHermiteAlternatingStep.lean](IntegerHermiteAlternatingStep.lean)
composes the row sweep, guard, and optional transpose-dual sweep, with exact
agreement, actual bases, preservation, triangularity, and TM0 certification.
[HermiteAlternatingWorkspace.lean](HermiteAlternatingWorkspace.lean) resizes
all three outputs at a common determinant bound. Its public wrapper derives
the common width internally, requiring
only positive lower triangular input. Exact agreement, realizability, and TM0
certification are checked. The mathematical forward update now agrees with
the recursive run, including both accumulated bases, and every prefix fits
one total-budget workspace.
[HermiteAlternatingAdvance.lean](HermiteAlternatingAdvance.lean) realizes the
fixed-width forward update, including stopping, both basis products, and
resizing. Exact agreement and TM0 certification are checked.
[IntegerBasisCompose.lean](IntegerBasisCompose.lean) shares basis accumulation
with initial stabilization.
[HermiteAlternatingController.lean](HermiteAlternatingController.lean) realizes
the complete bounded fold with exact recursive-run agreement.
[IntegerHermiteDiagonalize.lean](IntegerHermiteDiagonalize.lean) derives all
storage and the polynomial pair budget from positive lower triangular input.
The diagonal output retains both bases and the presentation, with realizability
and TM0 certification. Zero budget and empty dimensions are checked in
[the runtime examples](../Examples/IntegerHermiteDiagonalize.lean).
[IntegerLeadingBlock.lean](IntegerLeadingBlock.lean) extracts a leading square
block without changing entry width and composes square diagonalization under
mathematical rank and active-block assumptions. Realizability, TM0, signed
rectangular extraction, and rank-zero admissibility are checked in
[the block examples](../Examples/IntegerLeadingBlock.lean).
[IntegerRectangularHermite.lean](IntegerRectangularHermite.lean) reads the
square
diagonal and extends both actual bases, with exact agreement, presentation
preservation, realizability, and TM0. Its
[examples](../Examples/IntegerRectangularHermite.lean) check rank-zero
admissibility. [RectangularPresentation.lean](RectangularPresentation.lean)
shares rectangular matrix construction and both extensions with cleanup.
[IntegerRectangularHermiteAtRank.lean](IntegerRectangularHermiteAtRank.lean)
connects extraction and rectangular reduction, resizing all three full matrices
to one host-row/input-width capacity independent of active rank. Exact
agreement, supported-input presentation preservation, realizability, and TM0
are checked.
[IntegerRectangularHermiteAtSize.lean](IntegerRectangularHermiteAtSize.lean)
provides the named-rank host adapter. It reuses the canonical parameter views
and returns all three matrices in their original host domains. The shared
presentation views and transport theorems are in
[IntegerRename.lean](IntegerRename.lean). Host-coordinate
admissibility, realizability, TM0, and rank-zero admissibility are checked.
[IntegerRectangularHermiteStoredRank.lean][stored rank Hermite]
reads the supplied rank and uses the shared host-result call, keeping its
header internal. Realizability, TM0, and rank-zero admissibility are checked.
Named-rank and stored-rank host results now agree exactly with the mathematical
rectangular run. Supported-input presentation preservation and unimodularity
are proved, and the zero-matrix check passes. Initialization now returns its
proved mathematical entry width.
[IntegerHermiteReduction.lean](IntegerHermiteReduction.lean) composes all
Hermite stages for arbitrary signed rectangular input. Its full bases preserve
the presentation and are unimodular; the returned rank is the matrix rank and
the matrix is a positive active diagonal. Realizability, TM0, and zero-input
checks pass in [the examples](../Examples/IntegerHermiteReduction.lean).
[IntegerRectangularCleanup.lean](IntegerRectangularCleanup.lean) reads the
active diagonal from a full matrix and applies divisibility cleanup, returning
the full Smith contract. Both output-width interfaces have realizability and
TM0 certificates; the bounded interface uses a host-derived capacity
independent of active rank. Rank-zero admissibility is checked in
[the cleanup examples](../Examples/IntegerRectangularCleanup.lean).
[Named-rank cleanup](IntegerRectangularCleanupAtSize.lean) and
[stored-rank cleanup](IntegerRectangularCleanupStoredRank.lean) retain the full
Smith contract in host coordinates.
[IntegerSmithReduction.lean](IntegerSmithReduction.lean) composes Hermite
reduction and cleanup, retaining the actual accumulated bases and matrix rank.
It proves the full Smith contract for arbitrary bounded rectangular input.
Output codecs use fixed polynomial widths in the original input sizes.
[Diagonal feasibility](IntegerDiagonalFeasible.lean) decides integer solvability
for a supplied Smith diagonal using its zero-extended diagonal and total
pointwise divisibility. [IntegerMulVec.lean](IntegerMulVec.lean) provides the
matrix-vector product needed for target and solution transport.
[IntegerSystemFeasible.lean](IntegerSystemFeasible.lean) composes Smith
reduction, target transport, and diagonal feasibility, deciding integer
solvability for arbitrary rectangular input.
[IntegerDiagonalSolution.lean](IntegerDiagonalSolution.lean) recovers diagonal
solution coordinates with independent input widths and no rank argument. Its
coordinates solve every feasible Smith diagonal system.
[IntegerSystemSolve.lean](IntegerSystemSolve.lean) applies the right basis and
returns an explicit optional integer solution. Its contracts certify every
returned witness and characterize no-solution results exactly.
[IntegerAugmentedMatrix.lean](IntegerAugmentedMatrix.lean) constructs the full
generator/modulus matrix by certified horizontal concatenation.
[IntegerCyclicMembership.lean](IntegerCyclicMembership.lean) decides cyclic
span membership through the existing integer-system consumer. Its optional
solver returns generator and modulus coefficients through ordinary sum
indices, with both the augmented equation and cyclic representation proved.
[IntegerQuotientCoordinates.lean][runtime quotient] composes supplied diagonal
and left-basis transport. [IntegerSystemCoordinates.lean][system quotient]
certifies its composition with full Smith reduction, returning actual cyclic
and free coordinates. Vanishing is equivalent to integer feasibility.
[AugmentedRank.lean][finite quotient] proves full row rank for nonzero moduli
and finiteness of a full-row-rank Smith cokernel.
[IntegerMultiply.lean](IntegerMultiply.lean) specifies that product with
independent input widths and a proved partial-dot-product bound. The
[empty shared dimension check](../Examples/IntegerMultiply.lean) returns zero.
[IntegerMultiplyRealizable.lean](IntegerMultiplyRealizable.lean) realizes
matrix multiplication by row reads, transpose, and tabulation using the
[fixed-width dot-product fold](IntegerDotProduct.lean). Both operations have
exact mathematical contracts and standalone TM0 certificates. The examples
also check signed cancellation.

[permutation example]: ../Examples/PivotPermutation.lean
[Rank stabilization](HermiteRankMath.lean) identifies the reported pivot count
with Mathlib's integer matrix rank. [Two-pass initialization][stabilization]
composes row and column normalization, preserves rank, zeros both inactive
strips, and retains actual bases with polynomial widths.
[HermiteStabilization.lean][stabilization examples] checks rectangular inputs
and a rank-two block still requiring further passes.
[Supported determinant invariance](SupportedDeterminantMath.lean) restricts
two-sided presentations to their active block.
[Fixed Hermite bounds][determinant]
prove that later row and column passes preserve its determinant magnitude and
bound every output entry by that same value.
[HermiteDeterminant.lean][det examples]
checks a rectangular gcd change and the rank-zero empty determinant.
[Hermite diagonal progress](HermiteDiagonalMath.lean) now preserves the selected
diagonal product and other diagonal entries under explicit stage-zero
conditions. Nondivisible updates decrease the shared weighted bit measure;
divisible cancellation leaves the diagonal fixed. The cleanup proof reuses
the generalized pair estimate, including nonadjacent indices.
[HermiteDiagonal.lean][diagonal progress examples] checks nonadjacent transfer,
a following divisible stage, and a negative incoming entry.
[Triangular-input invariants](HermiteTriangularMath.lean) derive future-column
zeros from outer-prefix support. Canonical incoming traversal preserves positive
diagonals, selects the incoming diagonal pivot, and does not increase the bit
measure. [Examples](../Examples/HermiteTriangular.lean) retain a nonzero future
row and cover insertion with no earlier pivots. The complete outer traversal on
positive lower triangular square input now retains canonical pivots, positive
diagonals, and a nonincreasing bit measure at every prefix, including the empty
prefix. A genuine gcd update now forces strict decrease through every later
inner prefix and through final pivot extension. The existing nonincrease proof
reuses this transition estimate. Divisible stages and insertion without strict
progress preserve lower triangularity. A complete row pass on positive lower
triangular square input now either returns a diagonal matrix or strictly
decreases the bit measure. [Bounded alternating square reduction][alternating]
now composes row and transpose-dual column passes with both actual unimodular
bases. For positive lower triangular input of dimension `n` and entry width
`w`, `w * n * n + 2` pairs suffice for a positive diagonal output.
[Uniform alternating bounds][alternating bounds] retain the determinant
magnitude and bound pair-output entries by it. A common width derived from
`w` and `n` gives polynomial run-output and accumulated-basis widths, growing
additively with the pair budget. [Rectangular Hermite reduction][rectangular
Hermite] now lifts that run through arbitrary active-block identity extensions,
with full bases, a positive diagonal-output contract, and polynomial widths.
Singular rectangular and rank-zero empty-row examples are checked.
[The full mathematical Smith construction][Smith construction] now composes
initial compaction, bounded diagonalization, and divisibility cleanup, retaining
both full bases and identifying the returned rank with integer matrix rank.
Its Smith contract covers arbitrary signed rectangular and singular input,
including empty dimensions. [Composed output bounds][Smith bounds] now give
one exact polynomial width in the original row count, column count, and entry
width for the returned diagonal and both full bases. The bounds derive rank
and all internal capacities. Runtime realization and certified consumers remain
open.
[Minor invariance](MinorInvarianceMath.lean) also bounds
triangular incoming entries without requiring zeros outside the selected rows;
[MinorInvariance.lean](../Examples/MinorInvariance.lean) checks proper minors
and a two-stage rectangular example.
[Automatic minor witnesses](MinorWitnessMath.lean) remove the nonzero input
minor obligation. [Normalized pivot-block bounds][block bounds] use the
original entry width;
[MinorWitness.lean](../Examples/MinorWitness.lean) checks row permutations,
zero blocks, and empty minors. [Supported-row bounds](HermiteRowBoundsMath.lean)
extend the original-width bound to trailing columns using an adjugate identity;
[HermiteRowBounds.lean](../Examples/HermiteRowBounds.lean) checks a rectangular
rank-deficient example and rank zero.

[column traversal]: HermiteColumnTraversalMath.lean
[pair transpose]: IntegerPairTranspose.lean

[Diagonal cleanup][cleanup] has a bounded mathematical algorithm, polynomial
iteration and intermediate-entry bounds, and explicit two-entry unimodular
transformations. [DiagonalNormalization.lean][cleanup examples] exercises
repeated repairs, a valid chain, negative and zero pairs, and empty input.
[Accumulated cleanup bases][cleanup bases] satisfy the Smith contract for the
active square diagonal block, with [polynomial width bounds][bounds] at every
iteration prefix. [Rectangular cleanup][rectangular] extends these bases by
identity on unused coordinates, retaining the contract and polynomial bounds
for independent row and column counts. [RectangularDiagonal.lean][rect examples]
checks rank deficiency, empty dimensions, and composition with an earlier
diagonal presentation. [The two-entry cleanup operation][pair machine] already
returns both diagonal entries and the actual two-by-two transformations with a
TM0 certificate; [DiagonalPair.lean][pair examples] checks signs and zeros.
[Natural diagonal search][search] returns an optional coordinate, with a
certified failing successor and strict progress of the mathematical measure.
[DiagonalSearch.lean][search examples] checks signs, zeros, empty arrays, and
singletons. Reconstructing the successor gives exactly the pair selected by
the mathematical cleanup, through a shared pure finite-array specification.
[Coordinate selection][repair] returns both actual adjacent coordinates when
repair is needed. [The Boolean stopping guard][chain] shares the search flags
and accepts exactly when search returns no repair.
[The coupled basis step][basis step] retains the pair result and applies its
transformations to both accumulated bases, with additive output widths and
presentation-preservation proofs. [IntegerRowPairWidths.lean][width examples]
checks distinct coefficient/matrix widths and column orientation;
[DiagonalBasisStep.lean][basis examples] checks nonidentity bases and the zero
pair. [Matrix narrowing][narrow] preserves values after a proved entry bound;
[the internal basis adapter][basis narrow] returns both updated bases to their
workspace width. Its repair wrapper derives the narrowing precondition from
the prefix bound, sharing the growth lemma with the mathematical cleanup loop.
The same example checks nonzero and zero-pair narrowing and fixed-workspace
repair. [The selected repair][selected step] also composes coordinate selection
and entry lookup, retaining presentation and unimodularity certificates.
[MatrixNarrow.lean](../Examples/MatrixNarrow.lean) checks signed matrices,
empty dimensions, and zero-width bounds.
[The guarded state update][cleanup step] stores both replacement entries and
retains the bases. Its result equals one mathematical cleanup iteration;
[DiagonalCleanupStep.lean](../Examples/DiagonalCleanupStep.lean) checks
a repair, a stopped singleton, and empty dimensions.
[The bounded controller][controller] repeats this update with a certified
prefix invariant and fixed workspace.
[DiagonalCleanupController.lean][controller examples] checks zero budgets and
empty arrays. [Positive diagonal cleanup][positive cleanup] derives the budget
and workspace, widens the input, and initializes both identities internally.
[PositiveDiagonalCleanup.lean][positive examples] checks repeated repairs,
actual bases, the Smith contract, and empty or zero-width inputs.
[Rectangular diagonal construction][rectangular matrix] now has realizability
and TM0 certificates, including inactive zeros and rank zero; see
[IntegerRectangularDiagonal.lean][rectangular matrix examples].
[Basis extension][extend basis] adds the complementary identities.
[Rectangular cleanup][rectangular cleanup] composes the full `D`, `U`, and `V`
with a realizability certificate and the Smith contract for an already diagonal
input; [its examples][rectangular cleanup examples] include a 4-by-5 matrix and
rank-zero empty dimensions. Complete Hermite reduction and its bounds are
implemented above.
The mathematical Smith contract, diagonal feasibility test, solution recovery,
and augmented-system equivalence are proved in [SmithMath.lean][smith] and
[AugmentedMath.lean][aug]. [SmithCoordinates.lean][quot] transports quotient
coordinates and identifies the cokernel, including its free part. Certified
quotient transport is implemented in
[IntegerSystemCoordinates.lean][system quotient]; see its
[examples](../Examples/QuotientCoordinates.lean).

[cleanup examples]: ../Examples/DiagonalNormalization.lean
[rect examples]: ../Examples/RectangularDiagonal.lean
[pair examples]: ../Examples/DiagonalPair.lean
[search examples]: ../Examples/DiagonalSearch.lean
[width examples]: ../Examples/IntegerRowPairWidths.lean
[basis examples]: ../Examples/DiagonalBasisStep.lean
[controller examples]: ../Examples/DiagonalCleanupController.lean
[positive examples]: ../Examples/PositiveDiagonalCleanup.lean
[rectangular matrix examples]: ../Examples/IntegerRectangularDiagonal.lean
[rectangular cleanup examples]: ../Examples/RectangularDiagonalCleanup.lean

## Foundational work

[AddressContract.lean](AddressContract.lean),
[EntryContract.lean](EntryContract.lean), and
[ReplaceContract.lean](ReplaceContract.lean) certify the lower-level accessors.
[RowsContract.lean](RowsContract.lean) and
[RowsPresentation.lean](RowsPresentation.lean) connect shared row workspaces to
mathematical interfaces. They own address arithmetic, scratch, initialization,
and tape restoration. The generic [bounded traversal][traversal] avoids
repeating counter and guard arguments in each row algorithm.

[traversal]: ../Arithmetic/BoundedTraversal.lean

[pivot examples]: ../Examples/HermitePivot.lean

[insert examples]: ../Examples/HermiteInsert.lean

[processed examples]: ../Examples/HermiteProcessed.lean

[sweep examples]: ../Examples/HermiteSweep.lean

[compact examples]: ../Examples/CompactHermite.lean

[stabilization]: HermiteStabilizationMath.lean
[stabilization examples]: ../Examples/HermiteStabilization.lean

[determinant]: HermiteDeterminantMath.lean
[det examples]: ../Examples/HermiteDeterminant.lean

[diagonal progress examples]: ../Examples/HermiteDiagonal.lean

[alternating]: HermiteAlternatingMath.lean

[alternating bounds]: HermiteAlternatingBounds.lean

[rectangular Hermite]: RectangularHermiteMath.lean

[Smith construction]: SmithConstructionMath.lean

[Smith bounds]: SmithConstructionBounds.lean

[runtime stage]: IntegerHermiteStage.lean

[stage controller]: HermiteStageController.lean

[residual runtime]: IntegerResidualPivot.lean
[sign runtime]: IntegerPositivePivot.lean

[runtime prefix]: ../Arrays/PrefixFlags.lean

[prefix stage]: IntegerHermiteStagePrefix.lean

[incoming controller examples]: ../Examples/HermiteIncomingController.lean

[incoming]: IntegerHermiteIncoming.lean
[incoming example]: ../Examples/IntegerHermiteIncoming.lean

[Fixed-pivot remainder sweeps](RemainderSweepController.lean) use one additive
workspace for all prefixes; [their example][remainder example] checks signed
remainders, actual bases, and a TM0 certificate.

[remainder example]: ../Examples/RemainderSweepController.lean

[Runtime pivot extension](IntegerHermiteExtendPivot.lean) normalizes either
pivot sign and reduces the old rows, with internal storage preparation.
[Its example][extension example] checks a negative pivot and both actual
matrices, with a TM0 certificate.

[extension example]: ../Examples/IntegerHermiteExtendPivot.lean

[Residual finishing](IntegerHermiteResidualFinish.lean) returns the optional
new pivot and both actual matrices, retaining a zero residual or extending at a
found nonzero entry. [Its examples][residual finish example] check both branches
and presentation preservation, with a TM0 certificate.

[residual finish example]: ../Examples/IntegerHermiteResidualFinish.lean

[runtime insertion example]: ../Examples/IntegerHermiteInsertRow.lean

[Pivot-selection metadata](HermitePivotSelection.lean) exposes an ordinary rank
and row/column embeddings through a shared bounded-array codec.
[Pivot append](HermitePivotAppend.lean) reuses bounded-array snoc when the new
row and column are excluded from the old embeddings; capacity follows from
row injectivity. [Its examples][pivot metadata example] check empty coordinate
types, rank extraction, exact width, preserved and appended pivots, repeated
column rejection, and TM0 certificates.

[Computed-rank reading](HermitePivotRead.lean) extracts both live embeddings
as arrays, then appends the incoming row for insertion. It reuses array maps
and snoc, with a distinctness contract and TM0 certificates. Its insertion
coordinate view converts indices to the renamed polynomial dimensions.
[Named-rank insertion](IntegerHermiteInsertAtSize.lean) combines these arrays
with the two matrix parameter views and invokes complete row insertion,
retaining the presentation and unimodular basis. Its exact output contract
agrees with mathematical insertion for the supplied row and column maps,
including the optional new pivot. Its bounded variant returns both matrices
at a width derived from the original width and row count, independent of rank.
[IntegerResize.lean](IntegerResize.lean) reuses widening and narrowing for any
pair of widths when the entries fit the target bound.
[Stored-rank insertion](IntegerHermiteStoredRank.lean) now reads metadata,
invokes that callee through the shared host-result call, and returns no size
header. Its TM0 certificate includes preparation. The precondition requires
an excluded incoming row and a positive upper pivot block. Rank-zero and
nonzero-rank examples use this interface. Its host-sized values return ordinary
matrices and an optional column, with exact mathematical insertion and
presentation-preservation contracts. Equal finite dimensions are transported
by the shared insertion congruence rule.
[HermiteInsertionResult.lean](HermiteInsertionResult.lean) reconstructs the
complete host codec, including the optional column, without changing bits.
The stored-rank call uses this rank-independent output codec.
`integerHermiteInsertHost` returns the host payload directly, with
realizability, TM0, exact-insertion, and presentation-preservation certificates.
[IntegerHermiteAdvance.lean](IntegerHermiteAdvance.lean) combines insertion
with updated pivot embeddings. Returned columns are proved excluded from the
old selection; dependent rows retain metadata and independent rows append the
actual row/column pair. TM0, both metadata outcomes, and actual-basis
preservation are checked.
[HermiteRowsStep.lean](HermiteRowsStep.lean) identifies this transition with
the canonical mathematical prefix and resizes both matrices to one fixed
[workspace](HermiteRowsWorkspace.lean), derived from original input sizes.
Its TM0 certificate and signed initial-state example pass.
[HermiteRowsController.lean](HermiteRowsController.lean) now composes the whole
fold. `integerHermiteRows` prepares the initial state and returns the actual
left basis and pivot embeddings, with exact sweep and normalized-prefix
contracts and a TM0 certificate. [Its examples][rows runtime example] check a
signed singular rectangle, sign normalization, presentation preservation, and
either empty dimension.

[rows runtime example]: ../Examples/IntegerHermiteRows.lean

[pivot metadata example]: ../Examples/HermitePivotSelection.lean

[runtime quotient]: IntegerQuotientCoordinates.lean
[system quotient]: IntegerSystemCoordinates.lean
[finite quotient]: AugmentedRank.lean

[runtime Smith]: IntegerSmithReduction.lean
[feasibility]: IntegerSystemFeasible.lean
[solve]: IntegerSystemSolve.lean
[cyclic span]: IntegerCyclicMembership.lean

[stored rank Hermite]: IntegerRectangularHermiteStoredRank.lean
