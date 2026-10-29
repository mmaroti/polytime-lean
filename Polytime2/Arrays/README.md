# Arrays

[Project guide](../README.md) · [Encoding](../Encoding/README.md)

Array interfaces use mathematical functions on finite indices, including arrays
whose element widths depend on runtime sizes. Start with
[Operations.lean](Operations.lean) for access and updates.

| Task | Starting point |
| --- | --- |
| Read, replace, or copy an indexed element | [Operations.lean][access] |
| Combine arrays pointwise | [ZipWith.lean](ZipWith.lean) |
| Normalize actual cyclic/free coordinates | [CyclicCoordinates.lean][cyclic] |
| Enumerate canonical bounded coordinates | [BoundedPositions.lean][bounded] |
| Flatten arrays or fixed records | [FlattenRecords.lean][flatten] |
| Reverse a finite coordinate | [PositionReverse.lean](PositionReverse.lean) |
| Tabulate from finite coordinates | [Tabulate.lean](Tabulate.lean) |
| Lift an operation over every element | [Transform.lean](Transform.lean) |
| Use a named size parameter for a transform | [NamedTransform.lean][named] |
| Traverse with an accumulator | [Fold.lean](Fold.lean) |
| Find the first false flag as an optional coordinate | [FindFalse.lean][find] |
| Extract successful search coordinates and adjacent pairs | [coordinates] |
| Compare coordinates across dimensions or with a size | [position arithmetic] |
| Test whether every Boolean entry is true | [AllTrue.lean](AllTrue.lean) |
| Test whether an element occurs in an array | [Contains.lean](Contains.lean) |
| Retain prefix states | [Scan.lean](Scan.lean) |
| Select elements stably by a Boolean mask | [PackingResult.lean][pack] |
| Extract an exact interval | [Slice.lean](Slice.lean) |
| Share selected positions across related fields | [PackingResult.lean][pos] |
| Call a consumer at the retained length | [PackingCall.lean][call] |
| Read a stored packed array at its exact size | [PackingRead.lean][read] |

[cyclic]: CyclicCoordinates.lean
[access]: Operations.lean
[flatten]: FlattenRecords.lean
[bounded]: BoundedPositions.lean
[find]: FindFalse.lean
[coordinates]: SearchCoordinates.lean
[position arithmetic]: PositionArithmetic.lean
[named]: NamedTransform.lean
[pack]: PackingResult.lean
[pos]: PackingResult.lean
[call]: PackingCall.lean
[read]: PackingRead.lean

## Access and traversal

Public lookup and update take coordinates in the mathematical index type.
Lookup returns an element; update returns a separate array. Inputs remain
immutable. Nested arrays support whole-row access through the same rules.
Named-size accessors can use another coordinate domain when its encoded numeric
value agrees with the selected index.

[First-false search][find] reuses the prefix scan and count, returning
`Option (Fin length)` without exposing the internal all-accepted sentinel.
[Count.lean](Count.lean) specifies the cardinality of the true positions, and
[FirstFalse.lean](FirstFalse.lean) specifies the mathematical search index.
Their observation contracts hide the scan, counter seed, and traversal.
For dependent packing results, `arrayPack_compute` gives the complete
mathematical count and retained array together; the structural count remains
available for indexing the payload.
Its result and stopping-condition theorems cover empty arrays.
[PrefixIntervalFlags.lean](PrefixIntervalFlags.lean) selects a prefix and a
later interval using ordinary endpoints.
[PackingIntervals.lean](PackingIntervals.lean) identifies their stable packing
with list take/drop/take; nested-witness normalization uses this rule.
[Position arithmetic][position arithmetic] compares ordinary coordinate values
across dimensions or against an active-prefix size, using derived capacities.
[PositionPolynomial.lean](PositionPolynomial.lean) constructs a polynomial
coordinate under its mathematical interval bound. For expressions that also
read runtime coordinates, see [natural polynomial evaluation][polynomial].
`indexToPosition` in [PositionArithmetic.lean][position arithmetic] converts a
bounded index to the prefix-count position codec without changing its value.
[PrefixFlags.lean](PrefixFlags.lean) selects runtime prefixes in fixed-length
storage. [GuardedFold.lean](GuardedFold.lean) certifies selected updates and
identifies every guarded prefix with the corresponding ordinary prefix.
[Search coordinates][coordinates] recover the actual index and, when it exists,
its successor. [AllTrue.lean](AllTrue.lean) folds conjunction to supply a
certified Boolean guard, including on empty arrays.
[FindFalseMath.lean](FindFalseMath.lean) supplies the shared pure search and
adjacency specification used by the certified scan and diagonal cleanup.

For a fold, supply the step computation, an invariant, initialization, and
preservation proofs. The public realization rules are in
[FoldContract.lean](FoldContract.lean); use the total rule when all updates are
admissible.
For a proof-dependent step, certify `arrayFoldPartialStep` by composition, then
use `arrayFoldStep_of_partial_realizable` for its `ArrayFold.extend` update.
The invariant supplies admissibility without a runtime test. Use
`ArrayFold.extend_of_allowed` when proving prefix simulation;
`ArrayFold.prefix_invariant` defaults to the full array length and also accepts
an explicit prefix length and bound.
[SwapValues.lean](SwapValues.lean) exchanges two values throughout an array;
its use in pivot-permutation tables preserves the element codec and length.

Named-size `arrayZipWithAtParameter` and `arrayAllTrueAtParameter` retain
ordinary `Fin (sizes parameter)` coordinates. The
[CSP checker](../CSP/CheckerRealizable.lean) uses them for fixed-arity relation
tables, including empty coordinate ranges.

`arrayZip` combines any finite family of arrays with immutable context;
`arrayZipWith` is its binary specialization.
[Shift.lean](Shift.lean) reads left or right neighbors with a supplied boundary
value, preserving array length and canonical element bits.

For a transform, certify the element operation and let the array rule handle
traversal and result collection. No default mathematical element is needed.
See [Fold.lean](../Examples/Fold.lean) and
[Transform.lean](../Examples/Transform.lean) for examples, including empty
arrays and zero-width elements.

[FlattenRecords.lean](FlattenRecords.lean) supplies `recordToArray`,
`arrayFlatten`, and `arrayFlattenRecords`. Their list contracts retain the
complete row-major sequence, and their realizations preserve canonical bits.
`arrayPositionReverse` certifies `Fin.rev` at the existing coordinate width;
the disjunction observer uses it for reversed suffix blocks.

`arrayPosition_binary_bits` in [Indices.lean](Indices.lean) lets coordinate
arithmetic reuse canonical unsigned words at the codec's derived width.

`arrayOfLengthRename` and `arrayOfLengthRenameView` in [Capacity.lean][capacity]
move size renaming into or out of a polynomial array codec, preserving its
elements and bits. The word-circuit constructor uses the former.

[capacity]: Capacity.lean

[Fixed-array decoding](../Computation/FixedArrayDecode.lean) validates scalar
codes and returns an optional array of actual values. The scalar codec is
fixed before runtime; the array length may be any polynomial. Its canonical
contract covers unused codes, empty carriers, empty arrays, and zero widths.

## Packing and computed sizes

`boundedArrayAtLength` reads stored elements at an exact polynomial length,
after the caller proves that the stored count equals that length.
`boundedArrayAtSize` retains the named-size interface as a specialization;
both reuse one field-reading proof. The [instance reader][instance reader]
uses the polynomial form for dense relational-table widths.

[PackingWidth.lean](PackingWidth.lean) supplies `boundedArrayHasLength` to
validate that equality at runtime, including when the requested length exceeds
the host capacity. It reads the stored count and reuses unary count comparison;
element-code validation remains separate.

[Capacity.lean](Capacity.lean) supplies `boundedArrayResize` to increase a
stored array's capacity without changing its actual count or elements. It
reuses the existing count and payload accessors, unary resizing, and bit-vector
resizing. This supports retaining parsed CSP payloads at the caller capacity.
`boundedArrayRename` moves size renaming inside the codec while preserving the
actual count and element encodings; the header-payload parser uses it before
capacity conversion.

`arrayPack` returns a retained count and an array of exactly that length.
Capacity padding and binary counters stay private. Use shared positions when
packing targets, generators, or dependency labels selected by the same mask.
`arraySlice` specializes packing to a half-open interval with ordinary finite
endpoints. Its result agrees with list `drop` followed by `take`, including
empty and reversed intervals. The [word-pair extractor][pair fields] uses it
for both fields.
`boundedArrayCallFrame` prepares a consumer call from an already packed value;
`preparePackingCall` includes packing. Avoid repeating the packing stage for
related consumers.

[FixedArrayCall.lean](FixedArrayCall.lean) prepares a computed-size frame for
elements whose codec is fixed independently of runtime sizes. It reuses the
stored count and element bits and omits unrelated caller size parameters.
The [unary-size reader][unary size] uses this frame with the existing
computed-size execution rule. `ready.callFixedArray` combines frame preparation
and a total unary consumer call at the exact retained length.
[FixedArrayResult.lean](FixedArrayResult.lean) repackages a computed-size
Boolean flag and array into a flag and bounded array, preserving the actual
count. The stored binary decoder uses it to return validated fields to the
host capacity without exposing computed-size storage.

[BooleanField.lean](BooleanField.lean) supplies `storedBooleanFieldView` to
pass a direct stored Boolean field to a named-size reader without changing its
count or canonical bits. Instance and assignment word decoders share this rule.

See [Packing.lean](../Examples/Packing.lean) for stable positions and consumers.
The [SMP guide](../Examples/SMP/README.md) shows several fields sharing packed
coordinate data and later dropping the original working dimensions.

## Foundational modules

Fixed-width and runtime-width accessors share navigation, block-copy contracts,
and codec arguments, while retaining different workspace requirements.
[FoldContract.lean](FoldContract.lean) implements generic folds;
[PackingRaw.lean](PackingRaw.lean) and [PackingInvariant.lean][inv] implement
the
packing pass. These modules own tape placement, capacity proofs, head
restoration, and raw padding. Applications should use the interfaces above.

[inv]: PackingInvariant.lean

[SearchGuard.lean](SearchGuard.lean) tests whether an optional coordinate is
absent, including an empty search domain. It reuses canonical equality and
search; [the runtime pivot example][search guard example] includes its TM0
certificate and a residual-row zero test.

[search guard example]: ../Examples/HermitePivotRuntime.lean

[Snoc.lean](Snoc.lean) appends an element using record construction and
canonical array bits. [Its use in bounded unary successor][snoc example] checks
an empty array and includes a TM0 certificate.

[snoc example]: ../Examples/UnarySuccessor.lean

[BoundedSnoc.lean](BoundedSnoc.lean) calls snoc at a bounded array's actual
count and reassembles the incremented header and payload within the original
capacity. [Its examples][bounded snoc example] check old elements, the appended
value, actual counts, empty arrays, and full-capacity rejection, with TM0
certificates.

[bounded snoc example]: ../Examples/BoundedSnoc.lean
[pair fields]: ../Complexity/PairFields.lean
[unary size]: ../Complexity/UnarySize.lean
[instance reader]: ../CSP/ReadInstance.lean

[polynomial]: ../Arithmetic/NaturalPolynomial.lean
