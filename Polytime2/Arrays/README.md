# Arrays

[Project guide](../README.md) · [Encoding](../Encoding/README.md)

Array interfaces use mathematical functions on finite indices, including arrays
whose element widths depend on runtime sizes. Start with
[Operations.lean](Operations.lean) for access and updates.

| Task | Starting point |
| --- | --- |
| Read, replace, or copy an indexed element | [Operations.lean][access] |
| Combine two arrays pointwise | [ZipWith.lean](ZipWith.lean) |
| Normalize actual cyclic/free coordinates | [CyclicCoordinates.lean][cyclic] |
| Enumerate canonical bounded coordinates | [BoundedPositions.lean][bounded] |
| Tabulate from finite coordinates | [Tabulate.lean](Tabulate.lean) |
| Lift an operation over every element | [Transform.lean](Transform.lean) |
| Use a named size parameter for a transform | [NamedTransform.lean][named] |
| Traverse with an accumulator | [Fold.lean](Fold.lean) |
| Find the first false flag as an optional coordinate | [FindFalse.lean][find] |
| Extract successful search coordinates and adjacent pairs | [coordinates] |
| Compare coordinates across dimensions or with a size | [position arithmetic] |
| Test whether every Boolean entry is true | [AllTrue.lean](AllTrue.lean) |
| Retain prefix states | [Scan.lean](Scan.lean) |
| Select elements stably by a Boolean mask | [PackingResult.lean][pack] |
| Share selected positions across related fields | [PackingResult.lean][pos] |
| Call a consumer at the retained length | [PackingCall.lean][call] |
| Read a stored packed array at its exact size | [PackingRead.lean][read] |

[cyclic]: CyclicCoordinates.lean
[access]: Operations.lean
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
[Position arithmetic][position arithmetic] compares ordinary coordinate values
across dimensions or against an active-prefix size, using derived capacities.
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

For a transform, certify the element operation and let the array rule handle
traversal and result collection. No default mathematical element is needed.
See [Fold.lean](../Examples/Fold.lean) and
[Transform.lean](../Examples/Transform.lean) for examples, including empty
arrays and zero-width elements.

## Packing and computed sizes

`arrayPack` returns a retained count and an array of exactly that length.
Capacity padding and binary counters stay private. Use shared positions when
packing targets, generators, or dependency labels selected by the same mask.
`boundedArrayCallFrame` prepares a consumer call from an already packed value;
`preparePackingCall` includes packing. Avoid repeating the packing stage for
related consumers.

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
