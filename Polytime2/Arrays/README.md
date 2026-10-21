# Arrays

[Project guide](../README.md) · [Encoding](../Encoding/README.md)

Array interfaces use mathematical functions on finite indices, including arrays
whose element widths depend on runtime sizes. Start with
[Operations.lean](Operations.lean) for access and updates.

| Task | Starting point |
| --- | --- |
| Read, replace, or copy an indexed element | [Operations.lean][access] |
| Lift an operation over every element | [Transform.lean](Transform.lean) |
| Use a named size parameter for a transform | [NamedTransform.lean][named] |
| Traverse with an accumulator | [Fold.lean](Fold.lean) |
| Retain prefix states | [Scan.lean](Scan.lean) |
| Select elements stably by a Boolean mask | [PackingResult.lean][pack] |
| Share selected positions across related fields | [PackingResult.lean][pos] |
| Call a consumer at the retained length | [PackingCall.lean][call] |
| Read a stored packed array at its exact size | [PackingRead.lean][read] |

[access]: Operations.lean
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

For a fold, supply the step computation, an invariant, initialization, and
preservation proofs. The public realization rules are in
[FoldContract.lean](FoldContract.lean); use the total rule when all updates are
admissible.
For a transform, certify the element operation and let the array rule handle
traversal and result collection. No default mathematical element is needed.
See [Fold.lean](../Examples/Fold.lean) and
[Transform.lean](../Examples/Transform.lean) for examples, including empty
arrays
and zero-width elements.

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
