# Foundational primitives

[Project guide](../README.md) · [Machine convention](../Machine/README.md)

Search the [computation rules](../Computation/README.md) and domain-specific
interfaces before adding a primitive. These modules certify the tape operations
used by those interfaces; application proofs should not reconstruct their
wiring.

| Building block | Starting point |
| --- | --- |
| Copying with restored heads | [Copy.lean](Copy.lean) |
| Slices or fields | [FixedCopy.lean][fixed], [FieldCopy.lean][field] |
| Fixed encoded constants | [ConstantOperations.lean][constant] |
| Finite operations and predicates | [FiniteOperations.lean][finite], [pred] |
| Bit-preserving maps and zero extension | [BitOperations.lean][bits] |
| Unary sizes and binary counters | [SizeOperations.lean][sizes] |
| Finite-memory scans | [RestoringScan.lean][scan], [ScanReturn.lean][ret] |
| Copy, clear, and constant initialization plans | [Initialization.lean][init] |

[fixed]: FixedCopy.lean
[field]: FieldCopy.lean
[constant]: ConstantOperations.lean
[finite]: FiniteOperations.lean
[pred]: FinitePredicate.lean
[bits]: BitOperations.lean
[sizes]: SizeOperations.lean
[scan]: RestoringScan.lean
[ret]: ScanReturn.lean
[init]: Initialization.lean

## Reuse patterns

Finite tables specialize ordinary functions on finite encoded carriers. The
argument family and each field width are fixed by specialization; runtime
selection does not require a new controller for each caller. See
[FiniteTables.lean](../Examples/FiniteTables.lean).
`finitePredicate domain predicate` lifts a fixed domain to runtime sizes and
returns the native Boolean codec, with size transport inside its realization.

`encodingMap_realizable` certifies total maps preserving canonical bits. It
uses the existing copy realization because public inputs and outputs occupy
separate tapes. For changing an existing computation's mathematical meaning,
prefer the [specialization rules][specialization].

[specialization]: ../Computation/README.md#change-mathematical-representations

`RestoringScan` and `ScanReturn` share traversal, boundaries, and restoration
arguments. Fixed slice copying has a distinct workspace contract; choose an
existing routine by its preconditions rather than replacing it with a more
expensive generic controller. Exact costs belong in the source contracts.

Initialization plans reuse [Pipeline.lean](../Machine/Pipeline.lean) and prepare
only the live working data. Read unary sizes through the existing certificates
rather than requiring callers to initialize private headers. See
[SizeRead.lean](../Examples/SizeRead.lean) for a worked boundary case.
