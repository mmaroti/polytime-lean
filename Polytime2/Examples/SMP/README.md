# SMP preparation and consumers

[Project guide](../../README.md) · [Composition](../../Computation/README.md)

This development prepares a subpower-membership instance for a fixed finite
algebra and a specialization-fixed catalogue. Start with
[PreparedOutcome.lean](PreparedOutcome.lean) for the public preparation and
[PreparedConsumer.lean](PreparedConsumer.lean) to compose a consumer.

## Public interfaces

`Prepared.prepare` returns either an actual rejected original coordinate or a
dependent frame with the exact sort counts, generator count, and prepared
mathematical instance. The all-accepted search sentinel remains internal.
`prepare_specification` gives the rejection or preparation guarantees and
membership equivalence. `prepare_tm0` includes preparation and output
extraction.

[Multisorted.lean](Multisorted.lean) defines the conversion-independent prepared
input: generators and a target in the product of the fixed sort carriers, with
finite dependency sets. `IsPrepared` records the catalogue and dependency
conditions. Public statements use mathematical membership, cardinalities, and
products; characteristic masks, quotient blocks, and padding stay in codecs.

`Prepared.prepareAndConsume_realizable` composes preparation with a certified
unary consumer whose precondition follows from `IsPrepared`. It preserves
explicit rejection and invokes the consumer at the actual sort counts.
`prepareAndConsume_tm0` exports the whole computation. The consumer remains a
separate obligation; preparation alone is not a general polynomial-time SMP
solver.

## Start with examples

[RingExample.lean](RingExample.lean) specializes to `ZMod 4` and exercises empty
coordinates and a certified target consumer. [MultisortedExample.lean][multi]
also covers distinct finite rings, absent sorts, and empty catalogues. These
specializations use finite mathematical choices, proving existence for each
fixed algebra rather than an executable compiler from operation tables.

[multi]: MultisortedExample.lean

For the mathematical problem, read [target example 2][target]. For new work,
see the [prepared-consumer task](../../tasks/prepared-smp-consumer.md).

[target]: ../../../EXAMPLES.md#smp-preparation

## Navigate the implementation

| Concern | Starting modules |
| --- | --- |
| Coordinate images and subdirect decomposition | [images], [decomposition] |
| SI reduction and monolith equation | [reduction], [monolith] |
| Prepared carrier and dependencies | [Multisorted.lean][domain] |
| Convert coordinate data | [Conversion.lean](Conversion.lean) |
| Shared selection and exact sort counts | [PreparedPacking.lean][packing] |
| Generators, targets, and finite dependency sets | [input], [dependencies] |
| Frame construction and removal of original sizes | [frame], [projection] |
| Rejection and accepted outcome | [PreparedOutcome.lean][outcome] |
| Compose a certified consumer | [PreparedConsumer.lean][consumer] |
| Bound costs in the original dimensions | [PreparedCounts.lean][counts] |

[images]: CoordinateImages.lean
[decomposition]: Decomposition.lean
[reduction]: CoordinateReduction.lean
[monolith]: MonolithCatalogue.lean
[domain]: Multisorted.lean
[packing]: PreparedPacking.lean
[input]: PreparedInput.lean
[dependencies]: PreparedDependencies.lean
[frame]: PreparedFrame.lean
[projection]: PreparedProjection.lean
[outcome]: PreparedOutcome.lean
[consumer]: PreparedConsumer.lean
[counts]: PreparedCounts.lean

Preparation shares one coordinate selection across targets, generators, and
dependency labels. Reuse [array packing](../../Arrays/README.md) and
[computed-size calls](../../Computation/README.md#sizes-and-loops) when
extending
this pipeline. Do not expose original working dimensions or padding in the
prepared payload, or rebuild singleton argument records in consumers.
