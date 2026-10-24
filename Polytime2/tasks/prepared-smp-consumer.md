# A substantive prepared-SMP consumer

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome

Connect a concrete mathematical solver to the existing prepared-instance
interface. Select a fixed algebra or catalogue for which the intended query and
its polynomial algorithm can be stated explicitly; preparation does not promise
a generic polynomial-time solver for every finite algebra.

The existing guarantees and examples are described in the
[SMP guide](../Examples/SMP/README.md). Mathematical preparation requirements
remain in [target example 2](../../EXAMPLES.md#smp-preparation).

## Prerequisites and first milestone

Inspect `Multisorted.preparedDomain`, `IsPrepared`, and
[PreparedConsumer.lean](../Examples/SMP/PreparedConsumer.lean). Existing
examples
already compose simple target consumers. The next contribution should solve a
substantive query and prove its interpretation for the original instance.

Choose the consumer contract first. If it needs integer feasibility or
finite-abelian coordinates, identify the corresponding
[Smith normal form](../Matrices/IntegerSmithReduction.lean) interface and the
certified
coordinate conversion; abstract existence of coordinates is insufficient.

## Acceptance

- Specify mathematical input, output, admissibility, and the chosen algebraic
  assumptions independently of storage.
- Certify the unary consumer at the actual prepared sizes, and prove its
  precondition from `IsPrepared`.
- Compose with `prepareAndConsume_realizable`, preserving actual rejected
  coordinates and the consumer's mathematical outcome.
- Prove how the answer transports to the original query, with runtime bounded
  in the original dimensions.
- Export the complete computation to TM0 and exercise rejection, acceptance,
  absent sorts, and empty dimensions where relevant.

Reuse the preparation pipeline, packed data, and computed-size calling rules.
Do not expose working padding or rebuild the generic consumer wrapper.
