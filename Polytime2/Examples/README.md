# Worked examples

[Project guide](../README.md)

Choose a representative example for your task, then follow the linked topic
guide for the reusable interface. This is a starting-point map, not a catalogue
of every theorem or implementation experiment.

| Learn how to... | Example | Guide |
| --- | --- | --- |
| Certify a specification | [Specification.lean][spec] | [composition][cg] |
| Define a computation | [Computation.lean][comp] | [composition][cg] |
| Retain arguments and compose calls | [Context.lean][ctx] | [composition][cg] |
| Use records and alternatives | [Records.lean][rec] | [encoding][eg] |
| Prove a loop | [Loop.lean](Loop.lean) | [composition][cg] |
| Invoke at stored sizes | [DynamicSizes.lean][dyn] | [sizes][cg] |
| Use signed arithmetic | [Integers.lean](Integers.lean) | [arithmetic][ag] |
| Fold or transform arrays | [Fold.lean][fold], [Transform][map] | [arrays] |
| Pack related data and call a consumer | [Packing.lean][pack] | [arrays] |
| Access or transform matrix rows | [MatrixRows.lean][rows] | [matrices][mg] |
| Use elimination | [GaussJordan.lean][gj] | [Gauss–Jordan][gg] |
| Export to a standalone machine | [TM0.lean](TM0.lean) | [TM0][tg] |
| Prepare an SMP instance | [SMP/RingExample.lean][ring] | [SMP][sg] |

[spec]: Specification.lean
[comp]: Computation.lean
[ctx]: Context.lean
[rec]: Records.lean
[dyn]: DynamicSizes.lean
[fold]: Fold.lean
[map]: Transform.lean
[pack]: Packing.lean
[rows]: MatrixRows.lean
[gj]: GaussJordan.lean
[ring]: SMP/RingExample.lean
[cg]: ../Computation/README.md
[eg]: ../Encoding/README.md
[ag]: ../Arithmetic/README.md
[arrays]: ../Arrays/README.md
[mg]: ../Matrices/README.md
[gg]: ../GaussJordan/README.md
[tg]: ../TM0/README.md
[sg]: SMP/README.md

Numeric examples evaluate mathematical specifications. Realization and TM0
certificates establish machine existence and correctness for all admissible
inputs; these are distinct forms of evidence. Controller-level examples remain
useful for foundational work, but new applications should follow the public
mathematical interfaces.

[EXAMPLES.md](../../EXAMPLES.md) specifies target problems and required building
blocks. It is not a statement that every target or library is already available.
