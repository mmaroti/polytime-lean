# Arithmetic

[Project guide](../README.md) · [Composition](../Computation/README.md)

Choose the mathematical operation before looking at its machine. Public
computations and their realization theorems are in the modules below; exact
preconditions and result bounds live in their Lean declarations and docstrings.

| Need | Interface modules |
| --- | --- |
| Unsigned addition, subtraction, multiplication | [Operations.lean][unsigned] |
| Unsigned quotient and remainder together | [DivisionOperations.lean][div] |
| A remainder projection | [RemainderOperations.lean][rem] |
| Unsigned gcd | [GcdOperations.lean](GcdOperations.lean) |
| Sign, magnitude, zero, negation | [SignedOperations.lean][sign], [basic] |
| Signed comparisons | [SignedComparison.lean](SignedComparison.lean) |
| Signed addition and multiplication | [SignedAddition.lean][add], [mul] |
| Signed Euclidean division and gcd | [SignedDivision.lean][sdiv], [gcd] |
| Bézout coefficients | [SignedExtendedGcd.lean](SignedExtendedGcd.lean) |
| Shifts and magnitude bit length | [SignedShifts.lean][shifts], [length] |

[unsigned]: Operations.lean
[div]: DivisionOperations.lean
[rem]: RemainderOperations.lean
[sign]: SignedOperations.lean
[basic]: SignedArithmetic.lean
[add]: SignedAddition.lean
[mul]: SignedMultiplication.lean
[sdiv]: SignedDivision.lean
[gcd]: SignedGcd.lean
[shifts]: SignedShifts.lean
[length]: SignedBitLength.lean

## Choose the right contract

Signed arithmetic uses ordinary bounded integers with the canonical codec in
[Integers.lean](../Encoding/Integers.lean). Addition, subtraction,
multiplication,
and extended gcd derive sufficient result widths internally. Unsigned bounded
operations may require explicit nonoverflow conditions; do not carry those
implementation conditions into a public signed interface unnecessarily.

Use the pair-valued division operation when both results are needed, and bind
it once with `letThen`. Signed division uses Euclidean remainder conventions;
its only public divisor condition is nonzero. Gcd accepts zero operands.
Extended gcd returns actual integer coefficients with a proved bound.

Shift counts are mathematical size polynomials, not arbitrary binary-encoded
runtime operands. Right shift uses floor division. Magnitude bit length returns
a bounded mathematical natural. See each module's contract for width-zero and
negative-input behavior.

## Reuse and examples

Compose operations using the [computation rules](../Computation/README.md).
[NaturalArithmetic.lean](NaturalArithmetic.lean),
[SignedConstruction.lean](SignedConstruction.lean), and
[SignedWidth.lean](SignedWidth.lean) provide internal arithmetic adapters.
Use specialization rules for equal encodings; actual widening or narrowing is
a certified operation with its own contract.

Start with [Integers.lean](../Examples/Integers.lean) for signed arithmetic and
standalone TM0 certificates, [Division.lean](../Examples/Division.lean) for
unsigned division, or [Gcd.lean](../Examples/Gcd.lean) for gcd. Numeric examples
evaluate mathematical specifications; realization theorems certify the machines.

## Implementation work

Ripple arithmetic, bit folds, and binary scans are foundational components.
[BinaryRipple.lean](BinaryRipple.lean), [BitFold.lean](BitFold.lean), and
[BoundedTraversal.lean](BoundedTraversal.lean) share traversal and live-value
arguments. Reuse these before adding a controller; keep scratch representations
and tape traces out of application proofs.
