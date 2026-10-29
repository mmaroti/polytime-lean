# Arithmetic

[Project guide](../README.md) · [Composition](../Computation/README.md)

Choose the mathematical operation before looking at its machine. Public
computations and their realization theorems are in the modules below; exact
preconditions and result bounds live in their Lean declarations and docstrings.

| Need | Interface modules |
| --- | --- |
| Bounded natural polynomial evaluation | [NaturalPolynomial.lean][poly] |
| Unsigned addition, subtraction, multiplication | [Operations.lean][unsigned] |
| Unsigned quotient and remainder together | [DivisionOperations.lean][div] |
| A remainder projection | [RemainderOperations.lean][rem] |
| Unsigned gcd | [GcdOperations.lean](GcdOperations.lean) |
| Sign, magnitude, zero, negation | [SignedOperations.lean][sign], [basic] |
| Signed comparisons | [SignedComparison.lean](SignedComparison.lean) |
| Total divisibility test, including zero divisors | [SignedDivides.lean][dvd] |
| Signed addition and multiplication | [SignedAddition.lean][add], [mul] |
| Two-term combination, with shared or separate input widths | [two] |
| Signed multiply-add with derived width | [SignedMultiplyAdd.lean][madd] |
| Signed Euclidean division and gcd | [SignedDivision.lean][sdiv], [gcd] |
| Total signed quotient and remainder | [SignedQuotient.lean][total] |
| Normalize cyclic/free coordinates | [CyclicCoordinate.lean][cyclic] |
| Gcd and signed lcm together, including zero | [SignedGcdLcm.lean][lcm] |
| Bézout coefficients | [SignedExtendedGcd.lean][extended] |
| Normalized Bézout coefficients | [NormalizedBezout.lean][norm] |
| Shifts and magnitude bit length | [SignedShifts.lean][shifts], [length] |
| Compare stored unary counts with polynomial sizes | [UnaryWidth.lean][unary] |
| Read a unary count as a binary index | [UnaryToIndex.lean][unary-index] |

[poly]: NaturalPolynomial.lean
[total]: SignedQuotient.lean
[cyclic]: CyclicCoordinate.lean
[unsigned]: Operations.lean
[div]: DivisionOperations.lean
[rem]: RemainderOperations.lean
[sign]: SignedOperations.lean
[dvd]: SignedDivides.lean
[basic]: SignedArithmetic.lean
[add]: SignedAddition.lean
[mul]: SignedMultiplication.lean
[madd]: SignedMultiplyAdd.lean
[two]: SignedTwoProducts.lean
[sdiv]: SignedDivision.lean
[gcd]: SignedGcd.lean
[lcm]: SignedGcdLcm.lean
[shifts]: SignedShifts.lean
[length]: SignedBitLength.lean
[extended]: SignedExtendedGcd.lean
[norm]: NormalizedBezout.lean
[unary]: UnaryWidth.lean
[unary-index]: UnaryToIndex.lean

`boundedUnaryEqualsPolynomial` compares a stored count with the requested
mathematical size. Its shared unary capacity is derived internally by
`boundedUnaryWidenTo`; widening preserves the count and appends canonical zeros.

Extended gcd and normalized Bézout computations have controlled result
boundaries. Use `integerExtendedGcd_value` and
`integerNormalizedExtendedGcd_value` for ordinary integer triples, then their
`_correct` theorems for the gcd and Bézout identities. Full bounded-carrier
equations live under `Realizable.Internal` for realization proofs.

## Choose the right contract

Signed arithmetic uses ordinary bounded integers with the canonical codec in
[Integers.lean](../Encoding/Integers.lean). Addition, subtraction,
multiplication, and extended gcd derive sufficient result widths internally.
Unsigned bounded operations may require explicit nonoverflow conditions; do
not carry those implementation conditions into a public signed interface
unnecessarily.

Use the pair-valued division operation when both results are needed, and bind
it once with `letThen`. Signed division uses Euclidean remainder conventions;
its only public divisor condition is nonzero. Gcd accepts zero operands.
Extended gcd returns actual integer coefficients with a proved bound. Use
[normalized extended gcd][norm] when a matrix reduction needs linear returned
coefficient widths. It computes extended gcd once and normalizes the result,
including the coefficient pair `(1,0)` for zero inputs.

Shift counts are mathematical size polynomials, not arbitrary binary-encoded
runtime operands. Right shift uses floor division. Magnitude bit length returns
a bounded mathematical natural. See each module's contract for width-zero and
negative-input behavior.

`polynomialPosition bounds expression limit` evaluates a fixed Mathlib
`MvPolynomial (Parameter ⊕ Argument) ℕ`. Left variables read mathematical sizes;
right variables read runtime coordinates in the supplied intervals. Its result
is the exact natural value below `limit`. Only the final fit inequality is a
precondition; intermediate widths are derived inside the realization.

Use `MvPolynomial.rename Sum.inl` to embed an existing size polynomial.
Simplify concrete formulas with the specialized `MvPolynomial.eval_add`,
`eval_mul`, `eval_C`, and `eval_X` lemmas.
[WitnessEndpoints.lean](../Complexity/WitnessEndpoints.lean) evaluates several
formulas under one mathematical fit condition;
[BlockBase.lean](../Complexity/CookLevin/BlockBase.lean) combines runtime
coordinates with polynomial size values. Both retain their original codecs.

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

[UnaryWidth.lean][unary] also provides `boundedUnaryResize` for increasing a
count's capacity under a proved capacity comparison. The additive widening
interface specializes this rule. Both retain the actual count.

Ripple arithmetic, bit folds, and binary scans are foundational components.
[BinaryRipple.lean](BinaryRipple.lean), [BitFold.lean](BitFold.lean), and
[BoundedTraversal.lean](BoundedTraversal.lean) share traversal and live-value
arguments. Reuse these before adding a controller; keep scratch representations
and tape traces out of application proofs.

[UnarySuccessor.lean](UnarySuccessor.lean) increments a bounded unary count
strictly below capacity, reusing array snoc, Boolean counting, and projection.
[Its examples][unary successor example] cover zero, the last available rank,
and full-capacity rejection, with a TM0 certificate.

[unary successor example]: ../Examples/UnarySuccessor.lean
