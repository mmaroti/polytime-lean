# Computation and composition

[Project guide](../README.md) · [Encoding](../Encoding/README.md)

Start with [Basic.lean](Basic.lean) for `Computation` and
[Realizable.lean](Realizable.lean) for its realization predicate. A computation
specifies named input domains, one output domain, admissibility, and a function
on admissible inputs, all indexed by mathematical sizes.

A realization hides the finite machine, scratch, and polynomial witnesses.
Application proofs must use certified mathematical rules. If a rule is missing,
add it to the foundation rather than unpacking a realization in a caller.

## Choose a composition rule

| Intent | Rule and source |
| --- | --- |
| Feed one result to a unary computation | `followedBy`, [composition][seq] |
| Retain original arguments alongside a computed result | `letThen`, [seq] |
| Prepare arguments from shared inputs | `onResults`, [arguments][args] |
| Select arguments from a context | `withArguments`, [selection][select] |
| Collect results in a product or record | [Records.lean](Records.lean) |
| Pass an argument family on one record tape | [RecordArguments.lean][args] |
| Branch on a Boolean or mathematical sum | [Branch.lean][branch], [sums] |
| Certify a computation under complementary guards | [Conditional.lean][cases] |
| Restrict or replace a specification | [realization][real] |

[seq]: Composition.lean
[args]: RecordArguments.lean
[select]: Arguments.lean
[branch]: Branch.lean
[cases]: Conditional.lean
[sums]: Sums.lean
[real]: Realizable.lean

Use `letThen` when a continuation needs one computed value more than once.
`onResults` certifies independent argument producers on a shared immutable
context; it does not promise to evaluate common subexpressions only once.
`withPrecondition` strengthens admissibility, and `withSpecification` exposes a
mathematically equal answer without changing its domain.

[Equality.lean](Equality.lean) compares elements of any canonical encoded domain
by mathematical equality, reusing the certified bit comparison.
[Swap.lean](Swap.lean) exchanges two mathematical values using these tests and
conditional selection.

## Change mathematical representations

[Reindex.lean](Reindex.lean) provides three specialization steps:

1. `reinterpretInputs` changes input carriers through encoding-preserving maps
   and a proof that the new precondition permits the original computation.
2. `refineOutput` adds a predicate proved for every result on admissible inputs.
   The output becomes a subtype using the original canonical bits; the predicate
   is not checked at runtime.
3. `reinterpretOutput` applies a total encoding-preserving output map. Refine
   first when the conversion needs a proved result property.

Use `reindexDomains` for equivalences on inputs and output, or `reindexOutput`
when the target output codec is constructed by reindexing. Matching widths are
separate obligations, including when a carrier is empty. These rules change
mathematical meaning without requiring a new calling convention.

For concrete patterns, see signed construction in
[SignedConstruction.lean](../Arithmetic/SignedConstruction.lean), the bounded
result in [SignedBitLength.lean](../Arithmetic/SignedBitLength.lean), and the
rejection branch in [PreparedOutcome.lean][outcome]. `withEncoding` and
`withEncodedOutput` remain foundational tools for constructing codecs.

[outcome]: ../Examples/SMP/PreparedOutcome.lean

## Sizes and loops

Use [Substitution.lean](Substitution.lean) for fixed polynomial size
assignments.
For sizes computed from input data, start with
[ComputedSizes.lean](ComputedSizes.lean) and
[ComputedCall.lean](ComputedCall.lean).
`atComputedUnarySizes` prepares a singleton argument record internally and
retains the actual sizes with the result. Callers prove the consumer's
precondition at those sizes. Working capacities and padding remain private.

For loops, use [While.lean](While.lean) with a mathematical invariant, a
strictly decreasing measure, and a polynomial bound. Progress is proof data,
not executable fuel. For a bounded number of updates, use
[Traversal.lean](Traversal.lean); array folds and transforms are described in
the [array guide](../Arrays/README.md).

Worked examples: [Context.lean](../Examples/Context.lean),
[Loop.lean](../Examples/Loop.lean), and
[DynamicSizes.lean](../Examples/DynamicSizes.lean).

## Foundational work

[Layout.lean](Layout.lean) and [Fields.lean](Fields.lean) connect primitive
contracts to public computations. Tape placement, restoration, raw codec
arguments, and implementation witnesses belong here or in certified rule
implementations. See the [machine convention](../Machine/README.md) before
changing these proofs.
