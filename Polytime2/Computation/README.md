# Computation and composition

[Project guide](../README.md) · [Encoding](../Encoding/README.md)

Start with [Basic.lean](Basic.lean) for `Computation` and
[Realizable.lean](Realizable.lean) for its realization predicate. A computation
specifies named input domains, one output domain, admissibility, and a function
on admissible inputs, all indexed by mathematical sizes.

A realization hides the finite machine, scratch, and polynomial witnesses.
Application proofs must use certified mathematical rules. If a rule is missing,
add it to the foundation rather than unpacking a realization in a caller.

## Separate computation from its mathematical specification

Use `Computation.specification` in [Basic.lean](Basic.lean) to state the
mathematical answer independently of the implementation. Its result does not
unfold during ordinary conversion; use `specification_compute` explicitly when
an equation is needed. Keep the implementation private and certify the public
answer with `ready.specification`.

[Specification.lean](Specification.lean) provides two common variants:

- `decision` specifies a Boolean by a mathematical predicate;
  `ready.decision` certifies it from an equivalence with that predicate.
- `specificationBy` specifies a bounded answer through a mathematical
  observation. Supply existence in the exact output domain, then use
  `ready.specificationBy` with an injective observation to reuse the original
  realization without reconstructing bounds in application proofs.

For a scalar observation, `simp only [operation, specificationBy_correct]`
often proves the public contract directly. For structured observations, use
`specificationBy_correct _ operation.outputDomain _ observer _ _`,
then supply sizes and arguments. Lean infers the value and fit proof.
For large certificates, give argument producers their mathematical input
domains and precondition explicitly, and pass a named answer function to
`ready.specification`. [Smith reduction](../Matrices/IntegerSmithReduction.lean)
uses this to avoid inference through the enclosing computation.

Export a named mathematical contract for callers. Avoid adding the general
computation equations to the global simplifier. See
[integer feasibility](../Matrices/IntegerSystemFeasible.lean) for a predicate
and [Hermite columns](../Matrices/IntegerHermiteColumn.lean) for an observation
that forgets matrix bounds.
[Cyclic coordinates](../Arithmetic/CyclicCoordinate.lean) use a dependent pair
of a natural modulus and its actual `ZMod` element; the observation forgets
both bounds without exposing canonical representatives. These rules preserve
the chosen canonical codecs and exact widths; they introduce no new machine
implementation. For numeric examples, rewrite a mathematical observation
contract before evaluating the answer; `specificationBy` uses choice to supply
the bounded carrier, so evaluate its mathematical answer through the contract.

Use controlled specifications for recursive and multi-stage application
algorithms. Generic composition and traversal rules, elementary mathematical
operations, and structural constructors can remain transparent. Thin adapters
reuse the contracts and result boundary of their protected callees.

For dependent structural results, keep the mathematical index available.
[Array packing](../Arrays/PackingResult.lean) already returns the mathematical
count and retained values; `arrayPack_compute` gives their whole-pair equation.
Its transparent count supports dependent indexing without opening a machine or
traversal implementation.

## Choose a composition rule

| Intent | Rule and source |
| --- | --- |
| Feed one result to a unary computation | `followedBy`, [composition][seq] |
| Retain original arguments alongside a computed result | `letThen`, [seq] |
| Prepare arguments from shared inputs | `onResults`, [arguments][args] |
| Select distinct arguments | `withArguments`, [selection][select] |
| Select arbitrary arguments, including repeated names | `onArguments`, [args] |
| Pair, project, or map | `prodMk`, `fst`, `snd`, `prodMap`, [records] |
| Collect results in a record | [records] |
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
[records]: Records.lean

Use `letThen` when a continuation needs one computed value more than once.
`onResults` certifies independent argument producers on a shared immutable
context; it does not promise to evaluate common subexpressions only once.
`withPrecondition` strengthens admissibility, and `withSpecification` exposes a
mathematically equal answer without changing its domain.

[Optional.lean](Optional.lean) provides `ready.optionalGuard` for a partial
consumer behind a certified Boolean guard. Prove that an accepted guard
implies mathematical admissibility; rejection returns `none` without invoking
the consumer or requiring a default output. The word parsers share this rule.
`ready.guarded` in [Conditional.lean](Conditional.lean) supports a certified
fallback in the existing output domain. Use `none` for partial optional-result
consumers without nesting `Option`; `optionalGuard` reuses this branching rule.
`optionalBind_realizable` composes total optional-result decoders, skipping the
consumer when the source is absent. It also supports empty result carriers.
`optionalElim_realizable` supports an arbitrary result codec by combining a
certified empty branch and a total consumer. Optional bind specializes this
rule; the witness parser uses it with its substituted assignment codec.
`EncodedDomain.optional_encode_bits_congr` lifts encoding-preserving element
conversions to optional values, including inactive padding on rejection.
`optionalIsSome` and `optionalGet` certify presence testing and extraction;
the latter requires precisely presence.
[OptionalDecision.lean][optional decision] lifts a total Boolean decision to
optional inputs, rejecting any missing input before extracting payloads. The
CSP field checker uses this rule.
`optionalRename` moves size renaming inside an optional codec, preserving its
value and bits. The witness checker and header-payload parser share this rule.

[optional decision]: OptionalDecision.lean

Use `ready.fst` and `ready.snd` to project certified results, and
`firstReady.prodMk secondReady` to pair results on the same arguments and
precondition. `firstReady.prodMap secondReady` applies unary computations to
the two components of a pair; both component preconditions must hold.
`onArguments` selects a static family from a shared context, with no
injectivity obligation. Supply matching domains and the callee’s mathematical
admissibility proof. Use `onResults` when preparation computes new values.

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

[FullCodec.lean](FullCodec.lean) provides `decodeFullCodec` when every
exact-width bit pattern is valid, proved by surjectivity of the canonical
encoding. Its inverse preserves the bits and reuses the identity encoding map.
This supplies no validation for partial codecs. The
[dense-instance reader](../CSP/ReadInstance.lean) is a concrete caller.

[CodecDecode.lean](CodecDecode.lean) fixes the `decodeCanonicalBits` contract
without assuming an arbitrary codec is efficiently decodable.
`decodeCanonicalBits_of_full` certifies full codecs;
`decodeCanonicalBits_reindex` transports a certificate through a carrier
equivalence. [FixedArrayDecode.lean](FixedArrayDecode.lean) certifies arrays
over a specialization-fixed scalar codec at any polynomial length.
`decodeFixedArray_correct`, `decodeFixedArray_roundtrip`, and
`decodeFixedArray_some_iff` give canonical decoding, round trips, and success
criteria. `decodeFixedNamedArray_realizable` supplies ordinary named indices.
No default element or inhabited carrier is required. For external fields, pass
the exact-width certificate to the [stored-field rules][stored decode].

[stored decode]: ../Complexity/StoredFieldDecode.lean

[BooleanBits.lean](BooleanBits.lean) transports ordinary Boolean arrays to
exact little-endian bit vectors with unchanged canonical bits. It is used
between the stored-field reader and the dense-instance decoder.

For concrete patterns, see signed construction in
[SignedConstruction.lean](../Arithmetic/SignedConstruction.lean), the bounded
result in [SignedBitLength.lean](../Arithmetic/SignedBitLength.lean), and the
rejection branch in [PreparedOutcome.lean][outcome]. `withEncoding` and
`withEncodedOutput` remain foundational tools for constructing codecs.

[outcome]: ../Examples/SMP/PreparedOutcome.lean

## Sizes and loops

Use [Substitution.lean](Substitution.lean) for fixed polynomial size
assignments.
For a projection onto named caller sizes, use
[ParameterRename.lean](ParameterRename.lean). `ready.renameParameters` derives
the realization from polynomial substitution while exposing the directly
projected mathematical carriers and the existing renamed codecs.
Its proof uses the shared `EncodedDomain.substitute_X` equality; application
adapters can use constructor and composition laws from the
[encoding guide](../Encoding/README.md#widths-and-parameter-changes).
For sizes computed from input data, start with
[ComputedSizes.lean](ComputedSizes.lean) and
[ComputedCall.lean](ComputedCall.lean).
`atComputedUnarySizes` prepares a singleton argument record internally and
retains the actual sizes with the result. `atComputedSizeValue` observes the
ordinary dependent pair of the actual assignment and its payload, forgetting
bounded count storage. Callers prove the consumer's
precondition at those sizes. Working capacities and padding remain private.
[RetainUnary.lean](RetainUnary.lean) supplies `retainComputedUnarySize` when a
callee returns a unary count. It retains the already padded result at the
caller capacity without changing its value or scanning again.
[RetainBoolean.lean](RetainBoolean.lean) discards runtime count frames from a
Boolean result through field projection. The complete CSP verifier uses it
when returning from a prepared variable-count call.

For counts read from an unchanged host input, use
[ComputedHost.lean](ComputedHost.lean). `atComputedHostInput` retains a
size-dependent result; `atComputedHostSizes` returns a host-sized result and
removes the internal header. Both rules include count reading, size preparation,
and the callee's realization. Supply certified count readers and the callee's
mathematical admissibility proof. `withRenamedRecordArgument` supplies renamed
arguments from one host record without repeating codec transport proofs.
Use `atComputedHostSizes_compute` to evaluate a host-result call explicitly;
its result function has a reduction boundary for predictable proof checking.

For loops, use [While.lean](While.lean) with a mathematical invariant, a
strictly decreasing measure, and a polynomial bound. Progress is proof data,
not executable fuel. For a bounded number of updates, use
[Traversal.lean](Traversal.lean); array folds and transforms are described in
the [array guide](../Arrays/README.md).

Worked examples: [Context.lean](../Examples/Context.lean),
[Loop.lean](../Examples/Loop.lean), and
[DynamicSizes.lean](../Examples/DynamicSizes.lean).

## Foundational work

[ResizeBits.lean](ResizeBits.lean) certifies `BitVec.setWidth` at polynomial
source and target widths, including zero widths. It composes zero extension
and prefix projection; unary and stored-array capacity conversions reuse it.

[Layout.lean](Layout.lean) and [Fields.lean](Fields.lean) connect primitive
contracts to public computations. Tape placement, restoration, raw codec
arguments, and implementation witnesses belong here or in certified rule
implementations. See the [machine convention](../Machine/README.md) before
changing these proofs.
