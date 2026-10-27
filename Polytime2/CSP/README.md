# Relational CSP foundations

[Project guide](../README.md)

[VerifierRealizable.lean](VerifierRealizable.lean) proves `language_inNP` for
any fixed finite relational template. `wordVerifier_polynomialTime` certifies
its total word verifier, including malformed-input rejection. Canonical
assignment witnesses have linear length. Empty templates, empty instances,
empty relations, and nullary constraints need no extra hypotheses.

[Basic.lean](Basic.lean) states the fixed-template hardness contract and defines
Taylor operations, relation-preserving polymorphisms, and rigid cores using
Mathlib's first-order structures and homomorphisms. It also proves that
singleton unary relations imply rigidity and that reflexive templates admit
constant homomorphisms.

[Instance.lean](Instance.lean) defines `Satisfiable` as existence of a Mathlib
homomorphism and proves its characterization by relation-preserving
assignments. `Instance L N` is Mathlib's structure on `Fin N`; use
`Instance.Satisfiable L input Carrier` when passing the input as data and
keeping the template interpretation fixed. The empty-variable theorem handles
nullary constraints without requiring an inhabited template.

[ThreeSAT.lean](ThreeSAT.lean) defines the eight-relation Boolean template and
proves the assignment and satisfiability equivalences with three-literal CNF.
`instanceOfFormula` uses the original variables; `formulaOfInstance` provides
the reverse mathematical presentation. Its reconstruction theorem preserves
every relation application. The shared clause semantics are in
[SAT/ThreeSAT.lean](../SAT/ThreeSAT.lean).

[Encoding.lean](Encoding.lean) gives dense instance codecs with exact widths
and canonical assignment codecs. [CheckerMath.lean](CheckerMath.lean) proves
preservation and the recursive checker's correctness without importing codecs
or machines. [Checker.lean](Checker.lean) states the public computation, and
[CheckerRealizable.lean](CheckerRealizable.lean) certifies
`assignmentChecker_realizable` by finite operations and array composition.
[CheckerAtCount.lean](CheckerAtCount.lean) certifies this checker at a parsed
variable count, with the named instance and assignment domains used by the
field decoders. Its preservation contract is independent of host capacity.

`instanceDomain_encode_surjective` proves that every exact-width bit pattern
represents a dense relational instance, including empty and nullary relations.
[ReadInstance.lean](ReadInstance.lean) uses that fact through the shared
`decodeFullCodec` rule. Strict binary validation and an exact-width guard
precede this interpretation; finite assignment codes are validated separately.

[ReadInstance.lean](ReadInstance.lean) connects a stored Boolean field to the
dense decoder. Its precondition is exactly equality of the stored length and
the dense instance width. `readDenseInstanceField_decodeWord` identifies its
result with canonical word decoding. A runtime width-test guard must precede
this partial reader. `decodeStoredInstance_realizable` composes that
guard and returns an optional structure for every stored Boolean field.
`decodeStoredInstance_correct` agrees with canonical decoding on all lengths,
so short and overlong fields reject before extraction.
[DecodeField.lean](DecodeField.lean) connects strict binary-letter validation
to that interface. `decodeInstanceWordField_realizable` certifies the total
decoder at a supplied variable count, and `decodeInstanceWordField_correct`
identifies its result with canonical word decoding for every stored field.

[DecodeAssignment.lean](DecodeAssignment.lean) certifies finite assignment-code
validation and decoding, including unused codes and empty carriers.
`assignmentCodesValid_realizable` checks an exactly
framed array, accepting iff every entry decodes. `decodeAssignmentCodes` uses
that guard to return an optional array of actual values. Its realization,
success criterion, and pointwise decoding contract are proved without an
inhabitance assumption. `assignmentBitBlocks` certifies framing exact-width
bits into scalar blocks. `decodeAssignmentBits_realizable` composes framing
and guarded decoding. `decodeAssignmentBits_correct` proves equality with the
canonical array decoder on every exact-width pattern; canonical assignments
round-trip and unused codes reject. `readAssignmentField` reads a stored
Boolean witness at the supplied variable count; its precondition is exactly
the mathematical assignment width. `decodeStoredAssignment_realizable` adds
the length guard, and `decodeStoredAssignment_wrong_length` proves rejection
of both truncated and overlong fields. `decodeStoredAssignment_correct`
identifies the result with canonical array-word decoding on every stored
Boolean field. `decodeAssignmentWordField_realizable` composes strict binary
validation with that decoder. `decodeAssignmentWordField_correct` identifies
its result with canonical array-word decoding on every stored word.
`decodeAssignmentWitnessField_realizable` transports that result to the named
assignment codec used by the checker. Its correctness theorem agrees with
`assignmentDomain.decodeWord` at the supplied variable count on every field.
[FieldCheck.lean](FieldCheck.lean) composes the two strict field decoders with
the checker at a supplied variable count. `fieldChecker_correct` identifies
both rejection branches and the successful mathematical checker call.
[InstanceWordCheck.lean](InstanceWordCheck.lean) composes strict stored-header
parsing with that checker. Its correctness theorem covers all original
instance and witness words at a supplied count.
[PairWordCheck.lean](PairWordCheck.lean) invokes it using the unary count frame
from [PrepareCount.lean](PrepareCount.lean), with agreement on every valid
header. `pairWordChecker_correct` identifies the answer with the mathematical
verifier on the corresponding encoded pair; callers supply no count.

[WordVerifier.lean](WordVerifier.lean) supplies decoding of instance words,
malformed input rejection, and the bounded-witness characterization of
satisfiability. `tableWordVerifier` is the shared mathematical check for exact
table and witness words; `wordVerifier_decodeInstance` proves that factoring
the header preserves the canonical instance-decoder specification.
[VerifierRealizable.lean](VerifierRealizable.lean) composes outer pair parsing
with that stored-pair check and exports the all-word runtime certificate.
`language_inNP` combines it with malformed-pair rejection and
`wordVerifier_witnesses`.

These are mathematical definitions and proofs. Generic polynomial reductions
and NP definitions are in the [complexity guide](../Complexity/README.md).
Solvers and hardness proofs remain open.
The [hardness task](../tasks/csp-taylor-hardness.md) records the remaining
steps.
The target problems and instance representation live in
[EXAMPLES.md](../../EXAMPLES.md#further-application-fixed-template-csp).
