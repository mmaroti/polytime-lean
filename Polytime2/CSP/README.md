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
[ThreeSATClauses.lean](ThreeSATClauses.lean) identifies canonical clause arrays
with these relations: each dense table entry tests occurrence of the clause
with that pattern and scope. Forgetting finite variable bounds preserves
satisfiability. [ThreeSATProgram.lean](ThreeSATProgram.lean) certifies the full
dense-table compiler through equality, array membership, and tabulation. Its
output is the existing instance codec on exactly the formula's variable set.
[WordOutput.lean](WordOutput.lean) certifies native instance-word output.
The [Cook-Levin reduction](../Complexity/CookLevin/Reduction.lean) exports
`ThreeSAT.language_npComplete` for the existing strict word language.

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
Its structural proof reuses the shared Boolean, array, record, and reindex
surjectivity rules; `instanceDomain_decode_total` follows from the shared
encoder-surjectivity/decoder-totality equivalence.
[ReadInstance.lean](ReadInstance.lean) supplies `instanceFieldBits_realizable`
through the shared full-codec decoder and specializes total Boolean-field
reading as `decodeStoredInstance`. Its canonical contract covers every stored
length, so truncated and overlong fields reject before extraction.
[DecodeField.lean](DecodeField.lean) specializes the shared stored-word rule
as `decodeInstanceWordField`. Its correctness theorem agrees with canonical
instance-word decoding on every field, including nonbinary letters.

[DecodeAssignment.lean](DecodeAssignment.lean) specializes
[fixed-array decoding](../Computation/FixedArrayDecode.lean) to the template
carrier. `decodeAssignmentBits_realizable` certifies canonical decoding without
an inhabitance assumption. Scalar validation, bit framing, round trips, and
success criteria belong to the shared rule; unused scalar codes reject.
`decodeStoredAssignment` uses the same generic Boolean-field reader as dense
instances, and `decodeStoredAssignment_wrong_length` covers both truncation
and overlong witnesses. `decodeAssignmentWitnessField` uses the generic
[stored-word decoder](../Complexity/StoredFieldDecode.lean) and returns the
named assignment codec directly. Its correctness theorem agrees with
`assignmentDomain.decodeWord` at the supplied variable count on every field.
All three decoders preserve empty carriers, empty arrays, and zero-width codes.
The former partial field readers are replaced by the shared `readStoredBits`
interface; field extraction and rejection proofs are no longer duplicated in
CSP modules.

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
Solvers and the Taylor-hardness proof remain open.
The [hardness task](../tasks/csp-taylor-hardness.md) records the remaining
steps.
The target problems and instance representation live in
[EXAMPLES.md](../../EXAMPLES.md#further-application-fixed-template-csp).
