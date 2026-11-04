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

[Polymorphism.lean](Polymorphism.lean) identifies relation preservation with a
Mathlib homomorphism from the coordinatewise relational power. It proves
projection and composition closure and idempotence from rigidity, including
zero operation arity and nullary relations, without finiteness assumptions.
`polymorphismLanguage` and `polymorphismAlgebra` give the full operation
signature and its Mathlib structure on the original carrier. Template relations
are Mathlib substructures of its powers. `isPolymorphism_iff_term` identifies
its term operations with polymorphisms; `hasTaylorPolymorphism_iff_term`
connects the existing Taylor predicate to this algebra's terms. These
foundations import no codecs, machines, or realization infrastructure.

[PrimitivePositive.lean](PrimitivePositive.lean) defines the primitive-positive
fragment on Mathlib formulas: atomic relations and equality, truth, conjunction,
and existential quantification, without parameters or a falsehood constructor.
`IsPPDefinable.invariant` proves preservation under all polymorphisms.
[InvPol.lean](InvPol.lean) proves `isPPDefinable_iff_invariant` for finite
carriers and finite variable sets, with no signature-finiteness or inhabitance
assumptions. Its proof existentially quantifies a finite operation table.
Operation arity zero is included: `isPPDefinable_empty_iff` characterizes empty
relations by absence of nullary polymorphisms; `isPPDefinable_nullary_iff`
handles the two nullary truth values. These are mathematical existence results,
with no machine, codec, or algorithm certificate.

[TaylorCriterion.lean](TaylorCriterion.lean) proves Taylor's criterion for
idempotent algebras: a set of identities unsatisfiable by projections forces a
Taylor term (`hasTaylorTerm_of_nontrivial_identities`). Its contrapositive,
`hasProjectionModel_of_not_hasTaylorTerm`, supplies a projection interpretation
on `Bool` satisfying the algebra's entire equational theory. The proof uses
[star composition](TaylorTerm.lean) and
[compactness of finite coordinate choices](TaylorCoordinates.lean), without
carrier or signature finiteness. `hasProjectionModel_of_noTaylorPolymorphism`
applies it to the full polymorphism algebra of a rigid core.

[FiniteBirkhoff.lean](FiniteBirkhoff.lean) proves
`exists_finite_power_surjective_hom`: if every identity of a finite algebra `A`
holds in a finite algebra `B`, a Mathlib substructure of the
`|A| ^ |B|`-fold power of `A` surjects onto `B`. The proof factors target
term evaluation through source term tables, without enumerating the signature
or assuming either carrier inhabited.
[ProjectionWitness.lean](ProjectionWitness.lean) specializes this to the full
polymorphism algebra of a finite rigid core without a Taylor polymorphism.
`exists_finite_projection_witness_of_noTaylorPolymorphism` supplies a projection
interpretation on `Bool`, a substructure of the `|R|²`-fold power, and a
surjective homomorphism. All choices depend only on the fixed template.

[QuotientRelation.lean](QuotientRelation.lean) defines `Represents` and
`liftedRelation` for tuple blocks and their Boolean quotient values. It proves
unique representation values, validity exactly on the subalgebra, and
preservation of lifted relations by all template polymorphisms. Finite Inv–Pol
then supplies their pp definitions.
[BooleanGadgets.lean](BooleanGadgets.lean) exports
`exists_boolean_gadgets_of_noTaylorPolymorphism`: a fixed domain formula,
quotient-equality formula, eight clause formulas, and a quotient section
representing both Booleans. `IsBooleanGadgetFamily` states their positivity and
contracts on arbitrary blocks. Its `domain`, `equality`, `clause`, and
`clause_on_section` theorems give the representation and Three-SAT semantics.
All formulas use the original signature and block dimension `|R|²`, with no
input formula involved in their selection.

[CanonicalGadget.lean](CanonicalGadget.lean) realizes each pp-definable relation
by a finite relational-power gadget. Boundary columns may coincide, expressing
equality by variable identification. The construction favors proof reuse;
gadget sizes are fixed by the template, with no efficiency claim about those
constants. [GadgetGluing.lean](GadgetGluing.lean) allocates disjoint copies per
occurrence and identifies their boundaries with shared variables. Its quotient
structure has exactly the images of the gadget relation facts.
[GadgetExpansion.lean](GadgetExpansion.lean) attaches a domain gadget to each
source variable and a clause gadget to each clause occurrence.
`assignment_extends_iff` gives the Boolean assignment-extension contract;
`satisfiable_iff` identifies source satisfiability with a target homomorphism.
[GadgetExpansionBounds.lean](GadgetExpansionBounds.lean) exports
`exists_bounded_expansion_of_noTaylorPolymorphism`, combining correctness with
variable and constraint counts bounded by `C * (N + formula.length)` for one
fixed `C`. Constraints mean distinct enabled relation facts, including nullary
facts. These modules import only mathematical foundations.

[GadgetExpansionAllocation.lean](GadgetExpansionAllocation.lean) gives a
uniform finite pool for every occurrence. Its projection equations collapse
unused slots, and `allocatedQuotientEquiv` identifies the resulting variable
quotient with the original expansion. `allocatedVariables_card` gives its
linear raw size. [GadgetAllocation.lean](GadgetAllocation.lean) supplies the
underlying retraction and quotient proofs. These modules are mathematical;
constructing and certifying the raw relation tables and equation arrays
remains open.

[QuotientProgram.lean](QuotientProgram.lean) certifies dense relation images
from a raw instance, vertex labels, and output representatives. Its
`quotientInstanceProgram_satisfiable_iff` contract identifies solutions with
raw assignments respecting the equations. The class count is supplied as a
size parameter. [QuotientCompiler.lean](QuotientCompiler.lean) computes that
count and the representatives from equations, then calls the dense compiler
through [QuotientAtCount.lean](QuotientAtCount.lean). Only the actual class
count remains in the result frame; `quotientCompiler_count` identifies it with
the quotient cardinality. `quotientCompiler_satisfiable_iff` proves that its
solutions are exactly original assignments respecting the equations;
`quotientAtCount_compute` identifies the actual stored-count output with its
mathematical relation images.
[QuotientExport.lean](QuotientExport.lean) supplies
TM0 and serialized-input polynomial-time certificates for this component.
Fixed-gadget compilation and native output build on this component; see
[GadgetExport.lean](GadgetExport.lean).
[QuotientInstanceMath.lean](QuotientInstanceMath.lean) states the
mathematical quotient contract independently of codecs and machines.
[InstanceProgram.lean](InstanceProgram.lean) supplies certified relation
projection and assembly from scope tables or scalar queries.
[ScopeProgram.lean](ScopeProgram.lean), [ScopeLookup.lean](ScopeLookup.lean),
and [ScopeSearch.lean](ScopeSearch.lean) provide canonical tabulation, lookup,
and existential search, including nullary relations and empty domains.

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

[GadgetRawInstance.lean](GadgetRawInstance.lean) certifies the raw dense gadget
instance from a source clause array. Its relation contract is exactly the
placed domain and clause pool relations.
[GadgetPositions.lean](GadgetPositions.lean)
certifies allocation addresses through the polynomial evaluator;
[InstanceMaterialize.lean](InstanceMaterialize.lean) and
[RelationMaterialize.lean](RelationMaterialize.lean) insert optional tuple
facts into canonical dense tables, including nullary and empty cases.
`allocatedEquations_respects_iff` in
[GadgetExpansionAllocation.lean](GadgetExpansionAllocation.lean) specifies the
pool projections and boundary equations.
[GadgetEquationArrays.lean](GadgetEquationArrays.lean) certifies their array,
whose length is a fixed multiple of the raw allocation size. Its
`gadgetEquationArray_respects_iff` contract removes repeated row entries and
states the exact mathematical endpoint equalities.
[GadgetCompiler.lean](GadgetCompiler.lean) composes the generated tables and
equations with the quotient compiler at the raw allocation size. Its
`gadgetCompiler_satisfiable_iff_raw` theorem identifies solutions with
assignments preserving the raw relations and equations.
[GadgetSourceLayout.lean](GadgetSourceLayout.lean) identifies the clause-array
and list occurrences, scopes, gadget choices, and raw allocated numbering;
these mathematical lemmas require no codec or machine infrastructure.
[GadgetCompilerCorrect.lean](GadgetCompilerCorrect.lean) proves
`gadgetCompiler_satisfiable_iff`: for any fixed Boolean pp gadget family,
the computed dense quotient is satisfiable exactly when the original clause
array is satisfiable.
[GadgetCompilerCardinality.lean](GadgetCompilerCardinality.lean) identifies the
generated equation quotient with the mathematical allocation and proves its
exact output cardinality. [GadgetWordBounds.lean](GadgetWordBounds.lean) exposes
`gadgetCompilerInstance` as an ordinary size and dense instance, with the same
solution and cardinality contracts. Its native instance word has polynomial
length in the full serialized source, including unary headers.
[GadgetWordCompiler.lean](GadgetWordCompiler.lean) reuses the same preparation
with the native-word quotient consumer in
[QuotientWordCompiler.lean](QuotientWordCompiler.lean).
[GadgetExport.lean](GadgetExport.lean) supplies
`gadgetCompilerInstance_polynomialTime`: a finite standalone TM0 certificate
for the exact native instance word, including its computed count header and
dense tables. The output has no internal frame or capacity padding.

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
