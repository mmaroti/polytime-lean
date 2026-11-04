# Fixed-template CSP hardness from absence of a Taylor polymorphism

Status: steps 1--14 implemented; see the [CSP guide](../CSP/README.md),
[complexity guide](../Complexity/README.md), and [Cook-Levin guide][cook-levin].
Step 15 remains.
[Task index](../README.md#proposed-next-tasks).

## Statement and hypothesis correction

The requested reflexivity hypothesis does not support the intended hardness
argument. If every relation contains every constant tuple and the template is
nonempty, every instance has a constant homomorphism. Do not assert the
requested NP-completeness theorem with that hypothesis.

The working target instead uses a nonempty finite **rigid core** R over a
finite relational signature: every endomorphism is the identity. Including
every singleton unary relation is a sufficient normalization. If R has no
Taylor polymorphism, prove that CSP(R) is NP-complete under polynomial-time
many-one reductions. Do not confuse rigidity, the core property, and
reflexivity. This is the corrected contract used by the implementation.

CSP(R) asks whether a finite structure V of the same signature admits a
homomorphism V -> R. No symmetry, injectivity, or reflexivity is required of
instances. The template is fixed before choosing the reduction, machine, and
polynomial; these must work uniformly over all instances of that template.
No polynomial-time solver for CSP(R) is asserted.

## Sources and prerequisites

Use Zarathustra Brady, *Notes on CSPs and Polymorphisms*,
[arXiv:2210.07383][paper],
and the author's TeX sources [csp.tex][tex], [csp-notes.tex][main], and
[csp-append.tex][appendix]. The verified public source is on GitHub; a GitLab
version has not been identified. The source was checked at commit
`19d70550fe0bec75b7715d5c41005812f4fb965b`.

The relevant passages are section 0.4, "Crash course on NP-completeness"
(especially `thm-3-sat-np-complete`); section 1.1, "The Inv-Pol Galois
connection"; section 1.3, "Varieties, Birkhoff's HSP theorem, and the hardness
proof" (Theorems 1.3.1 and 1.3.6); section 1.4, "Cores and Idempotent
Reducts"; and section 1.5, "Taylor Algebras" (Theorem 1.5.2 and Corollary
1.5.7). Section and TeX identifiers take precedence over PDF pagination.
Prove any intermediate result used from these passages locally; citations are
mathematical provenance, not Lean dependencies.

Read the [computation](../Computation/README.md),
[encoding](../Encoding/README.md), and [TM0](../TM0/README.md) guides. Preserve
the relational instance contract in [EXAMPLES.md](../../EXAMPLES.md), and
coordinate the Boolean foundations with [3-SAT to CLIQUE][clique].

## Formalization milestones

Each milestone has a checkable deliverable. The complexity foundations and
algebraic representation proofs are substantial projects even though their
interfaces can be kept small.

1. **State the relational theorem (mathematics; implemented).** Fix a finite
   relational signature and a nonempty finite template R. Define preservation,
   Taylor polymorphisms, and rigid cores. Prove the constant-homomorphism
   observation above so the reflexive and rigid-core hypotheses cannot be
   confused. Deliverable: the mathematical hypotheses of the final theorem.

2. **Define instances and solutions (mathematics; implemented).** Represent
   an instance as a Mathlib structure on `Fin n`, with a solution an ordinary
   structure homomorphism to R. Prove equivalence with assignments preserving
   every input relation. Include empty variable sets and nullary relations.
   Deliverable: a machine-independent satisfiability predicate.

3. **Identify the Boolean source CSP (mathematics; implemented).** Define
   three-literal CNF satisfiability and the Boolean template with eight ternary
   relations, each excluding one tuple. Prove the assignment and satisfaction
   correspondences, allowing repeated variables. Deliverable: semantic
   conversions in both directions; step 7 certifies NP-hardness.

4. **Establish complexity contracts (certification; implemented).** Define
   word languages, polynomial-time many-one reductions, NP verifiers, and
   NP-completeness using the repository's machine conventions. Prove reduction
   composition and connect certified computations to these contracts. Specify
   canonical instance words and malformed-input rejection. Deliverable: exact
   statements that steps 5, 7, and 14 must certify.

5. **Certify CSP membership in NP (implemented).** Canonical assignment
   witnesses have linear length. The certified total verifier checks every
   enabled relation tuple, accepting exactly homomorphisms and rejecting all
   malformed framing and field encodings. Empty templates, empty instances,
   empty relations, and nullary constraints require no extra hypotheses.
   Deliverable: `language_inNP` and `wordVerifier_polynomialTime` in
   [VerifierRealizable.lean](../CSP/VerifierRealizable.lean). The
   [CSP guide](../CSP/README.md) links the mathematical and realization stages.

6. **Prove bounded machine computation has polynomial circuits.** For an
   arbitrary fixed verifier, construct a Boolean circuit for its bounded
   computation. Prove the transition simulation, acceptance equivalence, and
   polynomial circuit-size bound. Certify circuit construction using existing
   composition rules, including input preparation and output serialization.

   Implemented. [UniformVerifier.lean][uniform-verifier]
   exports `verifier_circuits_uniform`: every polynomial-time word verifier
   has a certified uniform constructor, polynomial gate bounds, and acceptance
   equivalence on every Boolean assignment. Invalid letter codes reject.
   `verifierProgram_polynomialTime` includes canonical length-input preparation,
   execution, and serialized output extraction. The time allowance is derived
   internally from the verifier's polynomial bound. The
   [construction guide](../Complexity/CookLevin/README.md) links the transition,
   finite-window, initial-wiring, guard, and output-reference proofs.

7. **Cook-Levin through 3-SAT (completed).** Implement and certify the Tseitin
   conversion from circuits to three-literal clauses, with both witness
   directions and polynomial output bounds. Compose with milestone 6 to
   prove every NP language reduces to 3-SAT. Do not assume 3-SAT hardness or
   replace this step with a citation. This completes the hardness foundation.

   Mathematical Tseitin conversion is implemented in
   [Tseitin.lean](../SAT/Tseitin.lean), including assignment extension and
   restriction, an exact `3 * gates + 1` clause count, and bounds on every
   variable reference. [TseitinProgram.lean](../SAT/TseitinProgram.lean)
   certifies the complete canonical conversion and serialized output.
   [FixedFormulaProgram.lean][fixed-formulas] composes the checked verifier
   constructor, framing, one-hot instance prefix, Tseitin conversion, and fixed
   unit clauses. It derives all internal sizes from the instance length and
   fixed polynomials. `np_formulas_uniform` gives every NP language a certified
   constructor whose output is satisfiable exactly for members of that language.
   [FixedWitness.lean](../Complexity/FixedWitness.lean) supplies its exact
   polynomial witness lengths through the certified padded verifier.
   [ThreeSATClauses.lean](../CSP/ThreeSATClauses.lean) proves the dense-table
   contract and satisfiability bridge for these clause arrays.
   [ThreeSATProgram.lean](../CSP/ThreeSATProgram.lean) certifies dense-table
   construction. [FixedInstanceProgram.lean][fixed-instances] composes it with
   the verifier formula constructor. [Reduction.lean][reduction] certifies
   native word framing, the all-word reduction `np_reduces_threeSAT`, and
   `CSP.ThreeSAT.language_npComplete` for the existing strict CSP word language.

8. **Define polymorphisms and their algebra (implemented).** View an n-ary
   polymorphism as a homomorphism from the relational power R^n to R. Prove
   closure under projections and composition, and prove rigid cores have
   idempotent polymorphisms. Reuse Mathlib's algebraic structures,
   substructures, products, terms, and homomorphisms wherever they fit.

   [Polymorphism.lean](../CSP/Polymorphism.lean) supplies the power structures,
   preservation/homomorphism equivalence, projection and composition closure,
   and rigid-core idempotence. The full polymorphism algebra uses Mathlib's
   language, structure, substructure, homomorphism, and term interfaces.
   `isPolymorphism_iff_term` and `hasTaylorPolymorphism_iff_term` connect this
   algebra to the existing mathematical predicates for subsequent steps.
   Nullary operations and relations are included.

9. **Prove the required finite Inv-Pol theorem (implemented).** Define
   primitive-positive formulas using conjunction, equality, and existential
   quantification.
   Prove preservation and the converse: every finite-arity relation on the
   finite carrier invariant under all polymorphisms of R is pp-definable
   over R. Treat empty relations and nullary cases explicitly; restrict the
   statement if their representation needs a separate argument.

   [PrimitivePositive.lean](../CSP/PrimitivePositive.lean) defines the fragment
   on Mathlib formulas and proves homomorphism and power preservation.
   [InvPol.lean](../CSP/InvPol.lean) proves `isPPDefinable_iff_invariant` on
   finite carriers and finite variable sets, without requiring a finite
   signature or an inhabited carrier. It includes operation arity zero;
   `isPPDefinable_empty_iff` and `isPPDefinable_nullary_iff` give the exact
   empty and nullary cases without adjoining falsehood to the syntax.

10. **Prove Taylor's algebraic criterion (implemented).** Formalize the needed
    part of section 1.5: an idempotent algebra satisfying identities that cannot
    all hold in projection algebras has a Taylor term. Apply the contrapositive
    to the full polymorphism algebra. Keep operation symbols and identities
    mathematical; do not introduce executable tests for absence of terms.

    [TaylorCriterion.lean](../CSP/TaylorCriterion.lean) proves the criterion
    for arbitrary sets of identities, with no carrier or signature finiteness
    assumptions. `hasProjectionModel_of_noTaylorPolymorphism` supplies a
    two-element projection interpretation satisfying all identities of the
    rigid core's full polymorphism algebra. The proof uses star composition,
    compactness of finite coordinate choices, and preservation of substitution;
    nullary symbols are excluded by idempotence in the non-Taylor case.

11. **Obtain a finite projection witness (implemented).** Starting from
    milestone 10's projection model, prove the finite Birkhoff steps needed to
    obtain it as a homomorphic image of a subalgebra of a finite power. Cover
    the possibly infinite operation signature of all polymorphisms. Use
    classical choice only to select data fixed by R, never an instance-dependent
    computation.

    [FiniteBirkhoff.lean](../CSP/FiniteBirkhoff.lean) constructs the finite
    single-source Birkhoff witness, with power dimension `|A| ^ |B|`. It uses
    term tables and identity satisfaction and requires no signature finiteness.
    [ProjectionWitness.lean](../CSP/ProjectionWitness.lean) supplies
    `exists_finite_projection_witness_of_noTaylorPolymorphism`: a projection
    interpretation on `Bool`, a substructure of the `|R|²`-fold power of the
    full polymorphism algebra, and a surjective Mathlib homomorphism. The
    choices depend only on the fixed template; compactness was proved in
    milestone 10.

12. **Extract finitely many gadgets over R (implemented).** Transfer the Boolean
    clause relations through the witness from milestone 11. Use milestone 9 to
    replace the resulting invariant relations by fixed pp-formulas in R's actual
    finite signature. Prove the Boolean-domain representation and clause
    contracts, including quotient representatives and equality. Output a finite
    gadget family independent of the input formula.

    [QuotientRelation.lean](../CSP/QuotientRelation.lean) proves preservation
    and pp-definability of lifted Boolean relations, with exact representation
    contracts. [BooleanGadgets.lean](../CSP/BooleanGadgets.lean) supplies
    `exists_boolean_gadgets_of_noTaylorPolymorphism`: the domain, equality,
    and eight clause formulas over the original language, together with a
    quotient section. `IsBooleanGadgetFamily` states correctness on arbitrary
    blocks; its representative theorems identify equality and the existing
    Three-SAT clause relations. All data is fixed by the template.

13. **Prove mathematical gadget expansion correct (implemented).** Replace each
    clause by its fixed gadget, allocating fresh auxiliary variables. Prove that
    an assignment extends to a target homomorphism iff it satisfies the source
    formula. Bound variable and constraint counts. This module must not import
    machines, codecs, runtime bounds, or realization infrastructure.

    [CanonicalGadget.lean](../CSP/CanonicalGadget.lean) realizes the fixed pp
    definitions as relational-power gadgets; [GadgetGluing.lean][gluing]
    combines fresh copies by boundary identification.
    [GadgetExpansion.lean](../CSP/GadgetExpansion.lean) proves the assignment
    extension and satisfiability equivalences, including repeated scopes and
    empty formulas. [GadgetExpansionBounds.lean][expansion-bounds] supplies
    uniform linear bounds on variables and distinct asserted constraints and
    `exists_bounded_expansion_of_noTaylorPolymorphism`. The target carrier is
    the mathematical quotient of the fresh variable sets; these modules have
    no codec, machine, or realization imports.

14. **Certify a generic fixed-gadget compiler.** Attach canonical encodings
    and a `Computation` specification to milestone 13. Certify renaming,
    allocation, and constraint insertion through existing array, traversal,
    and composition rules. Implement boundary identification and numbering of
    quotient variables. Output the dense relational tables specified in
    EXAMPLES.md; fixed arities make their widths polynomial. Prove bounds
    relative to source input length, including unary size headers, and export
    a standalone TM0 realization. Keep tape arguments in foundational rules.

    Implemented; the standalone native export is
    `gadgetCompilerInstance_polynomialTime` in
    [GadgetExport.lean](../CSP/GadgetExport.lean).
    `Arrays/QuotientNumbering.lean` certifies equation-class labels and packs
    exactly one representative per class. `CSP/QuotientProgram.lean` certifies
    canonical dense relation images at a supplied class count and proves their
    satisfiability contract. `CSP/QuotientCompiler.lean` connects label and
    representative preparation to dense output at the actual class count;
    `CSP/QuotientExport.lean` exports this component with serialized-input
    bounds. `quotientCompiler_satisfiable_iff` connects its computed output to
    the mathematical solution contract. `CSP/GadgetExpansionAllocation.lean`
    proves that a uniform pool and collapse equations give exactly the
    original variable quotient, with a linear raw allocation size.
    `CSP/GadgetRawInstance.lean` now certifies canonical dense raw tables,
    with exactly the placed domain and clause relations. Its address programs
    reuse the polynomial evaluator; fact insertion uses shared array and
    table materialization rules. `allocatedEquations_respects_iff` reduces
    the mathematical equation contract to pool projections and boundary
    endpoints. `CSP/GadgetEquationArrays.lean` certifies the complete equation
    array at a fixed multiple of the raw allocation size and proves its exact
    assignment contract. `CSP/GadgetCompiler.lean` composes both generators
    with quotient compilation and proves that its solutions are exactly
    assignments preserving the raw relations and equations. The mathematical
    `allocated_satisfiable_iff_assignments` gives the matching universal
    property of the original allocated quotient. `CSP/GadgetSourceLayout.lean`
    connects the clause-array and list layouts, including scopes and equation
    assignments. `CSP/GadgetCompilerCorrect.lean` proves the complete Boolean
    satisfiability correspondence through that mathematical quotient.
    `CSP/GadgetCompilerCardinality.lean` proves that the computed class count
    is exactly the mathematical expansion cardinality.
    `CSP/GadgetWordBounds.lean` exposes the ordinary sized-instance result and
    bounds its native word by a polynomial in the complete serialized source,
    including unary headers. `CSP/GadgetWordCompiler.lean` reuses the original
    argument preparation with `CSP/QuotientWordCompiler.lean`, producing the
    exact native instance word through the shared coded-stream export.
    `TM0/TrackOutput.lean` now shares one nonblank-symbol extraction proof
    between native symbols and the existing binary formatter.
    `TM0/BlockDecoder.lean` certifies fixed-block decoding to native symbols,
    stopping at a rejected sentinel, with output-head restoration and a
    linear time bound. `TM0/NativeTrackOutput.lean` extracts the native tape
    from simulator rows. `Complexity/BlockDecode.lean` composes the standalone
    decoder with raw preparation, simulation, and extraction under one
    word-length polynomial. `Complexity/NativeStream.lean` certifies the exact
    header, canonical payload, and absent sentinel. The computed-size variant
    retains capacity through `Arrays/ComputedPadding.lean`, interpreting
    existing zero padding as absent letters. `codedArray_polynomialTime`
    exports the resulting array to the exact mathematical instance word.
    Its finite TM0 witness bounds execution and output length in the complete
    serialized source. No internal frame or capacity padding survives.

15. **Assemble and audit NP-completeness.** Compose milestones 7 and 14 for
    hardness, and use milestone 5 for membership. Export the theorem with
    only finite relational, rigidity, and Taylor hypotheses. Audit dependency
    closure, public statements, polynomial size bridges, and edge cases.
    Build all changed Lean modules, update authoritative guides, and remove
    completed task entries when the full theorem is achieved.

## Proof reuse and acceptance

Adapt available mathematical proofs of preservation, compactness, finite HSP,
and semantic reductions. Translate them to this repository's Mathlib carriers
and conventions, retain appropriate attribution, and copy their necessary
mathematical dependencies into the repository. Do not import another project's
signature hierarchy, algorithm models, transducers, encodings, or cost claims.
Do not copy unused generalizations merely because they are available.
Imported mathematical arguments must compile locally with only Mathlib and
this repository; the source project must not become a build dependency.
Review each adapted theorem's hypotheses and conclusion before translating its
proof, independently of any algorithm representation in its source.

The pure mathematics ends at the finite gadget family and its satisfaction
contracts. Its existence proof may be nonconstructive because R is fixed.
The generic compiler supplies the polynomial-time algorithm; the algebraic
proof must not construct machines or inspect encodings. NP membership and
Cook-Levin are independent reusable foundations.

Keep the interfaces between steps explicit: steps 8--12 produce fixed
mathematical gadget data; step 13 proves its semantic expansion contract;
step 14 realizes that contract using the existing algorithm framework. Steps
1--3 and 8--13 are mathematical work. Steps 4--7 and 14 combine mathematical
correctness with complexity certification; step 15 composes the results.
These are small deliverables for planning, not claims that the algebraic or
Cook-Levin proofs are individually easy.

Acceptance requires a Lean codebase depending only on this repository and
Mathlib's dependency closure, with no `sorry`, unproved complexity assumptions,
or added axioms beyond Lean's standard foundations. Ordinary word encodings
must reject malformed inputs, and no hardness claim may rely solely on a
semantic map or output-size bound. Do not claim logspace complexity. Report
Lean lines added and removed for every completed milestone.

[tex]: https://github.com/notzeb/all/blob/master/csp.tex
[main]: https://github.com/notzeb/all/blob/master/csp-notes.tex
[appendix]: https://github.com/notzeb/all/blob/master/csp-append.tex
[paper]: https://arxiv.org/abs/2210.07383
[clique]: 3-sat-to-clique.md
[cook-levin]: ../Complexity/CookLevin/README.md
[uniform-verifier]: ../Complexity/CookLevin/UniformVerifier.lean
[fixed-formulas]: ../Complexity/CookLevin/FixedFormulaProgram.lean
[fixed-instances]: ../Complexity/CookLevin/FixedInstanceProgram.lean
[reduction]: ../Complexity/CookLevin/Reduction.lean

[gluing]: ../CSP/GadgetGluing.lean
[expansion-bounds]: ../CSP/GadgetExpansionBounds.lean
