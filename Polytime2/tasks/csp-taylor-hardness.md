# Fixed-template CSP hardness from absence of a Taylor polymorphism

Status: step 1 implemented in [CSP/Basic.lean](../CSP/Basic.lean).
Step 2 is next.
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

Use Zarathustra Brady, *Notes on CSPs and Polymorphisms*, arXiv:2210.07383,
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

## Remaining implementation milestones

Each milestone has a checkable deliverable. The complexity foundations and
algebraic representation proofs are substantial projects even though their
interfaces can be kept small.

2. **Define relational CSP using Mathlib.** Reuse `FirstOrder.Language`,
   `IsRelational`, `Structure`, and `Hom`. Define satisfiability by
   `Nonempty (V ->[L] R)` and prove its assignment characterization. Use
   `Fin N` for encoded instance carriers. Keep satisfiability separate from
   the existence of a polynomial-time decision algorithm.

3. **Identify 3-SAT as a relational CSP.** On `Bool`, use eight ternary
   relations, each excluding one Boolean triple. Prove equivalence with lists
   of three-literal clauses, allowing repetitions. Cover zero clauses,
   repeated variables, and unused variables. Reuse these definitions for
   the other reduction tasks.

4. **Define polynomial reductions and NP.** Use languages of finite words,
   polynomially bounded witnesses, and deterministic polynomial-time Turing
   verifiers. Reuse Mathlib's machine semantics. Define many-one reductions,
   NP-hardness, and NP-completeness; prove composition and establish the
   bridge from Polytime2 realizations to the chosen complexity definitions.
   Define malformed-input rejection and input length explicitly.

5. **Certify CSP membership in NP.** Encode assignments and certify the
   checker that tests preservation of every enabled relation tuple. Prove
   acceptance iff a homomorphism exists, and bound witness length and runtime
   polynomially in the serialized instance length. Handle empty relations,
   empty instances, and nullary constraints.

6. **Prove bounded machine computation has polynomial circuits.** For an
   arbitrary fixed verifier, construct a Boolean circuit for its bounded
   computation. Prove the transition simulation, acceptance equivalence, and
   polynomial circuit-size bound. Certify circuit construction using existing
   composition rules, including input preparation and output serialization.

7. **Finish Cook-Levin through 3-SAT.** Implement and certify the Tseitin
   conversion from circuits to three-literal clauses, with both witness
   directions and polynomial output bounds. Compose with milestone 6 to
   prove every NP language reduces to 3-SAT. Do not assume 3-SAT hardness or
   replace this step with a citation. This completes the hardness foundation.

8. **Define polymorphisms and their algebra.** View an n-ary polymorphism as
   a homomorphism from the relational power R^n to R. Prove closure under
   projections and composition, and prove rigid cores have idempotent
   polymorphisms. Reuse Mathlib's algebraic structures, substructures,
   products, terms, and homomorphisms wherever they fit.

9. **Prove the required finite Inv-Pol theorem.** Define primitive-positive
   formulas using conjunction, equality, and existential quantification.
   Prove preservation and the converse: every finite-arity relation on the
   finite carrier invariant under all polymorphisms of R is pp-definable
   over R. Treat empty relations and nullary cases explicitly; restrict the
   statement if their representation needs a separate argument.

10. **Prove Taylor's algebraic criterion.** Formalize the needed part of
    section 1.5: an idempotent algebra satisfying identities that cannot all
    hold in projection algebras has a Taylor term. Apply the contrapositive
    to the full polymorphism algebra. Keep operation symbols and identities
    mathematical; do not introduce executable tests for absence of terms.

11. **Obtain a finite projection witness.** Prove the compactness and finite
    Birkhoff steps needed to obtain a two-element projection algebra as a
    homomorphic image of a subalgebra of a finite power. Cover the possibly
    infinite operation signature of all polymorphisms. Use classical choice
    only to select data fixed by R, never an instance-dependent computation.

12. **Extract finitely many gadgets over R.** Transfer the Boolean clause
    relations through the witness from milestone 11. Use milestone 9 to
    replace the resulting invariant relations by fixed pp-formulas in R's
    actual finite signature. Prove the Boolean-domain representation and
    clause contracts, including quotient representatives and equality.
    Output a finite gadget family independent of the input formula.

13. **Prove mathematical gadget expansion correct.** Replace each clause by
    its fixed gadget, allocating fresh auxiliary variables. Prove that an
    assignment extends to a target homomorphism iff it satisfies the source
    formula. Bound variable and constraint counts. This module must not
    import machines, codecs, runtime bounds, or realization infrastructure.

14. **Certify a generic fixed-gadget compiler.** Attach canonical encodings
    and a `Computation` specification to milestone 13. Certify renaming,
    allocation, and constraint insertion through existing array, traversal,
    and composition rules. Output the dense relational tables specified in
    EXAMPLES.md; fixed arities make their widths polynomial. Prove bounds
    relative to source input length, including unary size headers, and export
    a standalone TM0 realization. Keep tape arguments in foundational rules.

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

The pure mathematics ends at the finite gadget family and its satisfaction
contracts. Its existence proof may be nonconstructive because R is fixed.
The generic compiler supplies the polynomial-time algorithm; the algebraic
proof must not construct machines or inspect encodings. NP membership and
Cook-Levin are independent reusable foundations.

Acceptance requires a Lean codebase depending only on this repository and
Mathlib's dependency closure, with no `sorry`, unproved complexity assumptions,
or added axioms beyond Lean's standard foundations. Ordinary word encodings
must reject malformed inputs, and no hardness claim may rely solely on a
semantic map or output-size bound. Do not claim logspace complexity. Report
Lean lines added and removed for every completed milestone.

[tex]: https://github.com/notzeb/all/blob/master/csp.tex
[main]: https://github.com/notzeb/all/blob/master/csp-notes.tex
[appendix]: https://github.com/notzeb/all/blob/master/csp-append.tex
[clique]: 3-sat-to-clique.md
