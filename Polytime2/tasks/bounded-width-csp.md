# Bounded-width CSPs and explicit algebraic constraints

Status: proposed. [Task index](../README.md#proposed-next-tasks).

## Outcome and exact hypotheses

Formalize and certify polynomial-time decision and assignment search for
bounded-width relational CSPs. Prove the algebraic sufficient condition:
if a fixed finite nonempty idempotent algebra A generates a congruence
meet-semidistributive variety, then CSPs over its compatible relations are
solvable by local consistency. Include variable-arity relations supplied as
explicit tuple lists, and a certified reduction from fixed relational templates.

For a variety V, congruence meet-semidistributivity means that every B in V
satisfies the following implication in its congruence lattice:

`alpha ∧ beta = alpha ∧ gamma` implies
`alpha ∧ (beta ∨ gamma) = alpha ∧ beta`.

Requiring this only of Con(A) is insufficient. Use V = HSP(A), not an arbitrary
ambient variety with no membership hypothesis. Idempotence and finiteness must
be explicit. A single Taylor term or a single weak near-unanimity term is not
the bounded-width hypothesis. Do not conflate bounded width with strict width:
a surviving partial assignment need not extend to a full solution.

This is a substantial algebraic solver project. The majority case is a useful
first milestone, not evidence that the full theorem is a short task.

## Mathematical problems and input sizes

1. **Fixed relational template.** Reuse `CSP.Instance`, `CSP.Satisfiable`,
   `CSP.language`, and the existing native instance-word format. The template R
   has a finite nonempty domain and finitely many relations of fixed arities.
   Instances have arbitrary relations of the same signature. No reflexivity
   assumption is imposed. Supply a fixed finite idempotent algebra A on the
   template domain whose operations preserve every template relation and for
   which HSP(A) is congruence meet-semidistributive. Export a solver for CSP(R).

2. **Explicit algebraic constraints.** Fix A before choosing the algorithm and
   polynomial. An instance has a finite variable set V and finitely many
   constraints, each with a finite coordinate set I, a scope map I -> V, and an
   explicitly listed relation R contained in A^I, closed under A's operations.
   Satisfaction means that the assignment restricted along each scope belongs
   to its relation. Allow repeated scope variables, duplicate constraints,
   empty relations, and nullary constraints. An empty relation rejects; a
   nullary relation containing the empty tuple imposes no restriction.

The second problem permits unbounded constraint arities. Bound runtime by the
complete encoding length: variable declarations, constraint headers, scope
entries, tuple counts, and every tuple coordinate. Relations are given by their
full tuples, not generators, circuits, or membership oracles. Never enumerate
all of A^I merely to encode a sparse input relation.

Use ordinary functions, finite sets, and Mathlib algebraic substructures as
mathematical carriers. Keep tables, tuple numbering, padding, and workspace in
codecs. State whether closure is an admissibility condition or is checked.
For a total word language, reject malformed encodings and specify treatment of
nonclosed tables. A fixed finite operation signature permits polynomial closure
checking; do not assume an oracle for checking an infinite operation signature.

## Relational-to-algebraic bridge

Every template relation preserved by A's basic operations is a subuniverse of
the appropriate power of A. Translate each enabled instance fact to a scope
with that fixed template relation as its explicit allowed table. Prove that
the assignment set is unchanged and certify the translation's polynomial cost.
Handle repeated scope variables and nullary facts explicitly. Reuse the existing
dense relational codec; enumerating its enabled facts is charged to its length.

The full polymorphism algebra is useful mathematically but can have an infinite
signature. Reuse `polymorphismLanguage`, `polymorphismAlgebra`, and preservation
lemmas for the semantic bridge. When starting from an algebraic bounded-width
condition on that clone, justify a finite choice of compatible operations
witnessing the condition, fixed independently of the input. Do not silently
identify a finite constraint language with the input-table problem over all
invariant relations, or assert a reverse polynomial reduction without proof.

## Sources and prerequisite review

- Zarathustra Brady, *Notes on CSPs and Polymorphisms*,
  [arXiv:2210.07383][brady], with the author's [TeX source][tex]. Use
  the section
  "Varieties, Birkhoff's HSP theorem, and the hardness proof" for the algebraic
  viewpoint. In the chapter "Absorption and Bounded Width", use
  "Cycle-consistency
  solves majority CSPs", "Bounded width: affine-free CSPs are solved by
  cycle-consistency", "Weak Prague instances", and "Terms for bounded width
  and the meta-problem". Relevant TeX labels include `affine-free-pq`,
  `weak-prague-pq`, and `bounded-width-terms`. Distinguish proved text from
  commented-out proposed strengthenings in the source.
- Libor Barto and Marcin Kozik, *Constraint Satisfaction Problems Solvable by
  Local Consistency Methods*, J. ACM 61(1), Article 3, 2014,
  [DOI:10.1145/2556646][bk]. The preliminary paper, *Constraint Satisfaction
  Problems of Bounded Width*, has an [author PDF][preliminary]; Theorem 3.7
  states the sufficient width bound and Theorem 4.5 treats Prague strategies.
- Libor Barto, *The collapse of the bounded width hierarchy*, Journal of Logic
  and Computation 26(3), 923–943, 2016, [DOI][collapse]. Use this separately if
  claiming relational width (2,3) for general bounded-width templates. Record
  the precise consistency convention and higher-arity constraint treatment.

Read the [CSP guide](../CSP/README.md),
[composition guide](../Computation/README.md),
[array guide](../Arrays/README.md), and [encoding guide](../Encoding/README.md).
Reuse the existing relational and polymorphism interfaces and Taylor algebra
foundations. Adapt necessary mathematical arguments to Mathlib and this
repository. All required proofs must compile locally with only this project's
modules and Mathlib's dependency closure; citations are not proof dependencies.
No imported algorithm representation, cost model, or unproved solver axiom is
acceptable. Keep any literature downloads outside the repository.

## Milestones

1. State both satisfaction problems and their exact mathematical inputs,
   outputs, and admissibility. Specify scope restriction and assignment
   transport before implementing codecs or algorithms.
2. Define the variety-level congruence condition and a usable finite term
   witness. Prove the implications actually used by the solver, including
   preservation under powers and subalgebras. Keep this pure mathematics.
3. Prove the relational-to-algebraic assignment equivalence. Choose a finite
   compatible reduct when needed, and separate this existence proof from its
   fixed finite-table realization.
4. Specify a concrete local-consistency system: maintained relations, deletion
   rules, initial state, and failure condition. Choose a verified source proof
   and match its conventions; arbitrary pairwise projection is insufficient
   for higher-arity constraints.
5. Prove every propagation step preserves all solutions and relevant algebraic
   closure. Show that failure certifies unsatisfiability, including empty and
   nullary constraints.
6. First prove completeness for majority-compatible constraints. Formalize
   Boolean majority preservation of every relation on at most two coordinates
   used for 2-SAT, and derive decision and satisfying-assignment corollaries.
7. Formalize the absorption, subdirect-product, and consistency lemmas needed
   for the full congruence meet-semidistributive case. Prove that a nonfailed
   terminal consistency system has a solution; do not assume this criterion.
8. For arbitrary-arity explicit inputs, prove a polynomial binary incidence
   encoding: retain original variables and introduce a tuple-choice variable
   for each constraint, with projection compatibility relations. Its domain
   is the listed relation, a subalgebra of a power of A. Prove solution
   transport and local completeness for the resulting heterogeneous domains
   in HSP(A). Never construct an exponentially large ambient product table.
9. Prove a polynomial deletion bound and certify propagation using existing
   array scans and composition. Count all maintained tuple slots and all
   support checks. The bound must be uniform in input arities and tuple-list
   sizes; a theorem with a different polynomial for each finite language does
   not establish this deliverable.
10. Certify assignment extraction. One acceptable method is decision-based
    self-reduction by singleton restrictions, proving that idempotence makes
    these restrictions admissible. Test a candidate before committing it;
    bounded width alone does not justify arbitrary greedy choices.
11. Certify both encodings, syntactic validation, any required closure check,
    incidence construction, propagation, and assignment transport. Derive
    workspace and counter capacities internally from mathematical input sizes.
12. Compose the relational solver and export realizability, standalone Mathlib
    TM0 certificates, and total polynomial word bounds. Audit mathematical
    hypotheses, dependencies, axioms, and edge cases; update authoritative
    guides and remove completed task entries.

## Acceptance and relation to 2-SAT

- Return an actual satisfying assignment or an unsatisfiable outcome with a
  correctness proof. Certify search as well as decision. No internal padding,
  dead tuple, or search sentinel may appear as a mathematical outcome.
- Prove bounded width under a stated local-consistency definition, not merely
  that some unspecified polynomial-time algorithm exists. Any width-collapse
  claim requires its additional proof.
- Handle zero variables, zero constraints, empty domains created by pruning,
  nullary constraints, repeated coordinates, inconsistent scope repetitions,
  duplicate tuples, disconnected components, and variables in no constraint.
- Include complete polynomial machine bounds in encoded input length. Do not
  infer the variable-arity bound from the fixed-template arity bound. Do not
  claim a solver uniform over arbitrary input algebras.
- Keep algebraic completeness and preservation proofs independent of machines.
  Application certificates use shared composition; no new machine model or
  speculative structures. Report net Lean lines added and removed.

This task subsumes 2-SAT decision and assignment search through the majority
case. It does not automatically supply the implication paths or the specific
empty-clause diagnostic required by [constructive 2-SAT](2-sat.md). Those remain
an optional specialized witness-extraction extension. No linear-time, NL, or
logspace claim is required here.

[brady]: https://arxiv.org/abs/2210.07383
[tex]: https://github.com/notzeb/all/blob/master/csp.tex
[bk]: https://doi.org/10.1145/2556646
[preliminary]: https://www.karlin.mff.cuni.cz/~barto/Articles/SDBW.pdf
[collapse]: https://doi.org/10.1093/logcom/exu070
