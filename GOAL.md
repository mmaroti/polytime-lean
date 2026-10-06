# Polytime: working specification

This document records the framework being designed. Requirements below reflect
the intended goal; proposals and open questions are not yet settled decisions.
The reference projects under `temp/` inform the design but remain outside this
repository's implementation scope.

## Intended mathematical interface

Make mathematical proofs of polynomial-time algorithms straightforward to
translate into Lean. Users should reason about finite structures, mathematical
values, algorithm composition, correctness, and polynomial bounds without
working with tape positions or machine control states.

An algorithm is deterministic, taking values in an input domain and producing
values in an output domain. The main theorem should assert the existence of an
algorithm computing a specified function, or producing an output satisfying a
specified mathematical relation, with a proved polynomial runtime bound.

The framework must distinguish a mathematical function, an executable
algorithm implementing it, and the evidence supporting its runtime claim.
An arbitrary function paired with an asserted cost is insufficient.

## Program schemas and mathematical parameters

The organizing object is a program schema P parameterized by a mathematical
structure S. The parameter space may be any Lean type in any universe. The
schema includes a mathematical structure hypothesis describing which S are
admissible; the framework does not globally require S to be finite, decidable,
enumerable, serializable, or represented by a built-in structure language.
Specific schemas may impose such properties when their algorithms need them.

Fixing P and an admissible S determines the specialized program `P_S`, its
precise input and output domains, and every temporary/state domain. Each
domain remains a family in N, written `D_{P,S}(N)`. Its Lean values may use
ordinary mathematical types associated with S. S itself is fixed mathematical
context, not runtime input and not something the machine must encode.

For every admissible fixed S and every declared domain, there exists a
polynomial size bound valid for all N and all members of that domain. Both
coefficients and degree may depend arbitrarily on P, S, and the particular
domain declaration. They may not depend on the runtime input or on N.
This is a separate requirement from the algorithm's runtime certificate.

Each `P_S` has a finite program/machine description independent of N. The
runtime theorem establishes, for each admissible S, the existence of a
polynomial bound valid across N and inputs satisfying the specialized input
hypothesis. Neither a shared runtime bound across different S nor a runtime
algorithm consuming S is required. Fixed polynomial expressions used for
domain capacities and subcall parameters may likewise depend on P and S;
once specialized, those expressions remain fixed at their declaration sites.

Any finite data determined by fixed S may be precomputed and included as
constant tables, with no polynomial preprocessing requirement in the size of
S. This includes full subgroup and congruence lattices of fixed finite algebras,
principal-generation tables, and fixed finite catalogues of maps or quotients.
Runtime inputs may select entries or objects from these tables. An object
depending on input is not thereby excluded from such a fixed finite catalogue.

S stays fixed throughout execution: runtime input never becomes a new
specialization parameter. Families such as A^N may be specified using S, but
one finite machine must handle every N. In general, the subgroup lattices of
all A^N cannot be supplied by one finite precomputed table. Operations
on these growing objects require bounded representations and certified
programs using the original S.

Structure hypotheses, runtime input hypotheses, and output contracts are
distinct: the first justify specializing the schema, the second justify a
particular run, and the third describe its result. S may enter mathematical
proofs freely. Executable operations still use only certified library
primitives and combinators; fixing S does not introduce an oracle for
arbitrary Lean functions or predicates associated with S.

## Data domains and representations

The primary complexity parameter is an explicit natural number N. Every data
domain, after fixing P and S, is a family `D N`, fixed apart from N; its
description must guarantee
a polynomial bound on the encoded length of every possible member. All inputs,
outputs, and intermediate stored values belong to such bounded domains.
Runtime claims are polynomial in N, not necessarily in the encoded input
length. No reverse bound
from input length to N is required for this notion.

For each domain description, its encoding certificate proves the existence of
one polynomial p such that, for every N and every `x : D N`,
`length (encode x) ≤ p(N)`. This p may depend arbitrarily on the program schema
P and fixed S, but cannot be selected separately for each N or each value.
Polynomial witnesses are internal: formalization users should not
calculate or carry explicit coefficients, degrees, total operation counts, or
composed size bounds. Constructors and closure lemmas should discharge these
qualitative polynomial claims. The domain may have exponentially many
elements; the length of each representation is polynomially bounded.

The intended domain language includes explicitly presented finite carriers and
finite algebras with operation tables; records/direct products;
alternatives/disjoint unions; lists; and finite indexed families, including
heterogeneous families and matrices. Lengths and dimensions may depend on
numeric parameters such as N, K, and L. The specification must distinguish this
data-domain signature from an algebraic signature of operation names and
arities.

In the initial examples, finite carriers and algebra operation tables are
fixed constants selected by the specialized mathematical parameter S.
In particular, Gauss–Jordan elimination fixes its
finite field and arithmetic tables before N varies. Algorithms and polynomial
witnesses may depend on this fixed data. The same applies to relational
templates and their relation tables. The framework must not require uniform
algorithms accepting varying templates or tables as runtime input.

Examples of required domains include:

- `A^N`, interpreted as exactly N entries of a fixed finite carrier A.
- Lists of length at most a specified polynomial in N.
- Nested lists over the disjoint union of fixed finite carriers A and B, with
  at most `N^3 + N^2` outer entries and at most `N^4` entries in each inner list.
  Polynomial encoded size should follow from generic nested-list rules without
  asking users to compute the resulting polynomial. Framing, tags, and empty
  lists must be included in the library's encoding proof.
- Dependent records containing K and L with `K ≤ N`, `L ≤ N`, followed by a
  K-by-L matrix over a fixed finite carrier.

Representations should provide encoding, decoding, a round-trip theorem, and
encoded-size bounds. Finite indexing needs an explicit enumeration, not just
a proof of finiteness. A mathematical family `i ↦ value i` should be represented
as stored finite data; it must not implicitly grant free evaluation of an
arbitrary Lean function. Proof fields establish validity without becoming
runtime data.

Proposed interface: each algorithm has one structured input and one structured
output. Records package multiple arguments and results. Dimensions determined
by earlier input fields require dependent records, not only fixed products.

All runtime data share this abstraction: an element of a bounded domain.
Different domain descriptions still distinguish matrices, lists, scalars, and
records; this does not require erasing their mathematical types into an
untyped universal value.

Bounded domains have an open interface. The library supplies standard
constructors, and users may introduce custom domains with certified
representations and qualitative polynomial size bounds. Operations and
representation conversions on custom domains must be implemented using the
library's existing primitives and combinators, with mathematical contracts.
Custom domains do not provide a mechanism for registering arbitrary executable
functions as new primitives. A size bound and round-trip theorem alone do not
establish the computational cost of an operation or representation conversion.

## Fixed CSP templates and instance domains

CSP is a decision problem for a fixed finite relational structure R over a
fixed finite carrier A. R includes finitely many named relation symbols, their
fixed arities, and their complete relation tables on A. These are known before
the algorithm is constructed and do not appear in runtime input. The number
of symbols, maximum arity, relation tables, and any fixed polymorphism may
influence both the algorithm and its polynomial bound.

The required theorem order is: for each fixed R satisfying the stated
mathematical properties, there exists an algorithm and a polynomial runtime
bound that work for every N and every instance of CSP(R) on N variables.
There is no requirement to place the algorithm or polynomial witness before
the quantification over R. Uniformity is required across N and instances for
one fixed R, not across different R.

N is exactly the number of variables, indexed by `Fin N`. For each relation
symbol r of arity k, input stores a Boolean table on ordered k-tuples of
variables: mathematically, `(Fin k → Fin N) → Bool`, represented as a vector
of exactly `N^k` bits with a certified fixed ordering. A true bit means the
corresponding relation application is a constraint. The complete instance
domain is the finite dependent product of these Boolean-table domains over
the fixed relation symbols.

This domain is constructible from standard domain operations: finite
products/families, finite tuples of indices, and Boolean vectors of polynomial
length. Its encoded-size bound follows automatically from the fixed signature.
There is no separate runtime constraint list or independent constraint-count
budget. Each possible application occurs once; repeated variables within a
tuple are allowed. For a signature containing a single binary relation, the
input is an N-by-N Boolean incidence matrix, stored in `N^2` bits.

The mathematical satisfaction condition for an assignment `a : Fin N → A`
is: every enabled tuple for symbol r maps coordinatewise under a into the
fixed relation R(r). The output domain is Boolean, with contract
`answer = true ↔ there exists a satisfying assignment`. Every well-formed
instance is covered, including unsatisfiable instances; satisfiability is not
an input hypothesis.

Alternative representations may be connected through certified polynomial-time
conversions in N. Exact framing conventions are not part of the user's
complexity proof; the template and the chosen representation are fixed.

## Shapes, contracts, and errors

A matrix domain over a fixed finite field contains dimensions K and L bounded
by N and exactly K-by-L entries. Rectangularity and dimension bounds are
structural validity conditions. Gauss–Jordan elimination should return a
matrix with the same dimensions; a variant removing zero rows may preserve
the column count and decrease the row count.

The program's ordinary bounded domain types establish structural validity
and polynomial storage bounds, while its correctness theorem establishes
relations between input and output, such as equal dimensions, row equivalence,
or a normal-form property. Such proof certificates are Lean proofs, not extra
serialized runtime output. Optional proof refinements may expose proved shape
relationships to subsequent program steps without repeating their proofs.

Every certified algorithm has a mathematical input hypothesis `H(N, x)` and an
output contract `Q(N, x, y)`. Contracts may relate outputs to inputs; they are
not restricted to predicates on the output alone. Under H, execution produces
an output satisfying Q and has the certified polynomial runtime guarantee.
There is no termination or correctness obligation outside H. Semantics must
therefore accommodate partial deterministic computation; an ordinary total
Lean function on all input values is not required. A certified result is
available on inputs satisfying H, without passing H as runtime data.

Composition requires a Lean proof that the preceding contract establishes the
next algorithm's input hypothesis. This is a proof obligation during
formalization. Mathematical preconditions need not be decidable or checked at
runtime. The framework must not insert implicit validation, exceptions, error
outputs, or runtime serialization of these proofs. A result alternative such
as success/no-solution is present only when explicitly part of the algorithm's
chosen output domain and contract.

Keep malformed serialized input distinct from a value failing a mathematical
precondition. No guarantee is required for malformed encodings, and they do
not introduce an error alternative into the structured output domain.

## Programs and composition

The intended uniformity in N is one finite algorithm description and one
runtime polynomial Q satisfying the bound for every N and every valid input
in `Input N` satisfying its theorem hypothesis. An independently chosen
machine or polynomial for each N would not meet this requirement. Q is
existential and hidden from users, like the
domain's encoded-size bound. N is an explicit runtime parameter, encoded
alongside the structured input and available to the program even when that
input is empty. Encoding and reading N are included in the realization's
costs.

Subprograms may be invoked with another size parameter `M = p(N)`, where p is
a fixed natural-coefficient polynomial expression specified at the call site.
The expression does not depend on input values or evolving loop state. N here
is the enclosing program invocation's parameter. The framework must provide a
certified call/reparameterization
rule: establish that the actual arguments belong to the callee's domain at M
and satisfy its input hypothesis, invoke the callee at M, and expose its
contract to the caller. Polynomial bounds in M compose with the polynomial
bound on M in N, with composed runtime and storage witnesses hidden from
users. Specifying p for a domain or subcall does not require users to calculate
the runtime polynomial of the resulting program.

Reparameterization must also account for computing M, transporting input and
output representations, and storing the returned values. Dependent records
can package M with data whose domain depends on M; their size certificate
must bound the entire package in the enclosing N. Reindexing at p is a
bounded-domain constructor with value family `D (p(N))`.

Within a loop, a call site's p is always evaluated at the enclosing program's
unchanged N. It must not instead be applied to the parameter used by the
previous iteration. Nested calls compose their fixed polynomial expressions;
the initial core does not introduce recursive self-calls.

Changing the parameter does not implicitly change a value's contents. For
example, extending an exact N-tuple to an M-tuple is a user program that
supplies the additional entries and proves its contract. A library may supply
ordinary certified construction/lookup/update operations used by that program,
but must not silently choose padding values.

Algorithms are written using certified combinators with notation resembling
mathematical pseudocode: `let`, `if`, `lookup`, `update`, and `while`.
The language has mathematical semantics and operational cost semantics.
Its ingredients include
certified primitive operations, composition, projections, record and
alternative construction, branching, and bounded while loops.

All user-defined algorithms are built from these existing certified primitives
and combinators. The user extension interface does not accept independent
machine implementations as new primitive algorithms. Library primitives
themselves require proved machine realization; no unverified oracle or bare
function with an asserted cost may enter the certified core.

DAG composition should retain shared intermediate results. A fixed finite DAG
alone does not express input-dependent repetition; bounded while loops supply
this capability. Traversal, mapping, folding, and bounded repetition can be
derived from while loops, counters, and list/tuple lookup rather than separate
core iteration constructs. A generated DAG is runtime data, whose construction
and evaluation must both be accounted for. Shared term certificates should remain compact
without requiring expansion into potentially much larger term trees.

Composition certificates must control intermediate representation sizes as
well as invocation counts. Reading, copying, allocation, table lookup, and
arithmetic need justified costs under the eventual realization model.

Users should prove correctness by mathematical equalities, relations, and loop
invariants. Runtime proofs should combine reusable bounds for primitives,
composition, collection operations, and bounded iteration. Saturation/worklist
algorithms additionally need an explicit progress or iteration-bound argument.
Prepared tables or coordinate systems count as inputs unless their preparation
has also been certified.

The intended proof interface combines qualitative facts: polynomially many
iterations, polynomial work per iteration, and polynomially bounded stored
state imply polynomial total runtime. It should not expose the multiplied
polynomial. A bounded state domain alone does not imply polynomially many
iterations: its number of distinct values may be exponential in N. Iteration
rules therefore still need termination and polynomial progress evidence.

Each loop should have a state in a bounded domain, an executable Boolean
guard, a certified body, and a mathematical invariant. The invariant and guard
must establish the body's hypothesis; its contract must preserve the invariant.
Guard evaluation costs are included. A stopping argument must yield a
qualitative polynomial iteration bound under the loop's input hypothesis.
Execution stops when the guard is false; there is no semantic iteration cap
or implicit timeout result. The polynomial bound is proof evidence rather
than a second stopping condition. Under the input hypothesis, the proof must
establish that the guard becomes false. The final invariant and false guard
establish the exit contract. Progress measures may be mathematical proof data
and need not be computed or stored by the program.

## Machine realization

The completed framework must prove that every certified program has a
realization on a standard deterministic machine. The finite machine
description may depend on P and S and is fixed independently of N.
On the encoding of N and a valid
input satisfying the theorem hypothesis, it halts with an encoded output
satisfying the contract, within a polynomial number of actual machine steps
in N. Abstract source-level cost certificates alone do not complete this goal.

The implementation may use intermediate execution models, but must prove
their correspondence and polynomial overhead through to the machine model.
Representation handling, subprogram handoff, guard evaluation, and loop
execution belong to this proof. Tape/control-state reasoning should remain
inside the reusable library. No termination or result guarantee is required
on malformed encodings or inputs failing the mathematical hypothesis.

## Initial examples and acceptance goals

The initial numerical core provides fixed finite-table arithmetic and natural
counters whose numeric values are polynomially bounded in N. Signed integers
with polynomially bounded bit length and their arithmetic helpers are later
work. Library primitives must suffice for finite-table application, Boolean
tests, counter operations, and stored-data construction, lookup, and update.

Three examples are required, in this order:

1. **Gauss–Jordan elimination.** Fix a finite field and its arithmetic tables;
   Z_p for any fixed prime p is a required instance. Inputs are K-by-L matrices
   with K and L at most N. The output is a matrix of the same dimensions.
   Proposed contract: reduced row-echelon form and row equivalence. Treat
   empty rectangular matrices, zero matrices, missing pivots, and rank-deficient
   matrices. Pivot inversions are justified by proved nonzero hypotheses.
   Zero-row removal, if supplied, is a separate certified program.
2. **Semilattice CSP.** Fix a finite relational structure with finite signature,
   relation tables, and a semilattice operation table preserving every relation.
   Semilattice identities and preservation are mathematical hypotheses on this
   fixed structure, not tests repeated at runtime. Inputs are bounded finite
   CSP instances in the dense domain above, on exactly N variables. The result
   is a Boolean decision. Proposed implementation: generalized arc consistency by
   repeated removal of unsupported values, with finite subsets of the fixed
   carrier represented as fixed-size data. Successful pruning strictly reduces
   the remaining variable/value pairs, supplying a polynomial progress bound.
   Prove preservation of all solutions and completeness under the semilattice
   hypothesis. A satisfying assignment may be constructed in the mathematical
   completeness proof; it is not a required runtime output.
3. **Affine CSP over Z_p.** Fix a prime p, the ternary relation `x + y = z`,
   and unary singleton relations `x = c` for each constant c in Z_p. Compile
   constraints into an augmented linear system, invoke certified elimination,
   and derive the Boolean CSP decision. Repeated variables must accumulate their
   coefficients. Prove the correspondence between CSP assignments and linear
   system solutions and account for matrix construction and result extraction.
   Its dense input consists of `N^3` ternary-application bits and one N-bit
   unary-application vector for each c in Z_p. The compiled system may have
   polynomially more than N rows; it has N variable columns and an augmented
   column. Derive a fixed polynomial call-site parameter accommodating both
   row count and augmented width from this signature, and invoke elimination
   there. Do not assume that a call at `N + 1` accommodates every dense instance.

All three examples must use the common combinators and receive the proved
machine-runtime guarantee. A false CSP result means mathematical
unsatisfiability and is not an error. Empty instances, repeated variables in a
scope, and isolated variables must be covered. Dense tables do not store
duplicate applications. Handle zero variables and zero-arity relation symbols
consistently with tuple cardinalities; a nullary constraint has one activation
bit and may determine unsatisfiability without mentioning any variable.

Product scans, compact term-DAG construction/evaluation, and structured
encoding conversions from the reference projects remain further motivating
applications rather than replacements for these three required examples.

Success means these examples use the common infrastructure rather than
requiring bespoke tape-level developments. Mathematical specifications may
use ordinary Mathlib objects, with proved correspondence to stored values.
Conditional algorithm theorems must expose any uncertified solver or
preparation assumptions.

## Decisions still being discussed

1. How should partial semantics and proof refinements be exposed in Lean?
2. What domain constructors and certified extensions should the first version
   support, and which qualitative polynomial closure facts should automation
   handle without user intervention?
3. How should loop invariants, qualitative progress certificates, and exit
   contracts be packaged? Are the proposed example contracts and edge cases
   appropriate?

## Reference-review requirements

The static expressiveness review is recorded in
[REFERENCE_REVIEW.md](REFERENCE_REVIEW.md). It found no basic control-flow
obstruction for the representative deterministic polynomial algorithms, but
identified representation and certification boundaries that the interfaces
must preserve:

- Fixed finite subgroups, congruences, quotients, or maps may have constant
  labels and precomputed operation tables. Growing mathematical objects may
  use bounded generators, rows, or other representations. Data-bearing
  witnesses such as DAG roots and coordinate tables must be available as
  constants or computed runtime data; only proof fields are erased.
- Generic algorithm schemas may accept certified subprograms as mathematical
  parameters, instantiated with core implementations. Bare callbacks with
  correctness alone are not certified executable algorithms.
- Fixed catalogue choices belong to S. Input-dependent selection from a fixed
  finite catalogue is allowed. Structures growing with N require bounded
  representations and certified operations within the original program;
  runtime input never becomes a new S.
- Exhaustive exponential closures, expanded term trees, and infinitary tables
  may be mathematical specification objects without being runtime domain
  values. Polynomial-size witness existence alone does not establish a
  uniform polynomial-time constructor as N varies.
- Signed integer solvers, randomized execution, and logspace guarantees are
  not part of the initial finite-table deterministic polynomial-time core.

## Reference motivations

For the semilattice example, the proposed arc-consistency route is described
in Bodirsky, Macpherson, and Thapper, *Constraint Satisfaction Tractability
from Semi-lattice Operations on Infinite Sets*, §2 (finite-domain preliminary
results): <https://arxiv.org/pdf/1111.6616>. This is design provenance, not an
assumed axiom or a claim that this repository has already verified the result.
