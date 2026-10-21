# Framework specification

This document records framework requirements. Current coverage, execution
designs, and next steps belong in [Polytime2/README.md](Polytime2/README.md);
target algorithms belong in [EXAMPLES.md](EXAMPLES.md). Proposals and open
questions are not yet settled decisions. The reference projects under `temp/`
inform the design but remain outside this repository's implementation scope.

Size parameters have equal roles. The data layer has no distinguished N
and no admissibility bounds between parameters. Algorithms will be polynomial
in all declared size parameters, measured by one plus their sum. Generic
algorithm discussions below using N mean this aggregate, not a parameter
available for reparameterization. In examples such
as CSP with N variables, N is an ordinary declared parameter.

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
domain remains a family indexed by its declared size parameters,
written `D_{P,S}(a)` for a complete size assignment a. Its Lean values may use
ordinary mathematical types associated with S. S itself is fixed mathematical
context, not runtime input and not something the machine must encode.

The `SizeContext` itself may depend on both P and S. For example, specializing
an SMP algorithm to a finite algebra A determines a fixed finite catalogue
HS(A); the context may name one coordinate-count parameter per catalogue sort.
Those counts vary with the input instance, while the catalogue and parameter
names remain fixed throughout execution. Domain expressions likewise depend
on P and S.

For every admissible fixed S and every declared domain, there exists a
multivariate polynomial size bound valid for all size assignments and members
of that domain. Both
coefficients and degree may depend arbitrarily on P, S, and the particular
domain declaration. They may not depend on the runtime input or on the values
of the size parameters.
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

`SizeContext` names all parameters through a finite type. Each parameter has
the same role, and a `SizeAssignment` maps each name to an arbitrary natural
number. A context may name N, K, and L without imposing any bounds between
their values. Every data domain, after fixing P and S, is a family `D a` over
these assignments. Its description guarantees one multivariate polynomial
encoding bound in all the parameters, uniformly over every assignment and
every domain value. All inputs, outputs, and intermediate stored values
belong to such bounded domains. Runtime certificates will separately establish
polynomial bounds in all size parameters; the data layer does not select an
aggregate.

For each domain description, its encoding certificate proves the existence of
one multivariate polynomial p such that, for every a and every `x : D a`,
`length (encode x) ≤ p.eval a`. This p may depend arbitrarily on the program
schema P and fixed S, but cannot be selected separately for each assignment
or each value.
Runtime and composed resource witnesses are internal: formalization users
should not calculate their coefficients, degrees, or total operation counts.
Implementations or library helpers supply explicit evaluable storage capacities
and prove them sufficient. The complete assignment determines the exact encoding
width. Size parameters need not
be fields of domain values or included in their encodings. Their eventual
machine interface is separate from this data-domain layer.
Constructors and closure lemmas should discharge these
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

The initial domain language must support `Fixed`,
`Product`, `Sum`, and `Power`. A Fixed domain supplies an explicit equivalence
with `Fin k`; its binary labels use `Nat.clog 2 k` bits. Product concatenates
fields from a fixed finite list. Sum uses a binary alternative tag, its
payload, and canonical zero padding to the maximum payload width. Power
contains an exact number of entries, specified by any natural-coefficient
multivariate polynomial in the size parameters, including constants.

These constructors must give fixed-width codecs with round-trip and canonical
decoding theorems, and automatically compose polynomial-size certificates. The
initial expression language remains limited to these four constructors. Bounded
lists, buffers, and heterogeneous coordinates use derived presentations with
active counts, tags, and contracts; dependent records remain deferred. Domain
certificates alone establish no algorithmic runtime claim. Declared capacities
use executable arithmetic expressions with derived mathematical polynomials and
a proved agreement theorem. The executable evaluator requires an agreement
theorem and a polynomial-time machine realization. Exact widths may also use
operations such as `max` and need not themselves be polynomial expressions, only
polynomially bounded. Constructor encoding equations hide representation casts
and transports behind reusable rewriting lemmas.

Representations should provide encoding, decoding, a round-trip theorem, and
encoded-size bounds. Finite indexing needs an explicit enumeration, not just
a proof of finiteness. A mathematical family `i ↦ value i` should be represented
as stored finite data; it must not implicitly grant free evaluation of an
arbitrary Lean function. Proof fields establish validity without becoming
runtime data.

`EncodedDomain` connects a mathematical carrier family to a domain expression
through `represent` and partial `interpret`. Interpreting a represented object
returns that object; every accepted representation is its object's unique
representation. Expression values outside this image may be rejected, in
addition to invalid bit patterns rejected by the expression's codec. Bit
encoding and decoding are derived by composing these layers. When several
generator lists have the same span, or several DAGs have the same meaning,
the carrier may be the list or DAG itself, with span, expansion, and evaluation
expressed separately in contracts. Unique representation does not require
canonicalizing these mathematical meanings. These presentation functions specify
meaning, not executable operations or implicit runtime validators; conversions
require certified programs.

Proposed interface: each algorithm has one structured input and one structured
output. Records package multiple arguments and results. Input-dependent
dimensions use fixed capacities and active counts related by contracts.

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

## Shapes, contracts, and errors

A matrix domain over a fixed finite field has independent size parameters K
and L and exactly K-by-L entries. Rectangularity is a structural validity
condition. Gauss–Jordan elimination should return a
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

The intended uniformity is one finite algorithm description and one runtime
polynomial Q valid for every size assignment a and every input satisfying its
theorem hypothesis. An independently chosen machine or polynomial for each a
would not meet this requirement. Q is existential and hidden from users.
The complete assignment is encoded alongside the structured input and available
to the program even when that input is empty. Reading it counts toward runtime.

At each call site, each callee size parameter is assigned a fixed
natural-coefficient polynomial in the caller's size parameters. Together these
expressions define a substitution p and callee assignment `p(a)`, independent
of input values and evolving loop state. The certified call rule requires
arguments in the callee's domain at `p(a)` satisfying its input hypothesis,
and exposes its output contract. Polynomial runtime and storage bounds compose
under substitution, with resulting witnesses hidden from users.

Reparameterization accounts for computing `p(a)`, transporting representations,
and storing returned values. Reindexing is an operation on existing domain
expressions, giving the value family `D (p(a))`, not a new constructor.

Within a loop, a call site's p is always evaluated at the enclosing program's
unchanged assignment a. It must not instead be applied to the assignment used by
the previous iteration. Nested calls compose their fixed polynomial expressions;
the initial core does not introduce recursive self-calls.

Changing the parameter does not implicitly change a value's contents. For
example, extending an exact N-tuple to an M-tuple is a user program that
supplies the additional entries and proves its contract. A library may supply
ordinary certified construction/lookup/update operations used by that program,
but must not silently choose padding values.

Algorithms are written using certified combinators with notation resembling
mathematical pseudocode: `let`, `if`, `lookup`, `update`, and `while`.
The initial language is first-order, with mathematical semantics and one
operational cost model. Its ingredients include certified primitive operations,
composition, projections, record and alternative construction, branching,
bounded while loops, and static calls using finite working storage.

All user-defined algorithms are built from these existing certified primitives
and combinators. The user extension interface does not accept independent
machine implementations as new primitive algorithms. Library primitives
themselves require proved machine realization; no unverified oracle or bare
function with an asserted cost may enter the certified core.

Named intermediate values provide sharing without a separate program-DAG syntax.
Traversal, mapping, folding, and bounded repetition can be derived from while
loops, counters, and list/tuple lookup rather than separate core iteration
constructs. A generated DAG is runtime data, whose construction and evaluation
must both be accounted for. Shared term certificates should remain compact
without requiring expansion into potentially much larger term trees.

Composition certificates must control intermediate representation sizes as
well as invocation counts. Reading, copying, allocation, table lookup, and
arithmetic need justified costs under the eventual realization model.

Users should prove correctness by mathematical equalities, relations, and loop
invariants. Runtime proofs should combine reusable bounds for primitives,
composition, collection operations, and bounded iteration. Saturation/worklist
algorithms additionally need an explicit progress or iteration-bound argument.
Finite data determined solely by S may be precomputed. Input-dependent tables
or coordinate systems not covered by these constants must be supplied as
bounded input or constructed by certified programs.

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
On the encoded size assignment and a valid input satisfying the theorem
hypothesis, it halts with an encoded output
satisfying the contract, within a polynomial number of actual machine steps
in N. Abstract source-level cost certificates alone do not complete this goal.

The implementation may use intermediate execution models, but must prove
their correspondence and polynomial overhead through to the machine model.
Representation handling, subprogram handoff, guard evaluation, and loop
execution belong to this proof. Tape/control-state reasoning should remain
inside the reusable library. No termination or result guarantee is required
on malformed encodings or inputs failing the mathematical hypothesis.

### Working storage and external interfaces

The working layout is an implementation choice: a prepared frame, separate
tapes, or another bounded representation. Fixing P, S, and the size assignment
determines storage capacities. Controllers, tape counts, and finite alphabets
may depend on P and S, but must be independent of runtime sizes. Growing
indices and tuples must be stored as data, not in size-dependent controller
states. A universal alphabet is optional; specialization-dependent finite
alphabets require a proved standard-machine realization.

Subroutine contracts specify valid representations, workspace, entry and exit
head positions, and preservation of caller-owned storage. Composition proves
entry/exit compatibility, including shared storage and scratch reuse. Bounded
mathematical values are required at program-operation boundaries; physical
scratch and partially written storage need not encode complete values.
Vacant storage uses explicit initialization invariants or tags, without
assuming default elements or adding implicit errors.

Canonical value encodings remain separate from working layouts. Navigation,
copying, allocation, marker maintenance, and representation conversions require
certified implementations. Copying must preserve values needed afterward;
overlapping copies require specified semantics and a proved strategy.
Polynomial overhead in bounded storage is sufficient; constant-time access is
not assumed. Program authors should not manipulate physical markers.

The external input supplies the complete size assignment alongside canonical
input bits, even when the mathematical input is empty. A self-delimiting
header uses a fixed known parameter ordering. Unary size headers are permitted
because complexity is measured in parameter values, not their binary lengths.
Other external formats require certified parsing and serialization adapters,
not alternative constructor codecs.

The complete realization includes three certified stages: preparation
establishes the internal entry contract; execution computes the result;
extraction returns its canonical encoding. Preparation must account for
bootstrap workspace, reading the header, computing required capacities,
initializing storage and metadata, and transporting the input. Prepared
workspace may be assumed by internal subroutines, but the external theorem
must construct it with polynomial time and storage.

## Target examples and acceptance goals

[EXAMPLES.md](EXAMPLES.md) specifies the prioritized application targets and
shared building-block libraries, including their contracts and edge cases.
Each implementation must eventually complete those targets through its own
certified primitives and combinators, bounded representations, and complete
external machine-runtime theorem. Implementation status belongs in its README.

Mathematical existence of decompositions, coordinates, or normal forms is
insufficient without the required executable construction. Shared term-DAG
witnesses must stay compact; correctness-only callbacks are not certified
solvers. Building-block libraries are derived certified programs and proofs,
except for the basic operations and execution machinery needed by the core.

Integers have polynomially bounded bit capacities, not necessarily
polynomially bounded numeric values. Arithmetic must have certified bit costs
and sufficient output capacities; algorithms must bound intermediate bit
lengths. Unary storage for polynomially bounded counters does not justify
unary storage for general binary integers.

Fixed-template CSP remains a motivating application; its instance domains
and contracts are specified in [EXAMPLES.md](EXAMPLES.md).
Logspace guarantees and randomized execution are outside the initial scope.

## Development priorities

Develop the reusable interface from concrete example proofs. Prefer predicates
and reusable lemmas to new structures, and avoid speculative definitions.

- Express mathematical preconditions and postconditions through representation
  relations, allowing irrelevant scratch to remain existential.
- Hide controller packaging, physical layouts, and runtime polynomial witnesses
  behind certified composition and access rules.
- Provide derived search, traversal, and fold rules. Users supply mathematical
  invariants and progress arguments; the library accounts for guards,
  handovers, and polynomial closure.
- Specify preservation and workspace conventions that allow subroutine reuse
  inside larger computations, including shared storage.
- Retain complete external realization as the acceptance check; a general
  compiler or wholesale rewrite is not a prerequisite for improving reuse.

## Decisions still being discussed

1. How should partial semantics and proof refinements be exposed in Lean?
2. Which qualitative polynomial closure facts should automation handle without
   user intervention?
3. How should loop invariants, qualitative progress certificates, and exit
   contracts be packaged? Are the proposed example contracts and edge cases
   appropriate?

## Reference-review requirements

The reference review found no basic control-flow obstruction for the
representative deterministic polynomial algorithms. The interfaces must
preserve these representation and certification boundaries:

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
- Signed integer solvers require extending the finite-table core with bounded
  binary integer representations and bit-cost arithmetic; this is required
  by the Smith-normal-form target. Randomized execution and logspace guarantees
  remain outside the initial scope.
