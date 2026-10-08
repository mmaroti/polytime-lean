# Target examples for Polytime

The first three examples are the initial implementation targets, in order;
examples 4–6 are additional targets. They specify
mathematical problems and required algorithm contracts, rather than claiming
that the algorithms are already implemented. They must use the common
bounded-domain language, certified program combinators, and machine realization
described in [GOAL.md](GOAL.md).

An algorithm schema P specializes to a mathematical object S satisfying its
stated assumptions. S fixes operation tables, catalogues, and other finite
constants; it is not runtime input. Its size context and domain expressions
may depend on both P and S. All declared size parameters have equal roles.
Runtime and storage must be polynomial in their sum (equivalently, their
maximum, with an added constant), with constants and degree allowed to depend
on P and S. Users should not have to calculate the resulting polynomial.

The external machine receives the complete size assignment and encoded input.
Its certified wrapper prepares the working frame, invokes the algorithm on
that frame, and extracts the output. Copying, navigation, arithmetic,
initialization, and extraction all count toward the runtime guarantee.

The framework must provide the [shared building-block libraries](#shared-building-block-libraries)
specified below. Examples should compose their certified operations rather
than each developing its own arithmetic, buffers, DAG machinery, or tape
navigation. These are development requirements, not claims of current support.

## 1. Gauss–Jordan elimination over a fixed finite field

### Mathematical problem and specialization

Fix a finite field F with a chosen enumeration of its elements and its
addition, multiplication, negation, and nonzero inversion tables. This data,
including the field laws, is the specialization. Every fixed prime field
`ZMod p`, for p prime, must be an instance.

The independent size parameters are the row count K and column count L.
Input is a matrix M in `F^(K × L)`; no additional parameter N or restrictions
between K and L are needed. Its mathematical carrier is an ordinary matrix
type, represented by K tuples of L fixed-field elements.

### Output contract

Return a K-by-L matrix R such that:

- R is in reduced row-echelon form: zero rows follow nonzero rows; each
  nonzero row has a leading entry 1; leading positions move strictly right
  down the nonzero rows; and each leading entry is the only nonzero entry in
  its column.
- R is row equivalent to M, meaning that an invertible K-by-K matrix E over F
  exists with `R = E M`.

The equality witness E may remain mathematical proof data; returning it is
not required by this example. Together these properties characterize the
unique reduced row-echelon form, so this example computes a mathematical map.
Row-space equality alone is not used as a substitute for the stated contract.

### What the implementation must accomplish

Implement pivot search, row exchange, pivot normalization, and elimination
using fixed-field tables, tuple lookup/update, counters, and certified loops.
Prove every inverted pivot nonzero. Bound all row and column accesses and
prove a qualitative polynomial iteration and runtime bound in K and L.

Include zero rows or columns, the zero matrix, missing pivots, rectangular
matrices, and rank deficiency. Preserve dimensions, including zero rows in
the output. Removing zero rows would be a separate algorithm and contract.

This example exercises mathematical carriers, exact tuple shapes, nested
loops, copying rows, and a full prepared-frame realization.

## 2. Single-sorted SMP to a monolith-prepared catalogue instance

### Mathematical problem and specialization

Fix a nonempty finite algebra A in a finite signature of finitary operations.
A subalgebra is a nonempty subset closed under those operations, including
any nullary operations.

The size parameters are the coordinate count n and the number g of listed
generators. Input consists of rows `x^1, ..., x^g` in `A^n` and a target
`y` in `A^n`. Write `B = Sg^(A^n){x^1,...,x^g}` for the least
operation-closed set containing those rows. The membership question is
whether `y ∈ B`. The main preparation contract assumes `g ≥ 1`, so B and
its coordinate projections are nonempty subalgebras. Empty generator lists
need the explicit extension described below.

Define HS(A) to consist of homomorphic images of subalgebras of A, considered
up to isomorphism. It has a finite catalogue of representatives because A is
fixed and finite. Precompute its subalgebra and congruence data, quotient
tables, quotient maps, and chosen isomorphisms. The output uses a fixed
catalogue C of the nontrivial subdirectly irreducible members of HS(A), with
enough precomputed decomposition data for the recursive construction.

A congruence is an equivalence relation preserved by every basic operation.
The equality congruence is denoted 0 and the universal congruence 1. A
nontrivial finite algebra D is **subdirectly irreducible (SI)** when it has a
least congruence strictly above 0. That congruence is its **monolith**, denoted
mu_D. A nontrivial simple algebra has only 0 and 1, so its monolith is 1 and
its monolith quotient has one element.

A relation `R ≤ product_i D_i` is **subdirect** when, for each coordinate i
and each `a ∈ D_i`, some tuple in R has i-th entry a. This describes the
generated subalgebra R, not the full ambient product or just the listed
generator rows.

### Output contract

Return one of two explicitly specified mathematical outcomes:

1. **Outside a coordinate image.** Return a coordinate i certifying
   `y_i ∉ B_i`, where `B_i = Sg^A{x^1_i,...,x^g_i}`. This proves `y ∉ B`;
   it is a valid negative membership result, not an implicit error.
2. **Prepared instance.** Return an ordered list of catalogue factors
   `D_1,...,D_q`, transformed generators X', transformed target y', and the
   finite coordinate maps and graph data described below.

In the prepared outcome, let `R = Sg^(product_i D_i)(X')`. Require:

- Every factor D_i is an SI member of the fixed catalogue, equipped with its
  precomputed monolith mu_i; R is subdirect.
- The factors are ordered by nondecreasing number of congruences, with simple
  factors first. Fix a deterministic tie-breaking convention.
- There is an injective homomorphism
  `e : product_i B_i → product_j D_j` taking each original generator to its
  transformed row and taking y to y'. It restricts to an isomorphism from B
  onto R. Thus `y ∈ B ↔ y' ∈ R`.
- For each final coordinate i, supply a set J_i of earlier coordinates and
  an algebra isomorphism
  `lambda_i : D_i / mu_i ≅ projection_(J_i)(R)` such that

  ```text
  projection_(J_i ∪ {i})(R)
    = { (lambda_i(a / mu_i), a) : a ∈ D_i }.
  ```

  The tuple on the left is ordered as J_i followed by i. In particular,
  agreement on all earlier coordinates forces agreement modulo mu_i.
  This full graph equality is the preparation contract; the prefix
  consequence alone is weaker. For a simple factor, J_i can be empty and
  its projected algebra is the one-element empty product.
- There are constants c_A and b_A fixed by the specialization such that
  `q ≤ c_A n` and `|J_i| ≤ b_A`. For each catalogue sort t, record its
  actual coordinate count n_t, with `sum_t n_t = q`, and the correspondence
  between the ordered coordinates and their sort-local positions.

There is no requirement that the whole ambient product `product_i B_i` be
isomorphic onto the whole final product. Added quotient coordinates generally
create dependencies; the required isomorphism is onto the embedded image,
and in particular from B onto R.

All representation choices and algorithms should be deterministic. Multiple
valid prepared presentations need not be identified as one carrier value:
the carrier contains the actual factor list, maps, and graph data, with
their mathematical meaning expressed by the output contract. Certificates
of the displayed properties are Lean proofs; indices and maps used by later
algorithms are bounded stored data or fixed catalogue lookups.

### Construction to formalize

First compute each B_i using closure in fixed A, scanning the g input entries
at that coordinate. Check the target against these coordinate images before
using maps whose domains are B_i.

For each B_i, use a precomputed subdirect embedding into its SI quotients.
For a finite algebra, the quotients by proper completely meet-irreducible
congruences provide such a decomposition. Their quotient maps jointly
separate elements and are individually surjective. Apply those maps to the
generator rows and target.

Next, for every SI factor D, decompose `D / mu_D` into SI factors and insert
the resulting quotient coordinates before D. Repeat recursively, using
composites of the fixed quotient maps. Nontrivial recursive factors are
strictly smaller, so the number added per original coordinate is bounded
by a specialization-dependent constant. The earlier coordinates encode
exactly the monolith quotient, yielding the graph equality above. Singleton
factors may be omitted because they carry no information.

Compute or select the bounded graph data using fixed catalogue tables and
closures of bounded-coordinate projections. Do not enumerate B, R, or the
full growing product. Generation commutes with coordinate projection, so a
projection onto at most `b_A + 1` coordinates can be computed by projecting
the input generators and taking closure in a fixed-size product algebra.

The algorithm must prove the decomposition, graph, and membership-transport
claims and give polynomial runtime in n and g. If later witness-producing
SMP algorithms return a term DAG over X', homomorphism preservation and
injectivity must prove that the same term on the original generators realizes
y. Preparation does not have to construct a membership witness itself.

### Size contexts and bounded outputs

The catalogue depends on A, so an interface for prepared inputs may name one
coordinate-count parameter per catalogue sort. These actual counts depend
on the input instance; they cannot be silently used as specialization data.

For this conversion's fixed output domain at assignment `(n,g)`, reserve
polynomial capacities for factor slots, rows, and graph records, and store
the active counts n_t as ordinary output data. Tagged inactive slots or
another explicitly chosen padding convention give a fixed-width encoding;
correctness relates the active data to the mathematical prepared instance.
This does not silently permit subcalls at input-dependent size assignments:
under the fixed-polynomial call-site rule, consumers use fixed polynomial
capacities and accept the active counts as data. An exact-count dependent
interface would require a separately specified transport mechanism.

Cover n = 0, repeated generators, singleton coordinate images, simple factors,
and catalogues with no nontrivial SI sorts. For g = 0, the generated
operation-closed set consists of values of closed terms. Over fixed A these
values form a fixed finite set; in A^n the evaluations are their diagonal
rows. If there are no closed terms, the set is empty. A small separate
membership routine can handle this case, including n = 0, rather than
assuming nonexistent nonempty coordinate images.

## 3. Smith normal form for integer matrices and SMP span queries

### Mathematical problem and specialization

Compute the **Smith normal form** of an arbitrary rectangular integer matrix
M. This is integer reduction using invertible integer row and column
operations, rather than field Gaussian elimination. No finite field or
modulus is part of the general normal-form algorithm's specialization.

Use independent size parameters r, c, and b: rows, columns, and the bound on
the binary length of entry magnitudes. For example, the mathematical input
domain can require `|M_ij| < 2^b`, with a fixed signed encoding convention.
The complexity guarantee is polynomial in r, c, and b, not in `2^b` or the
numeric magnitudes of entries.

### Output contract

Return integer matrices D of shape r-by-c, U of shape r-by-r, and V of shape
c-by-c, together with an active diagonal length t, satisfying:

```text
U M V = D
U and V are unimodular (invertible over the integers, determinant ±1)
0 ≤ t ≤ min(r,c)
D_ii = d_i > 0 for i < t, with d_i dividing d_(i+1)
all remaining entries of D are zero.
```

Thus t is the rational rank. D is unique; U and V need not be. The output
carrier contains the particular transformation matrices computed by the
deterministic algorithm, with their properties in the contract. Unique
encoding of each such output does not require unique transformation witnesses.

Retain U and V: diagonal entries alone do not suffice for subsequent subgroup
membership, coordinate transport, and coefficient recovery. All output entries
and all intermediate values must have polynomially bounded bit length in
r, c, and b. Reserve fixed polynomial bit capacities in their bounded domains;
prove that the chosen algorithm respects them. Polynomial output size alone
does not establish a polynomial intermediate-size or runtime bound.

### Finite-abelian subgroup membership

Given cyclic coordinates

```text
G = product_(k=1..r) Z/m_k Z,       m_k > 0,
generators h_1,...,h_s in G,       target h in G,
```

choose integer representatives H_kj and a_k for their coordinates and form

```text
M = [ H | diag(m_1,...,m_r) ],     M has r rows and s+r columns.
```

Then subgroup membership is exactly the ordinary integer feasibility problem
`M x = a`: its first s coefficients combine the supplied generators, and its
last r coefficients account for the coordinate moduli. A fixed common modulus
e is the special case `diag(m_k) = e I`. The diagonal modulus block makes these
queries full row rank, but the full rectangular matrix must be retained.
For example, `[1  2] x = 1` is solvable whereas `[2] x = 1` is not.

From `U M V = D`, set `a' = U a`. Prove the decision criterion

```text
d_i divides a'_i for i < t,
a'_i = 0 for t ≤ i < r.
```

If it holds, choose z_i = a'_i/d_i on the active diagonal and zero on the
remaining c coordinates; then `x = V z` is an integer solution. Return a
Boolean feasibility result, and provide a certified witness-producing variant
returning an explicit no-solution/solution alternative. The latter is a
mathematical outcome, not error handling. Include a bit-length parameter for
the right-hand side and moduli when applying this interface to varying data.

Smith reduction also describes the quotient by the subgroup: the cokernel
of M is the direct sum of `Z/d_i Z` for i < t and `Z^(r-t)`, and U transports
an integer vector to those quotient coordinates. For the positive-modulus
queries above t = r, so this quotient is finite. This supports both membership
tests and the finite-abelian quotient coordinates used by closure tests.
Construction of the cyclic-coordinate input from an SMP instance remains a
separate certified obligation; a bare abstract existence of coordinates is
not an executable conversion.

### What the implementation must accomplish

Provide signed binary integer domains and certified arithmetic, including
comparison, addition, multiplication, division with remainder, and the gcd
operations needed by a coefficient-growth-controlled normal-form algorithm.
These extend the initial fixed-table and polynomially bounded counter core:
an integer with polynomial bit length may have exponentially large magnitude.
Counting each unbounded integer arithmetic operation as one machine step is
insufficient.

Prove polynomial iteration counts, bit-operation costs, intermediate storage,
and machine runtime for rectangular and singular inputs, not only nonsingular
square matrices. Handle negative entries, zero matrices, zero rows or columns,
unit invariant factors, rank deficiency, and infeasible right-hand sides.
Then implement the augmented-matrix construction, decision criterion, witness
recovery, and coordinate transport as certified compositions.

## 4. Compressed exploration of exponentially many words

### Mathematical problem and input

Fix a finite ring R; the required first instance is `R = Z/e Z` for a fixed
positive integer e. Size parameters are an ambient dimension d, an output
dimension q, a number of layers l, and a menu capacity h. Work in the finite
module `V = R^d`. Input supplies an initial vector alpha, a linear readout
`beta : R^d → R^q`, and, for each layer j, a finite menu of at most h linear
maps `T_(j,s) : V → V`. Maps are stored matrices, not arbitrary runtime Lean
functions. Menu lengths are active counts in fixed-capacity arrays.

A word chooses one menu entry s_j at each layer. Define its states in forward
layer order by `v_0 = alpha` and `v_j = T_(j,s_j)(v_(j-1))`. The task is to
decide whether `beta(v_l) = 0` for every such word, and otherwise produce an
actual word for which it is nonzero. There can be h^l words; neither the
input representation nor the algorithm enumerates this collection.

### Output and correctness

Return an explicit alternative:

- `allZero`, with contract that every valid word has zero readout;
- a word of exactly l menu indices, each valid for its layer, whose computed
  final vector has nonzero readout.

Internally, compute retained pairs `(word, vector)` at each layer. Every pair
must be an actual path of the processed length, and its stored vector must
equal that path's evaluation. The span of retained vectors must equal the
span of all reachable vectors at that layer. A retained vector is not allowed
to be an arbitrary linear combination without its own actual path witness.

### Algorithm and polynomial certificate

Begin with the singleton `(empty word, alpha)`. At the next layer, apply
each menu map to every retained vector, extending its word by that menu index.
Greedily retain a candidate precisely when it is outside the span of already
retained candidates. Linearity proves that replacing a reachable set by a
spanning subset preserves the next layer's reachable span. Finally scan the
retained paths for a nonzero readout. If all are zero, linearity of beta proves
the universal answer; otherwise the retained word is the required witness.

Over a finite ring, a strictly increasing chain of additive subgroups of V
has length at most `log_2 |V|`, which is O(d) for fixed R. Retention therefore
has polynomial capacity even though V has exponentially many elements.
Reserve at least one initial entry, including for the zero module. Implement
span membership with a certified subroutine, using Smith reduction for the
required `Z/e Z` instance; a correctness-only callback is insufficient.

Prove polynomial bounds for candidate scans, matrix applications, adaptive
span calls, and copying or sharing word witnesses. Stored words have length
at most l. An empty menu leaves no paths through that layer, so the universal
answer is vacuously true. With l = 0 the only word is empty and its vector is
alpha. Cover repeated maps, zero maps, zero dimensions, and the one-element
ring. This example tests compression and existential witness production while
reasoning about an exponentially large semantic collection.

## 5. Central-direction saturation with shared witnesses

### A self-contained computational core

Fix a positive modulus e and let `V = (Z/e Z)^d`. Input supplies k seed
vectors and h additive endomorphisms of V, represented by d-by-d matrices.
The size parameters d, k, and h are independent. Compute the smallest additive
subgroup L containing the seeds and stable under all the supplied maps:

```text
seeds ⊆ L,       T_j(L) ⊆ L for every j.
```

Return a bounded generating list for L. Annotate each retained generator
with a shared expression DAG whose leaves are original seeds and whose
operations are additive combinations and applications of the supplied maps.
Interpretation of the DAG must equal the stored vector. Such expressions
are runtime data; the matrices are not new specialization parameters.

### Saturation algorithm and progress proof

Scan the seeds and the images of retained generators under every T_j.
If a candidate is outside the current subgroup, retain it and its annotation
and repeat. Stop when no such candidate remains. At that point the subgroup
contains all seeds and is stable: additivity extends stability from its
generators to all members. Every retained vector belongs to the least stable
subgroup by construction, proving equality rather than only an inclusion.

Each successful insertion strictly enlarges a subgroup of V, hence at least
doubles its cardinality. Since `|V| = e^d`, there are O(d) successful
insertions for fixed e. This is the mathematical progress certificate;
execution stops because no candidate remains, not because a counter budget
expires. A stable subgroup need not equal V, and a bounded state space alone
would not establish polynomial termination.

Use a certified span solver for membership, prove polynomial candidate scans
between insertions, and retain shared annotations without expanding their
trees. Cover no seeds, no maps, zero dimension, the one-element module,
redundant seeds, zero maps, and mutually dependent images. Support an optional
subsequent membership query with a Boolean result and a coefficient or
expression witness on success.

### Algebraic central-direction application

For the SMP application, let B be the generated algebra of a growing product
and `p : B → Q` a surjective homomorphism with abelian fibers. Prepared data
provide an additive direction group V, differences `delta(b,c)` for pairs
with `p(b) = p(c)`, and a section s choosing a representative above each
quotient value that is used. In the central case under consideration,
the contextual action on directions is independent of the quotient tags.

Prepare seeds from generator pairs `(b,s(p(b)))` and finite batches of
operation-defect pairs. An operation defect compares
`f(s(q_1),...,s(q_a))` with `s(f_Q(q_1,...,q_a))`; these lie in the same
fiber. The finite batch for f must span every such defect, without enumerating
all quotient tuples. Each argument position of each basic operation supplies
an additive context map T_j and a term construction realizing its action on
same-fiber pairs. Nullary operations contribute defects but no argument maps.

The algebraic theorem must identify the least stable subgroup generated by
these seeds with all realized differences in a fiber. Keep the pairs as
roots in a shared term DAG over the original generators, and prove that
their differences match the retained vector annotations. The generic
saturation proof alone does not imply this completeness theorem.

The full application must implement finite defect-batch construction,
sections on the queried bounded data, coordinate encoding, context actions,
and span membership through certified subprograms. Arbitrary functions on
the growing quotient and a bare completeness callback are not primitives.
The vector core can be accepted first; the algebraic extension is complete
only after its preparation and annotation obligations are discharged.

## 6. Compact-to-expanded Boolean clause encoding

### Input and mathematical meaning

Size parameters are the number n of Boolean variables and the number c of
clauses. A clause is an ordered triple of literals. Each literal consists
of an index in `Fin n` and a polarity bit indicating whether the variable
is negated. A formula is the conjunction of its clauses; a clause is the
disjunction of its literals. Repeated variables, repeated clauses, and
tautological clauses are permitted and retained in order.

Use the complete external size header and exactly c fixed-width records.
The compact encoding stores each index in `ceil(log_2 n)` bits and each
polarity in one bit. Its payload length is `c * (3 ceil(log_2 n) + 3)`.
The expanded encoding replaces each index i by an n-bit vector that is
true exactly at i, leaving the polarity unchanged. Its payload length is
`c * (3 n + 3)`. An additional output variant appends the eight-bit truth
table of the clause predicate on its three literal-position variables,
giving `c * (3 n + 11)` bits. Substituting the selected global variables
into that predicate recovers the clause semantics even when indices repeat.

### Output contract and invalid representations

Return the expanded formula encoding with exactly the same ordered literal
indices and polarities, and, for the truth-table variant, the corresponding
correct table. Decoding the output must recover the same mathematical formula
as decoding the input. Consequently every Boolean assignment satisfies the
input formula exactly when it satisfies the output formula.

The interpreter rejects unused binary index patterns and one-hot fields
with zero or multiple true bits. The algorithm's guarantee assumes valid
input and inserts no implicit error result. A separately specified inverse
conversion can decode each valid one-hot vector and emit its compact index,
with round-trip correctness on valid encodings.

### Execution and size obligations

Use counters for clause number, literal position, input offset, output offset,
and the selected variable index. For each literal, scan n positions and write
one true bit at its index, preserving its polarity. The truth table depends
only on the three polarity bits and can use a fixed finite lookup table.
Prove parsing and serialization lengths, cursor bounds, preservation of
unconsumed input, and completion of every output field.

These lengths are mathematical layout descriptions, not a requirement to
extend `Power` with logarithmic exponents immediately. With the current
polynomial expression language, reserve n bits per compact-index slot and
require zero padding above the minimum-width field, or hold the serialized
compact stream in a polynomial-capacity bit tuple with an active length.
Expose the exact serialized view separately. For n ≥ 1 the compact payload
is bounded by a polynomial in n and c. The c = 0 formula is valid even for
n = 0; no valid literal exists when n = 0. Singleton indices have width zero
and require no input index bits, while their one-hot output is `[true]`.

Certify preparation of the output region, tape navigation, binary counter
updates including carries, and input/output copying in actual machine steps.
No controller state may depend on the numeric value of n or an offset.
Polynomial time in n and c is the initial guarantee. It does not establish
logarithmic workspace or polynomial time in a different size measure that
counts only the binary header length while allowing arbitrarily many unused
variables. Stronger streaming and space bounds require separate certificates.

## Shared building-block libraries

These libraries belong to Polytime and are reusable targets in their own right.
Develop their operations when required by the examples, keeping the interfaces
mathematical and avoiding speculative additions. The first three application
targets retain their priority; libraries can be implemented incrementally as
their dependencies are needed.

Every executable operation must have a bounded input/output representation,
an explicit mathematical precondition and result contract, and proved
polynomial time and storage through the common machine realization. Generic
callbacks must be certified subprograms with matching contracts and bounds.
Bounds include representation conversion, copying, navigation, allocation or
frame initialization, and arithmetic. Users should compose qualitative
polynomial guarantees without calculating coefficients or degrees. A bare
Lean function, existence theorem, or unit-cost operation on unbounded data
does not satisfy this requirement.

### B1. Binary natural and signed integer arithmetic

Provide fixed-capacity binary representations, canonical signed encodings,
comparison, zero/sign tests, addition, subtraction, multiplication, division,
remainder, gcd, extended gcd, shifts, and magnitude bit-length calculation.
Distinguish polynomially bounded natural counters from integers whose bit
length is polynomially bounded but whose numeric value may be exponential.

Specify signed division with a nonzero-divisor precondition using the
Euclidean contract `a = b*q + r` and `0 ≤ r < |b|`. Specify nonnegative gcd
with `gcd(0,0) = 0`, and extended gcd returning coefficients u,v satisfying
`u*a + v*b = gcd(a,b)`. Natural subtraction must state whether it truncates
at zero or requires an ordering hypothesis. Bound results and intermediate
bit lengths, including those of Bézout coefficients, and prove actual
polynomial bit costs. Capacity exhaustion must be excluded by the operation's
proved bounds, rather than silently truncating arithmetic or adding an error.

### B2. Bounded tuples, buffers, and range operations

Provide indexed lookup/update, range copying, extraction of slices, and
concatenation into reserved capacity. Support active lengths inside fixed
capacities. Initialization and extension require explicitly supplied values
or a certified construction of them; the library must not assume every
carrier has a zero or default element.

Contracts state index/range bounds, active-length changes, copied values, and
preservation of untouched regions. Copying supports either disjoint regions
or explicitly specified overlap semantics implemented by a proved direction
or scratch-buffer strategy. Cover empty ranges, zero capacities, self-copy,
and boundary indices. Tape costs may depend on the containing frame size;
array access is not assumed to take one machine step.

### B3. Finite collection processing

Provide bounded search, membership tests, duplicate removal, filtering,
partitioning by tags, and packing active entries. Return source-index maps or
another explicit correspondence connecting retained values and annotations
to the original collection. Specify ordering conventions, such as retaining
the first occurrence and preserving relative order during filtering.

Equality and selection predicates must have certified implementations when
used at runtime. Distinguish list equality, set membership, and equality of
the mathematical object generated by a list. Removing duplicate vectors is
not a substitute for span compression. Search failure is an explicitly
specified mathematical alternative; it is not implicit error handling.

### B4. Permutations and coordinate transport

Construct and invert permutations and transport tuples, matrix rows/columns,
and heterogeneous tagged coordinates along them. Group coordinates by sort
while retaining a bijective correspondence with their original positions.
Provide conversion between global coordinates and sort-local positions using
bounded active-count metadata.

Prove forward/backward transport identities, tag compatibility, and preservation
of the represented mathematical object under reordering. When a caller needs
a bijection, make that precondition explicit; projection onto a subset of
coordinates is a separate operation and need not be invertible. Distinguish
position permutation from a catalogue isomorphism acting on coordinate values.

### B5. Scalar tables and basic matrix operations

Provide certified access to fixed finite-carrier operation tables, including
field and fixed-ring arithmetic. On top of scalar arithmetic, provide
matrix-vector and matrix-matrix multiplication, transpose, block assembly,
row/column exchange, scaling, and adding a scalar multiple of one row or
column to another. Maintain change-of-basis matrices when requested by a
reduction algorithm.

Contracts establish shapes, entry formulas, and the corresponding algebraic
identities. Invertibility assumptions belong only to operations that require
them: nonzero scaling over a field is invertible; arbitrary integer scaling
is not generally unimodular. Include zero dimensions and rectangular blocks.
Integer versions use B1 with proved bounds on sums, products, and intermediate
entries; finite-field versions use fixed tables. Gauss–Jordan and Smith
reduction are application algorithms built from this library, not assumed
primitives supplied by it.

### B6. Finite graphs, components, and transport paths

For graphs on a bounded finite vertex set, provide reachability, connected
components, deterministic representative selection, and paths or parent
pointers to representatives. Use bounded adjacency matrices or another
explicit bounded representation. Prove that returned components partition
the vertices and characterize reachability; include isolated vertices and
the empty graph.

For coordinate-dependency graphs whose edges carry isomorphisms from a fixed
catalogue, compose maps along returned paths and prove the transport formula.
An undirected edge must provide the inverse direction. Path independence is
not automatic: callers must establish the consistency of edge labels when
their contracts require a unique transported value. Store and access maps
concretely, without treating arbitrary Lean functions as executable labels.

### B7. Shared DAG construction and evaluation

Provide bounded gate storage, validation of earlier-node references, cached
evaluation, appending compiled term templates, merging DAGs, and root
reindexing. Specify the generator leaves, operation labels, gate arities,
and validity conditions. Contracts establish evaluation correctness,
preservation of old nodes, and the meaning of returned roots.

Track both the gate capacity and the node-value table, including values across
a growing product of coordinates. Bound copying and merge/reindex work as
well as newly appended gates. Term-tree expansion may be used in proofs but
must not be required during execution. Cover empty DAGs, shared subexpressions,
nullary gates, repeated roots, and the distinction between an output root
and an expanded mathematical term. More general annotated-expression DAGs,
such as those in example 5, need their instruction meanings and contracts
specified explicitly.

### B8. Encodings and prepared-frame execution

Provide parsing and serialization of the complete size header, computation
of domain widths and offsets, initial scratch/bootstrap routines, frame
formatting, region navigation, copying between call frames, subroutine
handoff, and output extraction. Connect canonical `BitVec` value encodings
to the marked working layout over the universal finite tape alphabet.

Each routine specifies its entry and exit head positions, marker invariants,
assigned region, and preservation of caller-owned storage. The wrapper proves
that a valid external input establishes the bare program's entry contract.
No guarantee is required on malformed input unless a validation algorithm
is explicitly requested. All controller states remain independent of runtime
size values. This library supplies the reusable machine proofs for B1–B7
and subsequent compositions; application authors need not manipulate markers.

### B9. Greedy compression with retained witnesses

Given candidates and a certified test for membership in the object generated
by retained candidates, keep a candidate precisely when it enlarges that
object. Preserve its original value, source identity, and witness annotation.
Prove generation/span preservation, validity of retained witnesses, and
polynomial storage and runtime under an explicit bound on successful insertions.

For vector spaces, suitable instances may return independent vectors. For
modules over rings and additive groups, promise a generating list with the
appropriate incremental nonmembership property, not a vector-space basis.
The membership test's correctness and costs are part of the certificate.
The library does not assume that arbitrary generated objects have polynomial
membership tests or short generating lists.

### B10. Finite closure and worklists

Provide saturation from seeds under explicitly represented operations or
certified consequence procedures. Maintain a bounded worklist and annotations;
stop when no missing consequence remains. Prove that every inserted value
belongs to the intended closure and that the final result is closed and least.
Supply loop rules using strict-growth or another proved polynomial progress
argument, rather than assuming bounded storage implies polynomial termination.

Support both closure in fixed-size catalogue products, using bitsets or
finite tables, and closure in growing modules, using generators and a span
solver. The former can enumerate a fixed carrier; the latter must not
enumerate the exponentially large ambient module. Generic closure has a
polynomial guarantee only under explicit capacity, candidate-generation,
membership-cost, and progress hypotheses. Prepare all runtime consequences
through certified programs; do not accept an unimplemented closure oracle.

### B11. Modular systems and finite-abelian group interfaces

Given explicit cyclic coordinates, construct the integer augmented system
for subgroup membership, invoke the certified Smith-form algorithm, and
translate the answer back. Provide coefficient recovery, finite-abelian
quotient coordinates, coordinate projection, and transport of represented
elements. Include a fixed-common-modulus specialization as well as explicitly
bounded varying positive moduli.

Prove the equivalence between modular combinations and integer feasibility,
the meaning of recovered coefficients, and the quotient-coordinate formulas.
Account for input, output, and intermediate bit lengths and matrix assembly.
Smith form is example 3, so this interface is built after that solver and
must not be used as an unproved premise to implement it. Extracting cyclic
coordinates from an abstract input-dependent group is a separate algorithm;
the group structure theorem alone does not provide the required runtime data.

### Dependencies and acceptance

The following map identifies the main library dependencies. B2 and B8 are
common to every external realization; other dependencies may be indirect.

| Example | Main additional libraries |
| --- | --- |
| 1. Gauss–Jordan elimination | B1 counters, B5 scalar and matrix operations |
| 2. Monolith preparation | B3 collections, B4 coordinate transport, B5 fixed tables, B10 fixed-size closure |
| 3. Smith normal form | B1 binary integers, B4 permutations, B5 integer matrix operations |
| 4. Layered-word exploration | B3 collections, B5 matrix application, B9 compression, B11 modular membership |
| 5. Central-direction saturation | B5 matrix actions, B7 annotations, B9 compression, B10 worklists, B11 membership |
| 6. Clause encoding conversion | B1 counters and bit operations, B3 bounded traversal |

Prioritize binary arithmetic, bounded buffers, basic matrix operations, and
shared DAG processing as independent milestones, while developing the
prepared-frame realization alongside the operations it implements. Common
contracts and proofs should be reused across examples. Library acceptance
requires the represented operations and their machine certificates, not only
abstract interfaces or operation counts that omit structural work.

Unrestricted finite precomputation on a fixed specialization, including its
congruence and subgroup lattices, remains permitted. These libraries need
certified runtime lookup and transport for that data; they do not require a
polynomial preprocessing bound uniform in the specialization's cardinality.
Data depending on a growing input must instead be computed and stored within
the certified runtime and capacity bounds.

## Reference provenance and current limits

The specifications above are self-contained.

Acceptance requires actual algorithms built from Polytime's library, their
mathematical contracts, bounded intermediate representations, and the complete
machine-runtime theorem. The reference projects are read-only design sources;
implementing these targets belongs in this repository.
