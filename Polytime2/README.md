# Polytime2

A multi-tape implementation of polynomial-time algorithms.

Encoded domain widths currently use exact polynomials. A possible future
generalization is a mathematical width function with a certified polynomial-time
unary evaluator. Avoid requiring only a polynomial upper bound: it does not
supply the operational width computation needed by generic tape algorithms.

## Directory layout

| Directory | Contents |
| --- | --- |
| `Machine/` | Multi-tape semantics, wiring, costs, storage, and conventions. |
| `Encoding/` | Bit encodings, encoded domains and arrays, width evaluation. |
| `Computation/` | Specifications, realizability, composition, and layouts. |
| `Primitives/` | Head movement, copying, scans, size reading, finite tables. |
| `Arithmetic/` | Binary arithmetic, counters, multiplication, and gcd. |
| `Arrays/` | Fixed/runtime-width access, copying, updates, and indexed maps. |
| `Matrices/` | Addressing, entry access, row access, and row operations. |
| `GaussJordan/` | Pivot search, column clearing, and elimination. |
| `TM0/` | Simulation, serialization, input/output handling, and export. |
| `Examples/` | Examples exercising the framework and algorithms. |

Concrete computation interfaces live beside their implementations, usually in
`Operations.lean`; `Computation/` contains the abstract machinery. Foundational
modules use `Basic.lean`. File names omit the former `Standard` prefix;
mathematical helpers use descriptive names where needed to avoid collisions.
The directory reorganization preserved namespaces and declaration names.

## Implemented and proved

- Abstract encoded domains combine mathematical carrier families, exact bit
  widths given by concrete multivariate polynomials over `ℕ`, canonical
  encoding
  and partial decoding, and round-trip laws. Fixed finite presentations supply
  the existing scalar codecs; examples cover tagged carriers and runtime bit
  widths.
  Encoding and decoding remain mathematical specifications.
- Heterogeneous records concatenate their field encodings directly. Their width
  is the sum of the field polynomials. Certified construction uses one input
  tape per field; projection uses one record input and one field output.
  Widths may depend on runtime sizes, including for nested array fields.
- Variants store a binary discriminator followed by every alternative's field.
  Inactive fields contain zero bits; decoding rejects nonzero inactive fields.
  The exact width is the discriminator width plus all alternative widths.
  Certified operations include injection, tag extraction and tests, projection
  with a matching-tag precondition, and case analysis requiring only the
  selected branch's precondition. No delimiters occur inside either encoding.
- Record arities and variant catalogues are fixed by specialization. Polynomial
  offset and length headers are private. `recordOutputs`, `namedRecordOutputs`,
  and `pairOutputs` collect certified results from shared immutable arguments;
  `withEncodedOutput` changes a result's mathematical interpretation when its
  canonical bits agree.
  `Examples/Records.lean` covers runtime widths, nested arrays, empty families,
  zero-width payloads, inactive-field rejection, and standalone TM0 export.
- Every fixed width polynomial has a certified finite unary evaluator. It
  receives one immutable unary size tape per parameter, prepares its private
  copies, and returns exactly that many unary ones with restored public heads.
  Its region-preserving certificate accepts arbitrary private contents and
  includes preparation and output restoration in the polynomial runtime bound.
  `EncodedDomain.width_computable` supplies this evaluator for every domain,
  including arrays with runtime-dependent element widths.
- `Realizable.atComputedSizes` calls a computation at input-dependent sizes
  stored as bounded unary data. Its dependent input and output domains retain
  the exact mathematical payloads, with binary zero padding to polynomial
  capacities. Private header preparation, width evaluation, argument extraction,
  execution, and result padding are included in the certificate, including zero
  sizes and empty parameter or argument families. `Realizable.substitute`
  handles fixed polynomial assignments using the same header compiler.
  `Examples/DynamicSizes.lean` counts leading true flags and invokes a quadratic
  evaluator at that actual count, with a standalone TM0 certificate.
- `arrayLookup` and `arrayUpdate` take coordinates in `Fin length`, with no
  independent counter capacity or separate range precondition. Their binary
  coordinate codec uses the polynomial array length as its exact bit width.
  The existing machines support arbitrary element widths, including nested
  arrays. `matrixLookup` and `matrixUpdate` accept row and column pairs through
  the same row-major codec. Capacity-sensitive array operations remain internal
  building blocks for algorithms with binary counters.
- `matrixEntry`, `matrixReplace`, and `rowTransform` expose only row and column
  counts as sizes. Separate coordinates have carriers `Fin rows` and
  `Fin columns`; every input is admissible. Private capacity and unary header
  preparation use the shared compiler also used by Gauss–Jordan elimination.
  The coordinate codec retains the internal controller's binary digits, and
  the older capacity-sensitive routines remain under `Realizable.Internal`.
  Row transformations take ordinary specialization-fixed scalar functions.
- `arrayPack` stably selects an array by a Boolean mask and returns its count
  and exact-length mathematical array in `EncodedDomain.boundedArray`.
  Counters and zero capacity padding are private; element widths may depend on
  sizes, including for nested arrays and tuples. `arrayPackWithPositions`
  supplies one shared prefix-count table for related fields and dependencies.
  `boundedArrayCallFrame` connects stored packed results to
  `Realizable.atComputedSizes` without repeating packing; `preparePackingCall`
  includes the packing stage. Original sizes are preserved and the retained
  count supplies one new runtime size.
  `Examples/Packing.lean` covers stable indices, shared fields, empty and
  zero-width cases, and an exact-array consumer with a TM0 certificate.
- Deterministic transitions over Mathlib's two-sided tapes, with separate
  alphabets, writes, and head movements for each tape.
- Counted execution, controller embedding, and sequential composition with one
  stationary handover transition.
- Injective tape wiring with exact-cost simulation and preservation of unwired
  tapes, including their head positions.
- Finite-machine polynomial certificates under mathematical preconditions,
  closed under wiring, sequencing, branching, and guarded while loops.
- Explicit preserved caller context, with composition and wiring rules that
  expose preservation of unwired tapes and their head positions.
- Executable mathematical gcd with correctness, capacity preservation, and an
  iteration bound in binary capacity. A standard-convention gcd machine composes
  a zero guard, binary remainder, and operand copies.
  It preserves both binary operands, accepts arbitrary writable contents, and
  returns a valid output encoding.
- Two fixed catalogue maps at runtime-selected active coordinates, preserving
  both indices, the active count, and inactive data. Binary-encoded scalars use
  fixed finite tables; each map writes a separate array, and equal indices apply
  both maps sequentially.
- `RestoringScan` shares finite-memory traversal, boundary handling, and safety
  proofs between binary transducers and copying. `ScanReturn` handles named
  groups of moving heads and caller-supplied termination actions, including
  arithmetic carry outputs and Boolean guards. Empty words and arbitrary old
  output contents are supported; fixed-width slice copying remains distinct.
- Runtime-width binary addition with a final carry digit, linear transition
  cost, preserved operands and neighboring storage, and restored heads. Its
  mathematical contract states exact natural-number addition.
- Runtime-width binary subtraction with an exact signed-difference contract,
  a final borrow that also detects unsigned underflow, and linear tape cost.
  Addition and subtraction reuse one finite-memory ripple scanner.
- Binary long remainder with a mathematical contract and a quadratic tape
  bound, preserved operands, restored heads, and fixed-width scratch. A shift
  and subtraction followed by selection process each dividend bit once, using
  separate result tapes and finite carry or borrow memory.
- `StandardBitFold.runsValues` tracks live multiplication and remainder
  accumulators through representation predicates. Private scratch needs only
  region bounds. Gcd uses `Runs.whileValues` for two live operands, without
  scratch recurrences or final scratch clearing. Mathematical product and
  remainder functions are independent of private tape contents.
- Fixed-width multiplication and compound `(left + right) * multiplier` and
  `factor * multiplier + addend` computations with immutable operands and
  arbitrary initial writable contents.
- Fixed finite pipelines hide controller injections and handovers behind stage
  contracts, preserving the standard tape convention at every transition.
- Fixed-width element copying in exactly `2 * width + 1` transitions, preserving
  the source and neighboring data and restoring both heads.
- Runtime-width copying, counter initialization and increment, and unary-size
  reading into binary counters under capacity hypotheses.
- Finite tables accept arbitrary finite families of fixed encoded arguments and
  results, each with its own width. One controller and contract cover binary
  tables, unary predicates, and row-entry combinations, including zero-width
  words and empty families. `Computation.finiteOperation_realizable` exposes the
  single-result case for arbitrary finite argument names. No dummy inputs or
  scratch tapes are required.
- Specialization-fixed encoded constants written from arbitrary output contents,
  without a source tape, in `2 * width + 1` transitions with a restored head.
- Binary decrement with a polynomial digit-cost certificate, fixed controller,
  unchanged digit capacity, and restored head position.
- Binary-indexed lookup/update with polynomial element widths and lengths,
  preserved arguments, and restored heads. Unary width preparation is internal;
  only declared results require valid encodings on return.
- Indexed copy derived from public lookup and update composition rules, with
  separate indices and a shared immutable source array.
- Array lookup/update exported to Mathlib's `TM0.init` from delimited public
  inputs, with width preparation and output extraction included in the
  polynomial runtime bound.
- Storage bounds at every counted execution prefix, derived from input capacity
  and time; each transition adds at most two cells per tape.
- Exact translation of one-tape routines to Mathlib's TM0, with two transitions
  per source transition, finite controllers, and transferred polynomial bounds.
- Marked scan-and-return routines on TM0 with finite controller memory,
  preserved neighboring regions, restored heads, and cost `4 * rowCount + 6`.
- Multi-track representation with one head marker per simulated tape. TM0
  sweeps collect exactly the source head symbols and perform simultaneous
  source writes, with polynomial certificates and preserved marker positions.
- Selected head-marker movement in either runtime direction, with a polynomial
  TM0 certificate, restored physical head, and preservation of every other
  simulated tape. This routine requires an already padded interval.
- Physical interval extension into adjacent blank cells, preserving payloads,
  with TM0 cost `4 * rowCount + 18`. Composing it with marker movement realizes
  a complete selected-head move with bound `8 * rowBound + 34`.
- Runtime dispatch of complete source actions through a fixed finite tape
  catalogue, including stationary heads, writes, padding, and controller
  handovers.
- A finite TM0 simulator transferring multi-tape polynomial certificates and
  polynomial input storage to polynomial runtime and output row bounds.
- Canonical initial track encoding for every bounded source tape collection,
  with lookup/update TM0 certificates proving the exact array and element
  outputs.
- Standard `TM0.init` entry, including its default start state and head
  position, with one charged startup transition before the simulator runs.
- Independent mathematical Gauss–Jordan correctness: reduced row-echelon form
  and an invertible row transformation, including empty rectangular dimensions.
- Binary finite-table array maps with runtime coefficients, immutable inputs,
  arbitrary initial outputs, and restored heads. Standalone row scaling and
  normalization use scalar arrays; addition and swapping use arrays of scalar
  pairs.
- Row-entry scalar tables also accept the coefficient, source, and target on
  three separate immutable tapes, returning two separate encoded scalars.
  Both outputs are overwritten, with restored heads and a constant cost fixed
  by the specialization, including zero-bit presentations.
- A complete standard-convention matrix row-entry controller reads both
  original entries before combining and replacing them in a separate result
  matrix. Its polynomial contract covers coincident rows, arbitrary initial
  writable contents, shared arithmetic scratch, and valid intermediate values.
  An internal column step commits that result to a private working matrix and
  advances a fixed-width binary counter through a separate increment output.
  Two consecutive column steps reuse these tapes without external preparation.
- Complete matrix row traversal initializes only the working matrix, result
  matrix, and column counter, reads the unary count into a binary limit, and
  runs the guarded column loop. Its polynomial contract includes zero columns,
  arbitrary initial writable contents and restored heads. A matrix-valued
  contract specifies only the result matrix. Scaling, normalization, addition,
  and swapping reuse the shared field identities. Gauss–Jordan's standard
  controllers use this traversal.
- Standard-convention matrix lookup and replacement compute a binary address
  from separate row and column inputs and the unary column-size tape, then
  access the encoded array. Replacement writes a separate result matrix.
  Address arithmetic and access share scratch tapes; arbitrary initial writable
  contents and zero-bit scalars are supported.
- Standard guarded pivot search with binary counters, returning the
  first eligible nonzero row or the row-count sentinel, with polynomial runtime
  and agreement with mathematical Gauss–Jordan pivot search.
- Complete Gauss–Jordan elimination in a shared workspace: pivot search, swap,
  normalization, column clearing, and outer traversal agree with the
  mathematical algorithm. The finite TM0 program has polynomial runtime and
  storage, returning reduced row-echelon form with an invertible row
  transformation, including empty rectangular matrices.
- Standard Gauss–Jordan startup copies the immutable encoded matrix, reads the
  unary column size, and initializes only live counters. Its TM0 certificate
  includes startup and preserves the mathematical row-equivalence and reduced
  row-echelon guarantees.
- Generic standalone TM0 output extraction erases every working track and
  boundary marker, leaving canonical binary output with the head at its start.
  Its polynomial bound includes extraction; empty output leaves a blank tape.
- Generic delimited input preparation initializes every input track and blank
  output/scratch track in one sweep, without evaluating domain widths.
  `Computation.Realizable.tm0` exports every realized computation to a finite
  TM0 machine, including preparation, simulation, extraction, and startup in
  its polynomial bound. Empty blocks and absent size or input tapes are covered.

The SMP development in `Examples/SMP/` proves coordinate-image restriction,
finite subdirect SI decomposition, membership transport, and the full monolith
graph equation. `Prepared.prepare` is the certified public conversion. It
returns either an actual rejected original coordinate or a dependent frame
containing the exact sort counts `n_1, ..., n_k`, the generator count `g`, and
the ordinary prepared instance. Internal quotient blocks, capacity padding,
source labels, and retained original sizes do not occur in the mathematical
prepared payload.

`Multisorted.lean` defines this conversion-independent interface for a fixed
catalogue `D_t`. Its input carrier is exactly generators and a target in `∏ t,
D_t ^ n_t`; `preparedDomain` adds Boolean dependency masks. Exact coordinate
columns and rectangular dependency blocks use ordinary record and array codecs.
`IsPrepared` specifies ordered SI sorts, subdirectness, bounded earlier
dependencies, and monolith quotient isomorphisms onto the generated dependency
projections, agreeing with fixed catalogue lookups.
`Prepared.prepare_specification` proves rejection or these guarantees together
with equivalence of the original SMP membership question and exact runtime
counts.

Stable packing uses a common source-coordinate selection for targets,
generators, and dependency labels. Generic polynomial-width comparison and
rectangular array product maps construct the masks. Extended computed-size
frames retain original dimensions only while constructing the result; their
projection removes those dimensions before exposing the prepared frame.
Singleton argument records reuse identical canonical bits.
`atComputedUnarySizes` invokes any certified unary computation on a value at
its stored sizes and retains those sizes with the result. It hides singleton
argument records and preserves the consumer's own precondition. Prepared SMP
consumers and preparation itself specialize this generic operation.
Packed-array extraction shares one field-copy theorem, including size-dependent
element conversions with identical canonical bits.

`Prepared.prepareAndConsume_realizable` composes preparation with any certified
unary consumer whose precondition follows from `IsPrepared`. The result
preserves explicit rejection and evaluates the consumer at the actual sort
counts. The computed-size compiler and `consumerPolynomial_bound` use
`n_t ≤ n` and the unchanged `g` to give a polynomial bound in the original
dimensions.
`prepare_tm0` and `prepareAndConsume_tm0` include all preparation, simulation,
and extraction in their standalone TM0 certificates.

`RingExample.lean` specializes the conversion to `ZMod 4`, checks
empty-coordinate acceptance, and composes a certified target consumer.
`MultisortedExample.lean` also covers two distinct finite rings, absent sorts,
and empty catalogues. Specialization uses finite mathematical choices: the
result proves existence of a machine for each fixed algebra rather than an
executable compiler from operation tables.

Tape count, alphabets, controller, and polynomial witnesses are fixed before
runtime size assignments. Loop progress measures are proof data, not fuel.
All algorithmic dependencies are defined within this implementation.

`CallingConvention.Realizes.tm0` retains track frames;
`CallingConvention.Realizes.tm0_output` extracts a declared binary output.
Both lower-level adapters start from a padded simulator track encoding.
`CallingConvention.Realizes.tm0_delimited` prepares ordinary delimited input
blocks and extracts a selected output;
`Computation.Realizable.tm0` hides all implementation witnesses behind the
public `Computation.TM0Realizable` predicate.

For gcd, size parameter `b` fixes the binary width of both separate operands
and the result. A separate immutable tape stores `b` in unary. The contract
requires twice the second operand to fit in `2^b`, reserving shift capacity.
The output is the nonnegative binary gcd, including `gcd(0, 0) = 0`.

## Execution design

The implementation uses a deterministic multi-tape Turing machine. The finite
tape set, finite controller, and finite alphabet with a blank symbol for each
tape are fixed by the program and specialization, independently of runtime
sizes. Each tape extends in both directions and has its own head. A transition
reads the symbols under all heads and selects a new state, symbols to write, and
left, right, or stationary movements. Machine execution counts these
transitions.

Internal subroutines specify tape roles, entry and exit states, valid encodings,
boundaries, head positions, scratch requirements, and preservation contracts.
Sequential composition uses the disjoint union of controller states; a
handover transition enters the next routine without changing tapes or heads.
Additional coordination work requires explicit transitions and cost proofs.

Disjoint union of tape sets supplies independent storage, but explicit wiring
also permits sharing. Embed each component's tape names injectively into an
enclosing finite tape set, with matching alphabets and blank symbols. Components
preserve every tape outside their image. Different components may share tapes;
injectivity prevents aliasing within a component. Wiring is static, and the
first component's contract must establish the next component's precondition. The
composite tape count is the sum for disjoint wiring; shared tapes are counted
only once. Only the active component controls its wired tapes. Reserve private
scratch tapes as needed and reuse them only under compatible contracts.
`MultiTape.relabel` transports machines across blank-preserving alphabet
equivalences without changing transition counts.

Lookup takes an immutable binary index and array and writes a separate element.
Update takes an immutable index, array, and replacement and writes a separate
result array. Both use temporary tapes, preserve their arguments, and restore
heads. Both element bit width and array length may be polynomial expressions in
runtime sizes. Width evaluation prepares a private unary header, including from
arbitrary scratch contents. Nested arrays support extracting and replacing whole
rows through the same generic lookup and update certificates.
Fixed and unary-width commands share navigation and block-copy layouts, the
encoded-array bridge, and a separate-output update controller. Transfer proofs
handle lookup and replacement through the same direction parameter. Fixed
commands retain their smaller tape sets and controller-dependent costs;
converting them to unary-width commands would require a private width header.

The general `Simulation` theorem transfers multi-tape certificates with
polynomial input storage to polynomial-time finite TM0 machines. Intermediate
simulator outputs retain the track layout;
`CallingConvention.Realizes.tm0_output` supplies physical output extraction for
standard routines.

## Standard calling convention

The source routines use this interface for their public algorithms and internal
arithmetic, gcd, array, matrix, and elimination steps. Lower-level machine
traces remain implementation details behind those contracts.
Simulator track markers belong to the TM0 backend and never appear on source
tapes.
`CallingConvention` records immutable inputs, arbitrary initial output
contents, fixed regions, restored heads, and preservation at every transition.

- Size parameters occupy separate read-only tapes, each encoded as that many
  unary ones surrounded by blanks. Zero has an empty data region.
- Each input and each output occupies a separate tape and has an encoded
  domain. Its fixed data width is determined by the specialization and size
  assignment by evaluating its width polynomial. Valid encodings use only binary
  zero and one. Blank is reserved for cells outside canonical data regions.
- Input regions contain canonical encodings and are never modified. Output
  regions initially contain arbitrary symbols, including blanks; outside each
  region, every cell is blank. Outputs do not alias inputs or one another.
- Each output region is completely overwritten with its canonical encoding,
  consisting of exactly its domain width of nonblank binary symbols. Cells
  outside every data region remain blank throughout execution.
- Every input, output, and size-parameter head points to the start of its data
  region before and after execution. For an empty region, this is the same
  designated blank cell on entry and exit.
- Private scratch tapes also have encoded domains and fixed regions. Their
  contents need not be valid, even on return. Only declared outputs must contain
  valid encodings. Validity is required only when a value is exposed as an
  output or consumed as a mathematical input, including a subroutine argument.
  Scratch has no independent validity obligation; its fixed region and restored
  head are still required.

No separate output prefill is required: the same routine handles fresh blank
and reused output regions. Execution determines its write extent from the
read-only inputs, not from existing output contents. The realization proof
establishes the exact written width; an encoded domain need not supply a
separately certified executable width evaluator.

The generic TM0 export serializes unary sizes first, then encoded arguments,
in a specialization-fixed order. Five distinct nonblank letters encode binary
zero, binary one, a separator, and two framing delimiters:

```text
begin # size_1 # ... # size_s # input_1 # ... # input_m # end
```

Empty blocks retain their separators. With no public inputs the word is
`begin # end`. Output contains only binary result letters; all framing and
working storage are erased, and the head returns to the output's start.

## Mathematical specifications and implementations

- `Computation` specifies finitely many named input encoded domains, one output
  encoded domain, a precondition, and a mathematical function total on the
  subtype of admissible inputs, all parameterized by the size assignment.
  Each argument occupies its own tape; sizes have separate unary tapes.
- `Computation.Realizable computation` existentially quantifies finite scratch
  names and domains, controller states, a machine, entry/exit states, and its
  `CallingConvention.Realizes` execution certificate. There is no implementation
  structure in the public interface; polynomial witnesses remain existential.

Application proofs MUST NOT unpack realizations or depend on their machines,
scratch layouts, execution traces, or polynomial witnesses. Reuse computations
ONLY through certified mathematical composition rules. Missing rules must be
added to the library, not bypassed by inspecting an existing realization.
Witness handling belongs exclusively to foundational library proofs in
`Computation.Realizable.Internal` and the implementations of certified rules.

Internal primitive adapters place named size, argument, and result roles using
`ofNamedLayout`; the remaining source tapes become private automatically.
Domain equalities determine carrier transport, widths, and encodings. Restoring
calls share `Runs.wire_restoring` and `Realizes.wired_runs` for tape placement
and preservation proofs.

`Computation.Realizable.followedBy` feeds a result to a single-argument
computation. `letThen` retains the original arguments alongside that result for
the continuation; nested bindings describe DAGs. `withArguments` selects inputs
injectively from a larger context. `onResults` prepares every callee argument
using certified computations on a shared context. `withRecordArgument` accepts
the entire argument family on one record tape. Callers prove domain and
precondition compatibility mathematically. `withPrecondition` restricts
admissible inputs.
Indexed array maps, sequential catalogue maps, and matrix access use `onResults`
and `argument` directly instead of constructing nested argument contexts and
routing embeddings. Fixed finite operations accept ordinary functions on the
specialized carriers, without an empty runtime size assignment.
`withSpecification` replaces a specification after proving agreement.
`withConstantSizes` reuses a specialization-fixed computation alongside sizes.
`reindexDomains` changes mathematical carriers through equivalences with the
same widths and canonical bit lists, without bit-vector casts in the encoding
obligations. Constructor lemmas for arrays, products, records, fixed domains,
and parameter renaming share these comparisons. Equal canonical words remain
equal under resizing. Matrix access reuses array computations this way.
`withEncodedInputs` also permits input maps into proper subdomains when their
canonical bits agree. It composes existing field copying and argument routing;
no new representation or machine primitive is needed.
`choose` reads a Boolean argument and requires only the selected branch's
precondition; uncalled branch scratch stays arbitrary.
`arrayFold_realizable` traverses an immutable array while updating an
accumulator through a certified computation. Applications supply the update's
precondition, an indexed invariant, and initialization and preservation proofs;
`arrayFold_total_realizable` omits those obligations for total updates.
Element widths, accumulator widths, and array lengths may depend on sizes.
`arrayTransform_realizable` lifts a total certified element computation to an
array, with immutable context and different runtime-dependent input and output
widths. A fold collects raw encoded blocks in a private queue, so the output
domain needs no default element. Record projection and construction implement
the queue; finite-table array maps specialize this same construction.
`Examples/Transform.lean` covers different widths, empty carriers, and TM0
export.
`boundedIteration_realizable` derives polynomially bounded repetition from the
fold, allocating its zero-bit traversal array privately. Both rules hide
counters, temporary values, copies, width headers, and polynomial costs.
`ArrayFold.prefix_invariant` and `boundedIteration_invariant` supply the
mathematical correctness arguments; `withSpecification` can expose a proved
answer instead of the fold expression.
`Examples/Fold.lean` covers runtime-width words, immutable context, empty
arrays, zero-width values, partial updates, and standalone TM0 export.
`whileLoop` uses a mathematical invariant, decreasing measure, and existential
polynomial bound. Its conserved answer equals the state when the guard stops;
the library handles state copies, scratch, and all execution costs.
`BinaryTraversal.comparison_runs` places a shared binary comparison in a named
workspace. `BinaryTraversal.range_runs` combines that guard with a certified
body and an arbitrary invariant over the live values. It maintains size headers
and bounded scratch, proves that the counter advances without wrapping, and
derives the polynomial cost for the whole interval, including empty intervals
and nonzero starts.
Matrix row traversal, Gauss–Jordan clear intervals, and outer elimination use
this rule; their proofs retain only the live values and mathematical updates.
Internal workspaces use `Runs.whileValues` for mathematical state families and
`Runs.whileRange` for bounded traversals. Immutable context stays in the
representations; only live variables require encoding proofs. `Initialization`
compiles finite copy, clear, and constant plans through `Pipeline.updates_runs`
and supplies shared unary-size reading. Matrix and elimination controllers use
these rules without preparing unused scratch, including for empty loops.
`CallFrame` and `Runs.frame` carry all region bounds and immutable caller values
through restoring calls. Matrix row steps, row clearing, and elimination bodies
use `Pipeline.runs_chain` for call, commit, increment, and advance stages; stage
handover costs are included in their polynomial bounds. Wired increments share
one adapter and preserve every caller tape except their separate result.
Compound arithmetic composes addition at a named capacity with multiplication.
It retains one intermediate word and the primitives' scratch: three binary words
and two flag tapes in total. It adds no operand copies and takes one additional
transition compared with the former standalone controllers. The matrix-address
controller retains its shared-workspace lowering.
Public certificates cover constants, unary-size reading, counter initialization,
copying, increment/decrement, nonzero tests, comparison, bounded arithmetic,
compound arithmetic, remainder, gcd, finite tables and predicates, array
lookup/update and mapping, indexed finite operations, catalogue maps, matrix
address calculation, access by flat index or row and column, row transforms,
and Gauss–Jordan elimination.
The arithmetic, gcd, countdown, indexed-copy, catalogue, finite-field row, and
elimination examples use these rules without implementation fields.

The public Gauss–Jordan computation has only row and column size parameters,
with every rectangular matrix admissible. Its counter capacity is private;
the library constructs its unary header and includes that work in the
polynomial runtime bound in the two public dimensions.

Implementation changes require no downstream proof edits when specifications
and realizability statements stay unchanged. Lean may rebuild dependent modules;
executable implementations are not a requirement.

## Next steps (remove completed steps)

For consolidation work, identify the implementations to replace before adding
an abstraction, and measure net lines removed, including the new machinery.
The immediate goals below follow the recommended implementation order. Estimates
are rough net changes in Lean code, include new machinery, overlap, and should
not be added together.

### Remainder capacity (~40–90 net lines added)

**Remove the long-division restriction from public remainder.**

[binaryRemainder](Arithmetic/Operations.lean)
requires both a positive divisor and
`2 * divisor ≤ 2 ^ capacity`. The latter reserves a shift bit for the
implementation; it is not a mathematical requirement for remainder.

Widen operands privately, call the existing implementation, and return
the result at the original width. The public precondition should only
require the chosen mathematical divisor condition.

### Dependency sets (~20–70 net lines added)

**Expose SMP dependencies as finite sets.**

[Dependencies](Examples/SMP/Multisorted.lean)
is currently a family of Boolean masks. Then
[dependencySet](Examples/SMP/Multisorted.lean)
converts those masks into sets for mathematical statements.

A natural carrier would be
`Coordinate → Finset Coordinate`. The codec can retain exactly the same
characteristic-bit representation through `EncodedDomain.reindex`.
This would let preparation conditions directly discuss membership,
cardinality, and projections without repeatedly translating Boolean
equations into set membership.

This improves mathematical usability; substantial line savings are less
certain.

### Preparation outcomes (~20 net lines removed to ~50 added)

**Replace numbered preparation outcomes with a mathematical sum.**

[preparationAlternatives](Examples/SMP/PreparedOutcome.lean)
exposes `Fin 2` tags. Its rejection alternative uses a bounded unary
value that also admits the all-accepted sentinel. Correctness later
proves that rejected outputs identify actual coordinates.

The natural result is:

```text
an original rejected coordinate
⊕
an exact size assignment together with its prepared instance
```

Derive a generic sum-domain interface from the existing variant codec.
Keep the sentinel inside the search algorithm. This would also simplify
the nested `Fin.cases` definitions in
[PreparedConsumer](Examples/SMP/PreparedConsumer.lean).
No new mathematical structure is needed.

Natural interfaces and fewer lines do not always coincide immediately.
In particular, sum results and finite-set dependencies may initially need
adapters. Their implementations should replace the current public forms,
rather than leave two parallel APIs permanently.

## Longer-term goals

### Integer arithmetic

Add quotient production, signed arithmetic, and the remaining bit arithmetic
needed for integer matrices, reusing generic arithmetic machinery.

### Algorithm notation

Develop higher-level algorithm notation over the certified mathematical
composition rules, keeping machine witnesses and scratch layouts internal.

### Algebra targets

Build consumers of the monolith-prepared SMP instance and implement Smith
normal form using the shared framework and generic integer-matrix operations.

The simulator's raw transport certificate remains internal.

Build from the repository root with `lake build Polytime2`, and use
`import Polytime2`. See [GOAL.md](../GOAL.md) for the shared specification and
[EXAMPLES.md](../EXAMPLES.md) for target algorithms and building-block
libraries.
