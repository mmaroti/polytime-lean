# Polytime2

A multi-tape implementation of polynomial-time algorithms.

## Implemented and proved

- Deterministic transitions over Mathlib's two-sided tapes, with separate
  alphabets, writes, and head movements for each tape.
- Counted execution, controller embedding, and sequential composition with one
  stationary handover transition.
- Injective tape wiring with exact-cost simulation and preservation of unwired
  tapes, including their head positions.
- Finite-machine polynomial certificates under mathematical preconditions,
  closed under wiring, sequencing, branching, and guarded while loops.
- Fixed-width element copying in exactly `2 * width + 1` transitions, preserving
  the source and neighboring data and restoring both heads.
- Binary decrement with a polynomial digit-cost certificate, fixed controller,
  unchanged digit capacity, and restored head position.
- Binary-indexed lookup/update with polynomial bounds in array length and index
  digit capacity, preserved arguments, restored heads, and zeroed scratch.
- Lookup followed by update with separate index tapes and shared array, element,
  and scratch tapes. This copies one selected entry to another with one handover
  transition and no full-array copy; both indices use the same digit capacity.
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
- Finite-table vector traversal with runtime coefficients, restored heads, and
  preserved surrounding cells, including regions inside a dense matrix. Row
  scaling, normalization, addition, and swapping instantiate this traversal.
- Unary-indexed finite-scalar lookup/update, row-major matrix access, scalar
  head tables, and unary counter increment/reset/decrement, with polynomial
  certificates and a constant-cost counter guard.
- Runtime row-major address construction and complete matrix-entry
  lookup/update, including address clearing, restored heads, and a polynomial
  TM0 certificate.
- Preserving unary counter comparison and guarded pivot search, returning the
  first eligible nonzero row or the row-count sentinel, with polynomial runtime
  and agreement with mathematical Gauss–Jordan pivot search.
- Shared complete matrix-row traversal for scaling, normalization, addition,
  and swapping, with runtime coefficients, restored heads, cleared traversal
  counters, and a polynomial TM0 certificate. Fixed scalar tables load
  coefficients without changing the matrix or indices.
- Preserving unary counter copies, including destination clearing and head
  restoration, for initializing pivot searches from the current pivot row.
- Reading self-delimiting unary size fields into initially blank counter tapes,
  preserving input data and restoring the counter head, with exact transition
  costs.
- Fixed-width conversion between canonical binary labels and scalar symbols,
  with finite controller memory and exact transition costs. Streaming
  preparation and serialization handle empty arrays, preserve surrounding data,
  and restore the required heads without preallocated output storage.
- Complete Gauss–Jordan elimination in a shared workspace: pivot search, swap,
  normalization, column clearing, and outer traversal agree with the
  mathematical algorithm. The finite TM0 program has polynomial runtime and
  storage, returning reduced row-echelon form with an invertible row
  transformation, including empty rectangular matrices.
- An external Gauss–Jordan wrapper parses the complete unary dimension header,
  initializes blank working tapes, decodes the canonical binary matrix, runs
  elimination, and serializes the result. Its polynomial certificate includes
  every preparation, serialization, and handover transition.
- A TM0 certificate for that wrapper starts with only the external input in a
  fixed track and all other tracks blank. The encoding adds constant framing,
  with no size-dependent padding or prepared working markers. Chosen
  finite-field enumerations use canonical binary labels, and the output track
  contains the serialized reduced row-echelon matrix.
- Complete external TM0 realization with physical output extraction: the machine
  erases every working track and boundary marker, leaving only canonical binary
  output letters with the head at the beginning. The polynomial bound includes
  extraction, and the empty output leaves a blank tape.

Tape count, alphabets, controller, and polynomial witnesses are fixed before
runtime size assignments. Loop progress measures are proof data, not fuel.
All algorithmic dependencies are defined within this implementation.

Intermediate TM0 certificates retain track frames; the complete Gauss–Jordan
certificate `GaussJordanExternal.realizes_output_tm0` extracts a standalone
binary word. Higher-level algorithm notation remains future work.

## Execution design

The implementation uses a deterministic multi-tape Turing machine. The finite
tape set, finite controller, and finite alphabet with a blank symbol for each
tape are fixed by the program and specialization, independently of runtime
sizes. Each tape extends in both directions and has its own head. A transition
reads the symbols under all heads and selects a new state, symbols to write, and
left, right, or stationary movements. Machine execution counts these
transitions.

Subroutines specify named tape roles, entry and exit states, valid encodings,
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

Lookup/update uses three argument tapes: a binary index, densely encoded array
data, and one element, plus temporary tapes. Element bit width is a
specialization constant; array length varies at runtime. Under the index-bound
hypothesis, lookup preserves the index and array and returns the selected
element; update preserves the index and supplied
element and changes only the selected array entry. Both restore agreed head
positions and scratch conditions. No implicit error result is introduced.
Runtime-dependent reserved element widths, needed for integer matrices, require
an explicit metadata convention in a later extension.

The general `Simulation` theorem transfers multi-tape certificates with
polynomial input storage to polynomial-time finite TM0 machines. Intermediate
simulator outputs retain the track layout; `TrackOutput` supplies physical
output extraction, instantiated by the complete external Gauss–Jordan theorem.

## Limits and next steps

- Lift tape-level certificates to mathematical input/output contracts with
  relational representations and existential scratch.
- Derive search, traversal, and fold rules, then refactor Gauss–Jordan's outer
  traversal to hide trace assembly, controllers, and explicit runtime bounds.
- Simplify nested tape names, wiring, and alphabet-compatibility proofs.
- Reuse the external parsing, initialization, simulation, serialization, and
  extraction adapters when adding algorithms.
- Add runtime-width binary arithmetic and polynomial reparameterization of
  subprogram calls. Fixed-width copying alone does not provide integer-matrix
  arithmetic with runtime bit capacities.

Recursive bounded-domain descriptions, a general size-expression evaluator,
the SMP targets, and Smith normal form remain future work.

Build from the repository root with `lake build Polytime2`, and use `import
Polytime2`. See [GOAL.md](../GOAL.md) for the shared specification and
[EXAMPLES.md](../EXAMPLES.md) for target algorithms and building-block
libraries.
