# Polytime2

A multi-tape implementation of polynomial-time algorithms.

## Implemented and proved

- Abstract encoded domains combine mathematical carrier families, exact bit
  widths, canonical encoding and partial decoding, round-trip laws, and an
  existential polynomial width bound. Fixed finite presentations supply the
  existing scalar codecs; examples cover tagged carriers and runtime bit widths.
  Presentations do not certify executable encoding, decoding, or width
  evaluation.
- Deterministic transitions over Mathlib's two-sided tapes, with separate
  alphabets, writes, and head movements for each tape.
- Counted execution, controller embedding, and sequential composition with one
  stationary handover transition.
- Injective tape wiring with exact-cost simulation and preservation of unwired
  tapes, including their head positions.
- Finite-machine polynomial certificates under mathematical preconditions,
  closed under wiring, sequencing, branching, and guarded while loops.
- Raw mathematical map contracts with relational representations and existential
  scratch, sequential composition, and guarded fold, while, and search rules.
- Explicit preserved caller context, with composition and wiring rules that
  expose preservation of unwired tapes and their head positions.
- Executable mathematical gcd with correctness, capacity preservation, and an
  iteration bound in binary capacity. A standard-convention gcd machine composes
  a zero guard, binary remainder, scratch clearing, and operand copies.
  It preserves both binary operands, accepts arbitrary writable contents, and
  returns valid output and scratch encodings.
- Two fixed catalogue maps at runtime-selected active coordinates, sharing array
  and scalar scratch, preserving both indices, the active count, and inactive
  data. Binary-encoded scalars use fixed finite tables; each map writes a
  separate array, and equal indices apply both maps sequentially.
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
- Fixed-width multiplication with a polynomial transition bound in both
  operand digit counts. `AddMultiply.contract` composes addition and
  multiplication on shared tapes and computes `(left + right) * multiplier`.
  Both accept arbitrary writable contents and return valid scratch encodings.
- Fixed finite pipelines hide controller injections and handovers behind stage
  contracts, preserving the standard tape convention at every transition.
- Fixed-width element copying in exactly `2 * width + 1` transitions, preserving
  the source and neighboring data and restoring both heads.
- Runtime-width copying, counter initialization and increment, and unary-size
  reading into binary counters under capacity hypotheses.
- Specialization-fixed encoded constants written from arbitrary output contents,
  without a source tape, in `2 * width + 1` transitions with a restored head.
- Binary decrement with a polynomial digit-cost certificate, fixed controller,
  unchanged digit capacity, and restored head position.
- Binary-indexed lookup/update with polynomial bounds in array length and index
  digit capacity, preserved arguments, restored heads, and zeroed scratch.
- Lookup followed by update with separate index tapes, a shared source array,
  and an internal element tape. Its mathematical contract proves indexed copy,
  immutable arguments, arbitrary initial writable contents, valid scratch,
  restored heads, and polynomial time with one handover transition.
- Standard array lookup/update certificates transferred to Mathlib's `TM0.init`
  through the generic `CallingConvention.Realizes.tm0` theorem, with polynomial
  input storage, time, and simulator space.
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
- Complete matrix row traversal initializes all nineteen writable tapes from
  immutable inputs, reads the unary column count into a binary limit, and runs
  the guarded column loop. Its polynomial contract includes zero columns,
  arbitrary initial writable contents, valid scratch values, and restored
  heads. A matrix-valued contract computes the ordinary mathematical row
  transform. Scaling, normalization, addition, and swapping reuse the shared
  field identities. Gauss–Jordan's standard controllers use this traversal.
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
  unary column size, and initializes every writable tape. Its TM0 certificate
  includes startup and preserves the mathematical row-equivalence and reduced
  row-echelon guarantees.
- Generic standalone TM0 output extraction erases every working track and
  boundary marker, leaving canonical binary output with the head at its start.
  Its polynomial bound includes extraction; empty output leaves a blank tape.

Tape count, alphabets, controller, and polynomial witnesses are fixed before
runtime size assignments. Loop progress measures are proof data, not fuel.
All algorithmic dependencies are defined within this implementation.

`CallingConvention.Realizes.tm0` retains track frames;
`CallingConvention.Realizes.tm0_output` extracts standalone binary words.
Both start from a padded simulator track encoding. Construction of that encoding
from an external size header and canonical input bits is not yet certified.

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

Lookup takes an immutable binary index and array and writes a separate element.
Update takes an immutable index, array, and replacement and writes a separate
result array. Both use temporary tapes, preserve their arguments, and restore
heads. Element bit width is a specialization constant; array length varies at
runtime. Runtime-dependent element widths remain unsupported.

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
  assignment. Blank, binary zero, and binary one are the entire source alphabet.
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
  contents may temporarily be invalid. `CallingConvention.Realizes` requires
  valid encodings on all writable tapes on return, including scratch, and
  restores their heads. Its output family includes every writable tape.

No separate output prefill is required: the same routine handles fresh blank
and reused output regions. Execution determines its write extent from the
read-only inputs, not from existing output contents. The realization proof
establishes the exact written width; an encoded domain need not supply a
separately certified executable width evaluator.

## Limits and next steps

- Adapt the raw mathematical composition, fold, while, and search rules to
  `CallingConvention.Runs`; current safe algorithm proofs handle this manually.
- Simplify nested tape names, wiring, and alphabet-compatibility proofs.
- Certify external input preparation and compose it with simulation and output
  extraction.
- Add quotient production, signed arithmetic, and the remaining bit arithmetic
  for integer matrices. Extend polynomial reparameterization of subprogram
  calls.

`MultiTape.Realizes`, `MultiTape.Computes`, `Copy.realizes`, and `Move.realizes`
remain raw interfaces without the standard calling convention. Higher-level
algorithm notation, the SMP targets, and Smith normal form remain future work.

Build from the repository root with `lake build Polytime2`, and use
`import Polytime2`. See [GOAL.md](../GOAL.md) for the shared specification and
[EXAMPLES.md](../EXAMPLES.md) for target algorithms and building-block
libraries.
