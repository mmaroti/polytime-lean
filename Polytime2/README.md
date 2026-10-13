# Polytime2

A multi-tape implementation of polynomial-time algorithms.

## Implemented and proved

- Abstract encoded domains combine mathematical carrier families, exact bit
  widths, canonical encoding and partial decoding, round-trip laws, and an
  existential polynomial width bound. Fixed finite presentations supply the
  existing scalar codecs; examples cover tagged carriers and runtime bit widths.
- Deterministic transitions over Mathlib's two-sided tapes, with separate
  alphabets, writes, and head movements for each tape.
- Counted execution, controller embedding, and sequential composition with one
  stationary handover transition.
- Injective tape wiring with exact-cost simulation and preservation of unwired
  tapes, including their head positions.
- Finite-machine polynomial certificates under mathematical preconditions,
  closed under wiring, sequencing, branching, and guarded while loops.
- Mathematical map contracts with relational representations and existential
  scratch, sequential composition, and a guarded mathematical fold rule.
- Explicit preserved caller context, with composition and wiring rules that
  expose preservation of unwired tapes and their head positions.
- Mathematical while and early-stopping search rules with logical invariants,
  decreasing measures, and conserved answers; runtime witnesses stay internal.
- Executable mathematical gcd with correctness, capacity preservation, and an
  iteration bound in binary capacity. A standard-convention gcd machine composes
  a zero guard, binary remainder, scratch clearing, and operand copies through
  the shared mathematical loop rule. It preserves both binary operands, accepts
  arbitrary writable contents, and returns valid output and scratch encodings.
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
  row-echelon guarantees. The older packed-input and prepared-frame wrappers
  have been removed.
- Generic standalone TM0 output extraction erases every working track and
  boundary marker, leaving canonical binary output with the head at its start.
  Its polynomial bound includes extraction; empty output leaves a blank tape.

Tape count, alphabets, controller, and polynomial witnesses are fixed before
runtime size assignments. Loop progress measures are proof data, not fuel.
All algorithmic dependencies are defined within this implementation.

`CallingConvention.Realizes.tm0` retains track frames;
`CallingConvention.Realizes.tm0_output` extracts standalone binary words.
Higher-level algorithm notation remains future work.

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
`StandardCopy` certifies fixed-width copying under this contract.
`StandardTerminatedCopy.contract` certifies runtime copying of any encoded
domain, with immutable unary size inputs and arbitrary output contents.
`StandardBinaryRipple` similarly certifies carry/borrow scans, instantiated by
the internal `BinaryAddition.rippleMachine` and
`BinarySubtraction.rippleMachine` controllers. The public
`BinaryAddition.algorithm` and `BinarySubtraction.algorithm` expose separate
immutable operands, low-word outputs, and carry/borrow outputs under
`CallingConvention.Realizes` contracts.
Both controllers have exact `2 * width + 2` execution bounds and handle empty
operands. The carry/borrow scanner also accepts either initial carry value.
`StandardBinaryScan.contract` certifies finite-memory digit maps between
encoded domains of equal width; its common exit hides private final memory.
The counter-clearing example instantiates this contract with a constant-zero
mathematical map. `StandardBinaryArithmetic.contract` supplies separate
encoded-domain tapes for two immutable operands, a low-word result, and carry;
its postcondition is the corresponding finite ripple map.
`StandardBinaryReduce.contract` certifies bounded natural remainder when the
dividend is less than twice the divisor. Its exact
bound is `4 * width + 7`; both operands remain immutable.
`StandardBinaryDivisionStep` composes shifting and reduction in
`6 * width + 10` steps, computing `(2 * remainder + bit) % divisor` under the
division invariant. Both accept arbitrary scratch contents and preserve every
region throughout execution. `StandardBinaryRemainder.contract` certifies the
complete long-division loop with bound `8 * width² + 19 * width + 6`, including
valid scratch results and unchanged operands. Its entry accepts entirely
blank output regions; the divisor must be positive and reserve shift capacity.
`StandardBinaryDecrement.contract` writes the predecessor of a positive
counter to a separate output, preserving its width and input, in
`2 * width + 3` steps.
`StandardBinaryGuard.contract` certifies the nonzero test in `2 * width + 2`
steps, including zero-width counters and initially blank one-bit outputs.
`StandardGcdStep.contract` computes `(b, a % b)` on separate output tapes in
`8 * width² + 21 * width + 9` steps, preserving both operands.
`StandardGcdMachine.runs` certifies the complete private Euclidean loop and
return cleanup, with bound `16 * width³ + 70 * width² + 102 * width + 56`.
Every scratch region is cleared to a valid encoding, including for zero
operands and empty words. `StandardGcd.contract` adds immutable separate inputs
and a separate output, with bound
`16 * width³ + 70 * width² + 108 * width + 65`.
The obsolete packed-input GCD controllers have been removed.
`StandardBinaryMultiplication.contract` uses separate immutable factor and
multiplier tapes, with independent widths `n` and `m`, and a separate result.
Its internal Horner step also has a mathematical contract for the shifted word,
low result, and carry, with arbitrary initial scratch. The multiplication bound
is `m * (6 * n + 14) + 6 * n + 14`; the result capacity must contain the
product. Initialization and scratch cleanup work even for empty operands.
`StandardBitFold` shares the restoring high-bit-first traversal with remainder
division.
Safe runs support control-state renaming, branching, sequential composition,
guard-driven loops, and wiring into larger tape collections.
`StandardTapeCommands` provides copy, clear, and Boolean initialization
commands for those callers. `StandardCounterZero.contract` initializes a binary
counter directly from its unary capacity tape.
`StandardBinaryIncrement.contract` certifies modular increment without growing
the counter. `StandardSizeRead.contract` reads an immutable unary size into a
binary counter when it fits, with arbitrary initial result and scratch.
`StandardPivotSearch.algorithm` composes workspace initialization, unary row
limit reading, and bounded first-nonzero search. Its `Realizes` contract returns
the row-count sentinel when no pivot remains, certifies the skipped prefix, and
validates every writable tape on return. Its returned row is bounded below by
the starting row; `StandardPivotSearch.field_runs` proves exact agreement with
mathematical `GaussJordan.findPivot` over the specialization's finite field.
`MultiplyAdd.contract` computes `factor * multiplier + addend` with the same
convention, providing the arithmetic needed for binary matrix addresses.
`booleanContract` verifies that initialization overwrites an
arbitrary one-bit output region and restores its head.
`Examples.Context` uses the new addition controller and proves preservation of
unrelated caller tapes.
`StandardArrayLookup.runs` certifies binary-indexed lookup with separate
immutable index and array tapes, arbitrary initial output and scratch, and
restored heads. Its private seek phase clears both counter words and the guard,
including at index zero. `StandardHead.BlankReturn` restores the array head
using surrounding blanks and handles zero-bit elements.
`StandardArrayUpdate.contract` specifies a separate immutable source array and
replacement, a separate output array, and valid fixed-width scratch outputs.
Its output contract proves that exactly the selected array entry is replaced.
`StandardMatrixLookup.contract` gives the same calling convention to
row-major rectangular matrices, using their mathematical matrix domain and
proving that the selected flat coordinate is returned.
`StandardMatrixUpdate.contract` writes that coordinate to a separate result
matrix and specifies the exact changed flat entry.
`IndexedCopy.contract` composes lookup and update without copying the
source array between calls; the selected source entry replaces the target
entry in a separate output array.
`StandardFiniteTable.contract` certifies specialization-fixed scalar operations
on binary arguments. `StandardArrayMap.contract` lifts them pointwise to
polynomial-length arrays, including empty arrays and zero-bit elements.
`FieldRow` uses these contracts for scaling, normalization, addition, and swap.
`StandardMatrixRowField.clear_target_contract` specializes row addition to
clearing a target entry when the pivot entry is one and the supplied scalar is
the negated target entry. This isolates the row-update phase of column
clearing. `StandardGaussJordanClearTarget.algorithm` composes standard
lookup, finite-table negation, and row traversal. Its `Realizes` contract proves
the complete row update with immutable arguments, arbitrary writable contents,
valid scratch, restored heads, and polynomial time.
`StandardGaussJordanClearStep.runs` certifies a complete internal row-clear
step: clear the target row, commit the separate result to the loop's private
working matrix, and advance its counter through a separate increment output.
All writable tapes return valid values, with polynomial time and restored
heads. `StandardGaussJordanClearInterval` supplies the guarded interval
controller, with verified comparison, body wiring, and exhausted-interval exit.
Its polynomial traversal theorem computes the ordinary matrix updates on an
interval excluding the pivot, stops at its limit, and returns valid scratch.
`StandardGaussJordanClear.handover_runs` certifies skipping the pivot and
loading the second interval's row-count limit while preserving both matrices.
The two interval calls and handover have a verified polynomial execution theorem
computing `clearColumn` and returning valid scratch. Caller initialization from
arbitrary writable contents now includes verified field-zero and working-matrix
seeding, reuse of the nineteen-tape row initializer, and extra-counter setup.
`StandardGaussJordanClear.algorithm` combines initialization and traversal under
a `Realizes` contract computing `clearColumn`, with immutable arguments, valid
scratch, restored heads, and polynomial time.
`StandardGaussJordanPivot` composes matrix copying, candidate-entry lookup,
swapping, normalization, and column clearing. The copy and lookup calls are
verified, as are the shared row calls, result commits, and final column-clear
call. Its complete `Realizes` contract computes `MatrixOperations.pivotStep`
with immutable arguments, arbitrary writable contents, valid scratch, restored
heads, and polynomial time. The enclosing column now has a complete
`Realizes` contract: it initializes the shared frame, searches the column,
applies the found-pivot branch, and returns both the updated matrix and next
pivot row. The outer elimination controller has a standard guard and a verified
body that commits the matrix and pivot outputs and advances the column without
overflow. Its polynomial loop theorem computes `eliminateColumns`. The complete
`StandardGaussJordanElimination.algorithm` initializes arbitrary writable
contents and computes `GaussJordan.eliminate` under a `Realizes` contract,
including empty rectangular matrices, with immutable input and valid scratch.
Its `realizes_tm0` theorem transfers this contract and the mathematical
row-equivalence and reduced-row-echelon guarantees to the finite TM0 simulator.
`CallingConvention.Realizes.tm0_output` also supports standalone binary output
for any standard routine, charging simulation, extraction, erasure, and startup.
`StandardGaussJordanColumn` shares arguments and the selected candidate between
search and pivot calls. Search and the separate next-row increment are verified;
the branch controller uses search's certified found flag. Column initialization
is verified from arbitrary writable contents. The successful branch and both
dispatch paths are verified, including counter capacity, scratch validity, and
the unchanged tapes on the sentinel path.
`StandardGaussJordanColumn.workspace` prepares all writable column tapes without
matrix lookup or dimension hypotheses, including when there are zero columns.
`TableTraversal` exports the binary traversal; its old marker controller has
been removed.
`StandardCopy.slice_runs` and `CallingConvention.Runs.regions` certify transfers
inside larger regions.
`EncodedDomain.arrayOfLength` encodes arrays whose length is any polynomial
size expression; `EncodedDomain.array` is the named-parameter case. The lookup
contract connects indexed access to the machine, with immutable unary sizes
and valid scratch on return. The superseded marker-based scalar, matrix, unary
counter, and Gauss–Jordan controllers and their wrappers have been removed.
The marker-based binary array controllers and packed arithmetic input/output
wrappers have been removed; `ArrayTM0` uses the standard array contracts.
`AddMultiply.contract` composes the standard arithmetic routines, with bound
`m * (6 * n + 14) + 8 * n + 17`. Its old packed-input preparation and growing
word multiplication controllers have been removed. The standard array and
matrix lookup contracts are available.

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
  number and contents are implementation details. Temporary contents need not
  be valid encodings; validity is required at routine boundaries where a value
  is exposed or consumed. Scratch heads also return to their region starts.

No separate output prefill is required: the same routine handles fresh blank
and reused output regions. Execution determines its write extent from the
read-only size tapes, not from existing output contents. For example, nested
unary traversals can write a region of width `K * L * N`. The realization proof
accounts for this work and establishes the exact written width; an encoded
domain need not supply a separately certified executable width evaluator.

## Limits and next steps

- Extend mathematical contracts to lower-level routines and apply the shared
  search rule to pivot search.
- Simplify nested tape names, wiring, and alphabet-compatibility proofs.
- Reuse the external parsing, initialization, simulation, serialization, and
  extraction adapters when adding algorithms.
- Add quotient production, signed arithmetic, and the remaining bit arithmetic
  for integer matrices. Extend polynomial reparameterization of subprogram
  calls.

Recursive domain syntax, a general size-expression evaluator,
the SMP targets, and Smith normal form remain future work.

Build from the repository root with `lake build Polytime2`, and use `import
Polytime2`. See [GOAL.md](../GOAL.md) for the shared specification and
[EXAMPLES.md](../EXAMPLES.md) for target algorithms and building-block
libraries.
