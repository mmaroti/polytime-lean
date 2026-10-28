# Bounded-machine circuit construction

[Complexity guide](../README.md) · [Hardness task][task]

This implements step 6 of the CSP hardness task: bounded simulation,
polynomial gate bounds, and certified uniform circuit construction with
canonical word-level input and output. SAT hardness is step 7.

[VerifierCircuit.lean](VerifierCircuit.lean) exports `verifier_circuits`:
every certified polynomial-time word verifier has a polynomial-size circuit
family. Its contract covers every Boolean assignment: invalid letter codes
reject, and accepted assignments encode actual accepted words. This is a
mathematical gate-bound theorem. [UniformVerifier.lean](UniformVerifier.lean)
exports `verifier_circuits_uniform`, which also supplies the certified
constructor. `verifierProgram` uses word length as its sole size parameter;
`verifierProgram_polynomialTime` includes size preparation, execution, and
canonical output serialization.

[AcceptanceFlat.lean](AcceptanceFlat.lean) exports `acceptanceProgram`: the
bounded-configuration acceptance circuit is specified as an ordinary network
and certified in the canonical gate-array/output-coordinate codec.
`acceptanceProgram_polynomialTime` includes canonical unary-size input
preparation, TM0 execution, and encoded output extraction.
[WordProgram.lean](WordProgram.lean) extends construction to the complete
word-input circuit with the same guarantees.
[CheckedWordProgram.lean](CheckedWordProgram.lean) includes letter-code guards
and certifies exact agreement with `checkedWordCircuit`.

The mathematical components are:

- [Circuit semantics](../../Circuit/Basic.lean): constants, NAND gates,
  acyclicity, numbered shared wires, and ordinary Boolean assignments.
- [Expression compilation](../../Circuit/Compile.lean) and
  [layer compilation](../../Circuit/Layer.lean): correctness and exact gate
  counts, preserving earlier wires.
- [Truth tables](../../Circuit/TruthTable.lean) and
  [local dynamics](../../Circuit/Local.lean): fixed-arity local transitions
  have circuits linear in time and configuration width.
  [Unrolling](../../Circuit/Unroll.lean) shares wires across time steps.
- [LocalMachine.lean](LocalMachine.lean): radius-one marked-cell updates
  simulate Mathlib TM0 steps, including absorbing halts. The head moves at
  most one cell per step.
- [Trace.lean](Trace.lean): exact certified word-machine runs agree with the
  local evolution at the full time allowance.
- [Window.lean](Window.lean): a window of radius twice the time allowance
  preserves every possible final head position.
- [CellCircuit.lean](CellCircuit.lean): one-hot encodings turn finite arrays
  of marked cells into fixed-arity Boolean dynamics and bounded circuits.
- [FiniteWindow.lean](FiniteWindow.lean): finite array transitions agree with
  truncated tape evolution, including the finite boundary updates.
- [Acceptance.lean](Acceptance.lean): the final observer returns exactly the
  certified verifier's Boolean answer, including early halts.
- [WordInput.lean](WordInput.lean): a word-input circuit prepares the initial
  marked cells through input references and two constant gates.
- [WordGuard.lean](WordGuard.lean): every Boolean input assignment is checked
  for canonical one-hot letter blocks before acceptance.

[Circuit composition](../../Circuit/Compose.lean) relocates gates and retains
shared references. [Observations](../../Circuit/Observe.lean) and
[input guards](../../Circuit/Guard.lean) append their gates to a single copy
of the simulation. [CellObservation.lean](CellObservation.lean) supplies the
one-hot acceptance observer. Acceptance enumerates reachable head positions
and machine states explicitly, with an exact polynomial observation count.

The uniform constructor has these certified components:

- [Construction.lean](../../Circuit/Construction.lean) emits fixed gate
  templates and finite programs using the existing sum and record codecs.
- [TemplateChoice.lean](../../Circuit/TemplateChoice.lean) dispatches among
  specialization-fixed templates using a runtime finite tag.
- [ExpressionTemplate.lean](../../Circuit/ExpressionTemplate.lean) prepares
  fixed wire offsets and emits an expression template at a runtime base.
  Its value theorem identifies the full gate list with the mathematical
  compiler, using [template relocation][relocation].
- [UniformUnroll.lean](../../Circuit/UniformUnroll.lean) expresses the unrolled
  simulation as directly indexed fixed-size blocks. These equations supply
  the offsets needed for array tabulation.
- [CellProgram.lean](CellProgram.lean) prepares and emits a machine transition
  block from time and cell coordinates. It composes certified block addresses,
  predecessor wires, clamped neighbors, and boundary-template selection.
- [SimulationProgram.lean](SimulationProgram.lean) certifies nested time/cell
  tabulation of those blocks. [SimulationCorrect.lean](SimulationCorrect.lean)
  proves that the complete flattened gate list equals mathematical unrolling.
- [FinalWire.lean](FinalWire.lean) certifies final-layer wire coordinates,
  including zero time. [UniformObserve.lean](../../Circuit/UniformObserve.lean)
  gives the exact prefix/suffix layout of disjunction observers.
- [AcceptanceReferences.lean](AcceptanceReferences.lean) certifies the final
  wire references for the explicit acceptance observations.
- [AcceptanceObserver.lean](AcceptanceObserver.lean) certifies observer
  emission and its exact concatenation with the simulation.
- [SimulationFlat.lean](SimulationFlat.lean) and
  [DisjunctionFlat.lean](../../Circuit/DisjunctionFlat.lean) retain gate order
  while converting constructor blocks to canonical flat arrays.

[WireArithmetic.lean](../../Circuit/WireArithmetic.lean) reuses existing
unsigned arithmetic; the shared coordinate encoding law is in
[Indices.lean](../../Arrays/Indices.lean).

[WireSplice.lean](../../Circuit/WireSplice.lean) certifies input-alias lookup
and fresh-wire relocation for composition. The source and target input counts
may differ in either direction; its value contract is `spliceNames`.
[GateSplice.lean](../../Circuit/GateSplice.lean) applies this operation to both
NAND operands. [SpliceProgram.lean](../../Circuit/SpliceProgram.lean) certifies
the whole gate-array transformation and its exact mathematical gate list.

[WordLetterWire.lean](WordLetterWire.lean) certifies external one-hot letter
references for cells inside the word. [WordCellFlags.lean](WordCellFlags.lean)
certifies word membership and the initial head position in signed tape
coordinates, including empty words and zero time. Their mathematical sizes
are the time allowance and word length.
[WordCellChoice.lean](WordCellChoice.lean) supplies the fixed alphabet table,
which agrees with the constant/letter component of `initialChoices`.
[WordAlias.lean](WordAlias.lean) certifies each actual alias reference directly
from the flags, without a runtime choice codec.
[WordAliases.lean](WordAliases.lean) tabulates and flattens the complete array;
`wordAliases_correct` identifies every reference with the original
mathematical two-constant wiring layer.
[WordCore.lean](WordCore.lean) reuses the acceptance constructor at these
sizes. [WordRelocatedCore.lean](WordRelocatedCore.lean) certifies relocation
through the alias array. Its gate-list theorem identifies the result, after
prepending the two constants, with the entire mathematical `wordCircuit`
program. [WordGateProgram.lean](WordGateProgram.lean) assembles these gates,
using [ConstantGates.lean](../../Circuit/ConstantGates.lean) for the prefix.
[WordProgram.lean](WordProgram.lean) certifies the complete ordinary network,
including its output reference. `wordProgram_polynomialTime` includes
canonical size preparation and serialized circuit output.

[WordGuardLayout.lean](WordGuardLayout.lean) identifies the letter guard's
exact prefix, constant, and reverse-order suffix blocks, using the general
[conjunction layout](../../Circuit/UniformConjunction.lean).
[WordGuardPrefixes.lean](WordGuardPrefixes.lean) certifies the entire prefix
array and its exact compiler gate list.
[WordGuardSuffixes.lean](WordGuardSuffixes.lean) certifies the reverse-order
suffix array; [WordGuardProgram.lean](WordGuardProgram.lean) assembles the
complete predicate, including the empty word's true gate.
[CheckedGuardProgram.lean](CheckedGuardProgram.lean) emits the three predicate
copies and joining templates of the existing selector compiler.
[CheckedWordGates.lean](CheckedWordGates.lean) joins these to the simulation;
its gate list is exactly the mathematical checked-word circuit.

The exponential truth-table factor depends only on the fixed cell alphabet,
never on configuration width. Circuit-size bounds count gates; by themselves
they do not certify construction or serialization time.

Step 7 supplies the certified Tseitin conversion and NP-hardness composition.
The constructor theorem alone does not establish SAT hardness.

[task]: ../../tasks/csp-taylor-hardness.md
[relocation]: ../../Circuit/TemplateRelocation.lean
