# Execution and calling convention

[Project guide](../README.md) · [Composition](../Computation/README.md)

Read this guide when changing foundational realization proofs. Application
proofs should normally stay at the computation interface.

## Source execution

[Basic.lean](Basic.lean) defines deterministic multi-tape execution over
Mathlib's two-sided tapes. Specialization fixes the finite tapes, controller,
and alphabets; runtime sizes do not change the machine. Each transition reads
all heads, writes symbols, and moves heads left, right, or not at all.

[Complexity.lean](Complexity.lean) supplies polynomial certificates.
[Wiring.lean](Wiring.lean) embeds a routine's tapes injectively into a caller's
workspace and preserves unwired tapes, including heads. Different routines may
share tapes when their contracts agree; one routine cannot alias its own roles.
Controller composition includes the stationary handover transition in its cost.

[Branch.lean](Branch.lean), [While.lean](While.lean), and
[Pipeline.lean](Pipeline.lean) provide control flow.
[Storage.lean](Storage.lean)
bounds storage along execution prefixes. Mathematical loop measures are proof
data, not runtime fuel. Machine relabeling changes alphabet presentations while
preserving execution counts.

## Standard convention

The authoritative definitions are in [CallingConvention.lean][convention];
[CallingConventionRegions.lean][regions] supports region transport.

- Sizes occupy separate immutable unary tapes. Ordinary inputs use their domain
  codecs on separate immutable tapes.
- Outputs use separate writable tapes and do not alias inputs or each other.
  Their initial contents are arbitrary, including blanks.
- Each region has the domain's exact width. Canonical data use binary symbols;
  cells outside the region remain blank throughout execution.
- Every public head starts and finishes at the region's start, including the
  designated blank cell for a zero-width region.
- Outputs are completely overwritten with canonical encodings. Scratch must
  respect its region and restoration obligations but need not decode on return.
  A scratch value needs validity when it becomes a mathematical input or output.

[convention]: CallingConvention.lean
[regions]: CallingConventionRegions.lean

There is no output-prefill obligation. Region preservation and restored heads
allow a caller to reuse a workspace with arbitrary old writable contents.
`Runs.whileValues` tracks live mathematical values without specifying irrelevant
scratch recurrences. `Runs.whileRange`, `Runs.frame`, and `CallFrame` support
bounded traversals and preserved caller context.

## Where to extend the foundation

For copy, scan, initialization, and finite-table building blocks, use the
[primitive guide](../Primitives/README.md). For adapting a contract to a public
computation, use [Layout.lean](../Computation/Layout.lean). Tape placement and
witness handling belong in these foundational proofs, not application proofs.

The [TM0 guide](../TM0/README.md) explains the single-tape backend. Simulator
track markers and framing are private backend data, not source-tape symbols or
public mathematical inputs.
