# Standalone Turing-machine export

[Project guide](../README.md) · [Source convention](../Machine/README.md)

Start with [Computation.lean](Computation.lean). Apply
`Computation.Realizable.tm0` to an existing realization to obtain
`Computation.TM0Realizable`. One finite machine and one polynomial work for all
public sizes and admissible inputs. Input preparation, simulation, output
extraction, and startup are included in the bound.

## External input and output

`Computation.serialize` uses a specialization-fixed ordering of size parameters
followed by ordinary arguments. Sizes use unary blocks; arguments use their
canonical domain encodings. Five nonblank letters represent binary zero, binary
one, a separator, and framing delimiters:

```text
begin # size_1 # ... # size_s # input_1 # ... # input_m # end
```

Empty blocks retain their separators. With no sizes or arguments, input is
`begin # end`. The final tape contains only the canonical result bits, with all
other cells blank and the head at the result's start. Empty output leaves a
blank tape. The exact serialization and realization predicates live in
[Computation.lean](Computation.lean).

See [Examples/TM0.lean](../Examples/TM0.lean) for public export examples and
[Examples/Integers.lean](../Examples/Integers.lean) for arithmetic certificates.
The [complexity guide](../Complexity/README.md) explains the bridge from these
exports to word-length polynomial bounds and total many-one reductions.

## Backend layers

| Layer | Source |
| --- | --- |
| Delimited public input preparation | [DelimitedInput.lean][input] |
| Arbitrary word preparation | [RawInput.lean](RawInput.lean) |
| Word symbols as immutable input tracks | [WordBits.lean](WordBits.lean) |
| Complete convention-level wrapper | [CallingConventionDelimited.lean][wrap] |
| Physical binary output extraction | [CallingConventionOutput.lean][output] |
| Source convention to simulator | [CallingConventionSimulation.lean][conv] |
| Multi-tape simulation and polynomial bounds | [Simulation.lean][sim] |
| Track representations and serialization | [Tracks.lean][tracks], [encoding] |
| Direct translation of one-tape routines | [SingleTape.lean](SingleTape.lean) |
| Word-machine transport and sequencing | [WordComposition.lean][words] |

[input]: DelimitedInput.lean
[wrap]: CallingConventionDelimited.lean
[output]: CallingConventionOutput.lean
[conv]: CallingConventionSimulation.lean
[sim]: Simulation.lean
[tracks]: Tracks.lean
[encoding]: Encoding.lean
[words]: WordComposition.lean

Lower-level `CallingConvention.Realizes.tm0` retains simulator track frames;
`tm0_output` extracts a declared output. Both start from prepared simulator
storage. `tm0_delimited` adds ordinary input preparation. Application proofs
should use the computation-level export rather than prepare tracks themselves.

`TrackOutput.Symbolic` extracts any contiguous word of nonblank source symbols
with finite formatter memory. `TrackOutput.Stateful` specializes this to binary
symbols, and stateless binary extraction uses unit memory. All share the same
linear bound, frame erasure, and head-restoration proof. Symbol-level extraction
supports the decoded native letters needed by variable-length word output.
The [word export rules](../Complexity/WordArrays.lean) keep that controller and
the simulator representation out of application proofs.
[BlockDecoder.lean](BlockDecoder.lean) reuses the fixed-width reader and head
movement to decode accepted blocks into actual native symbols until a rejected
sentinel. Its whole-stream trace includes a linear input-length bound and
output-head restoration. [NativeTrackOutput.lean](NativeTrackOutput.lean)
extracts that native tape from simulator rows with the shared erasure bound.
[Complexity/BlockDecode.lean](../Complexity/BlockDecode.lean) composes the
standalone decoder. The [coded-stream rules](../Complexity/README.md) connect
computed results to exact native words without exposing simulator storage.

Sweeps, selected head-marker moves, interval extension, and action dispatch
are certified separately in their source modules. Their markers, padding, and
workspace sizes are backend implementation details. Exact transition costs and
preservation obligations belong in those module contracts.

The mathematical local simulation in [LocalMachine.lean](LocalMachine.lean),
[Window.lean](Window.lean), and [FiniteWindow.lean](FiniteWindow.lean) is shared
with Cook–Levin. [LocalComputation.lean](LocalComputation.lean) certifies its
finite-array transition directly through shifts and finite tables.
