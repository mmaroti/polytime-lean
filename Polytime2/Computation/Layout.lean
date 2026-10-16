/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Computation.Realizable

/-! # Internal transport from existing finite tape layouts

This adapter belongs to foundational realization proofs. Application proofs
must reuse `Computation.Realizable` through its mathematical construction rules.
-/

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

-- carrierLevel: mathematical values; source tapes and controllers are finite types.
universe carrierLevel
variable {Parameter InputName SourceTape State ScratchName : Type}
variable [Fintype Parameter] [Fintype InputName] [Fintype SourceTape]
variable [Fintype State] [Fintype ScratchName]

/-- Pull mathematical inputs back along a static, domain-compatible layout. -/
def pullInputs (computation : Computation.{carrierLevel} Parameter InputName)
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool)
    (layout : SourceTape ↪ TapeName computation ScratchName)
    (values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      (sourceDomains name).Carrier sizes)
    (readonly : ∀ name, sourceReadOnly name = readOnly computation (layout name))
    (sizes : Parameter → ℕ)
    (input : Inputs (domains computation scratchDomains) (readOnly computation) sizes) :
    Inputs sourceDomains sourceReadOnly sizes :=
  fun name => values name.val sizes
    (input ⟨layout name.val, (readonly name.val).symm.trans name.property⟩)

/-- An injective layout and carrier equivalences package a primitive without
exporting its machine or scratch names. Unused caller scratch stays arbitrary. -/
theorem ofLayout {SourceOutputName : Type} (computation : Computation.{carrierLevel} Parameter InputName)
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (sourceSizes : Parameter ↪ SourceTape)
    (sourceOutputTapes : SourceOutputName ↪ SourceTape)
    (machine : Machine (Alphabet SourceTape) State) (entry exit : State)
    (sourceHypothesis : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes → Prop)
    (sourceContract : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes →
      Outputs sourceDomains sourceOutputTapes sizes → Prop)
    (certificate : CallingConvention.Realizes sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
      machine entry exit sourceHypothesis sourceContract)
    (layout : SourceTape ↪ TapeName computation ScratchName)
    (values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      (sourceDomains name).Carrier sizes)
    (widths : ∀ name sizes, (domains computation scratchDomains (layout name)).width sizes =
      (sourceDomains name).width sizes)
    (encodings : ∀ name sizes value,
      encoded (domains computation scratchDomains (layout name)) sizes value =
        encoded (sourceDomains name) sizes (values name sizes value))
    (readonly : ∀ name, sourceReadOnly name = readOnly computation (layout name))
    (sizeLayout : ∀ parameter, layout (sourceSizes parameter) = .inl parameter)
    (resultName : SourceOutputName)
    (resultLayout : layout (sourceOutputTapes resultName) = outputTape computation)
    (valid : ∀ sizes input,
      computation.precondition sizes (arguments computation scratchDomains sizes input) →
      sourceHypothesis sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input))
    (correct : ∀ sizes input (good : computation.precondition sizes
        (arguments computation scratchDomains sizes input)) output,
      sourceContract sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input) output →
      encoded (sourceDomains (sourceOutputTapes resultName)) sizes (output resultName) =
        encoded computation.outputDomain sizes
          (computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩)) :
    computation.Realizable := by
  classical
  refine ⟨ScratchName, inferInstance, scratchDomains, State, inferInstance,
    MultiTape.wire (Alphabet := Alphabet (TapeName computation ScratchName)) layout
      machine, entry, exit, ?_⟩
  obtain ⟨bound, execute⟩ := certificate.wired_runs layout
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [MultiTape.wire, certificate.2.2.1]), bound, ?_⟩
  intro sizes input initial good represented headers
  let localInput := pullInputs computation scratchDomains sourceDomains sourceReadOnly
    layout values readonly sizes input
  obtain ⟨ticks, sourceOutput, final, cost, trace, result, canonical, outside, immutable⟩ :=
    execute sizes localInput (fun name => (domains computation scratchDomains name).width sizes)
      (readOnly computation) initial (fun name => widths name sizes)
      (fun name premise => (readonly name).trans premise) (valid sizes input good)
      (by
        intro name immutable
        exact (represented.1 (layout name) ((readonly name).symm.trans immutable)).trans
          (encodings name sizes (input ⟨layout name, (readonly name).symm.trans immutable⟩)))
      (by intro name writable; exact represented.region (layout name))
      (by
        intro parameter
        change initial (layout (sourceSizes parameter)) = unary (sizes parameter)
        rw [sizeLayout]
        exact headers parameter)
  have resultEq : final (outputTape computation) = encoded computation.outputDomain sizes
      (computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩) := by
    rw [← resultLayout]
    exact (canonical resultName).trans (correct sizes input good sourceOutput result)
  let output : Outputs (domains computation scratchDomains)
      (outputTapes computation ScratchName) sizes :=
    fun _ => computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩
  refine ⟨ticks, output, final, cost, trace, ⟨good, rfl⟩, ?_⟩
  intro name
  cases name
  exact resultEq

end Polytime2.Computation.Realizable.Internal
