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
import Polytime2.Encoding.EncodedArray

/-! # Changing mathematical domains without changing their encoded bits -/

namespace Polytime2.Computation

open MultiTape CallingConvention

-- carrierLevel: the source and target mathematical values use the same universe.
universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Reinterpret arguments and result through mathematical equivalences.
Realizability additionally requires matching widths and canonical encodings. -/
def reindexDomains (computation : Computation.{carrierLevel} Parameter InputName)
    (inputDomains : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (outputDomain : EncodedDomain.{0, carrierLevel} Parameter)
    (inputEquivalence : ∀ name sizes,
      (inputDomains name).Carrier sizes ≃ (computation.inputDomains name).Carrier sizes)
    (outputEquivalence : ∀ sizes,
      outputDomain.Carrier sizes ≃ computation.outputDomain.Carrier sizes) :
    Computation Parameter InputName where
  inputDomains := inputDomains
  outputDomain := outputDomain
  precondition sizes arguments := computation.precondition sizes
    (fun name => inputEquivalence name sizes (arguments name))
  compute sizes arguments := (outputEquivalence sizes).symm
    (computation.compute sizes
      ⟨(fun name => inputEquivalence name sizes (arguments.val name)), arguments.property⟩)

namespace Realizable

/-- Domain reinterpretation reuses the same hidden realization and polynomial
bound. It neither copies data nor inspects private scratch contents. -/
theorem reindexDomains {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (inputDomains : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (outputDomain : EncodedDomain.{0, carrierLevel} Parameter)
    (inputEquivalence : ∀ name sizes,
      (inputDomains name).Carrier sizes ≃ (computation.inputDomains name).Carrier sizes)
    (outputEquivalence : ∀ sizes,
      outputDomain.Carrier sizes ≃ computation.outputDomain.Carrier sizes)
    (inputWidths : ∀ name sizes,
      (inputDomains name).width sizes = (computation.inputDomains name).width sizes)
    (outputWidths : ∀ sizes, outputDomain.width sizes = computation.outputDomain.width sizes)
    (inputEncodings : ∀ name sizes value,
      EncodedDomain.ArrayEncoding.bits ((inputDomains name).encode sizes value) =
        EncodedDomain.ArrayEncoding.bits ((computation.inputDomains name).encode sizes (inputEquivalence name sizes value)))
    (outputEncodings : ∀ sizes value,
      EncodedDomain.ArrayEncoding.bits (outputDomain.encode sizes value) =
        EncodedDomain.ArrayEncoding.bits (computation.outputDomain.encode sizes (outputEquivalence sizes value))) :
    (computation.reindexDomains inputDomains outputDomain inputEquivalence outputEquivalence).Realizable := by
  classical
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteState,
    machine, entry, exit, certificate⟩ := realizable
  let target := computation.reindexDomains inputDomains outputDomain inputEquivalence outputEquivalence
  let equivalence (name : Internal.TapeName computation ScratchName) sizes :
      (Internal.domains target scratchDomains name).Carrier sizes ≃
        (Internal.domains computation scratchDomains name).Carrier sizes :=
    match name with
    | .inl _ => Equiv.refl _
    | .inr (.inl argument) => inputEquivalence argument sizes
    | .inr (.inr (.inl _)) => outputEquivalence sizes
    | .inr (.inr (.inr _)) => Equiv.refl _
  refine ⟨ScratchName, finiteScratch, scratchDomains, State, finiteState, machine, entry, exit, ?_⟩
  refine CallingConvention.realizes_reindex equivalence ?_ ?_
    (Internal.readOnly computation) (Internal.sizeTapes computation ScratchName)
    (Internal.outputTapes computation ScratchName) machine entry exit _ _ _ _ ?_ ?_ certificate
  · intro name sizes
    rcases name with parameter | argument | result | scratch
    · rfl
    · exact inputWidths argument sizes
    · exact outputWidths sizes
    · rfl
  · intro name sizes value
    rcases name with parameter | argument | result | scratch
    · rfl
    · exact congrArg CallingConvention.tape (inputEncodings argument sizes value)
    · exact congrArg CallingConvention.tape (outputEncodings sizes value)
    · rfl
  · intro sizes input valid
    exact valid
  · intro sizes input output correct
    obtain ⟨valid, correct⟩ := correct
    refine ⟨valid, ?_⟩
    exact congrArg (outputEquivalence sizes).symm correct

/-- Change a computed result's mathematical interpretation when its exact bits
agree. Unlike an equivalence of domains, this also permits proper subdomains. -/
theorem withEncodedOutput {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (outputDomain : EncodedDomain.{0, carrierLevel} Parameter)
    (compute : ∀ sizes, {arguments : computation.Arguments sizes //
      computation.precondition sizes arguments} → outputDomain.Carrier sizes)
    (sameWidth : ∀ sizes, outputDomain.width sizes = computation.outputDomain.width sizes)
    (sameEncoding : ∀ sizes arguments,
      encoded outputDomain sizes (compute sizes arguments) =
        encoded computation.outputDomain sizes (computation.compute sizes arguments)) :
    (Computation.mk computation.inputDomains outputDomain computation.precondition compute).Realizable := by
  classical
  obtain ⟨Scratch, finiteScratch, scratch, State, finiteState, machine, entry, exit, certificate⟩ := realizable
  let scratchFinite := finiteScratch
  let stateFinite := finiteState
  let target := Computation.mk computation.inputDomains outputDomain computation.precondition compute
  refine ⟨Scratch, finiteScratch, scratch, State, finiteState, machine, entry, exit, ?_⟩
  obtain ⟨sizeReadonly, outputWritable, halt, bound, execute⟩ := certificate
  refine ⟨sizeReadonly, outputWritable, halt, bound, ?_⟩
  intro sizes input initial valid represented headers
  let sourceInput : Inputs (Internal.domains computation scratch) (Internal.readOnly computation) sizes := by
    intro name
    rcases name with ⟨name, immutable⟩
    rcases name with parameter | argument | result | scratchName
    · exact input ⟨.inl parameter, rfl⟩
    · exact input ⟨.inr (.inl argument), rfl⟩
    · contradiction
    · contradiction
  have widths (name : Internal.TapeName computation Scratch) :
      (Internal.domains target scratch name).width sizes =
        (Internal.domains computation scratch name).width sizes := by
    rcases name with parameter | argument | result | scratchName <;> first | rfl | exact sameWidth sizes
  have sourceEntry : Entry (Internal.domains computation scratch) (Internal.readOnly computation)
      sizes sourceInput initial := by
    constructor
    · intro name immutable
      rcases name with parameter | argument | result | scratchName
      · exact represented.1 (.inl parameter) rfl
      · exact represented.1 (.inr (.inl argument)) rfl
      · contradiction
      · contradiction
    · intro name writable
      obtain ⟨old, length, equal⟩ := represented.2 name writable
      exact ⟨old, length.trans (widths name), equal⟩
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute sizes sourceInput initial valid sourceEntry headers
  have trace := trace.regions (fun name => (Internal.domains target scratch name).width sizes)
    (fun _ => 0) (by intro name writable; rw [widths]; simp)
  simp only [zero_add] at trace
  refine ⟨ticks, (fun _ => compute sizes ⟨Internal.arguments target scratch sizes input, valid⟩),
    final, cost, trace, ⟨valid, rfl⟩, ?_⟩
  intro name
  cases name
  have equal := correct.2
  have result := canonical ()
  change final (Internal.outputTape target) = encoded computation.outputDomain sizes (output ()) at result
  rw [equal] at result
  exact result.trans (sameEncoding sizes ⟨Internal.arguments target scratch sizes input, valid⟩).symm

end Realizable
end Polytime2.Computation
