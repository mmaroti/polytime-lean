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

/-- Reuse a machine unchanged when input maps and computed outputs preserve
canonical words. Widths are separate obligations, including for empty carriers. -/
theorem withEncoding {computation target : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (inputMap : ∀ name sizes,
      (target.inputDomains name).Carrier sizes → (computation.inputDomains name).Carrier sizes)
    (inputWidths : ∀ name sizes,
      (target.inputDomains name).width sizes = (computation.inputDomains name).width sizes)
    (outputWidths : ∀ sizes, target.outputDomain.width sizes = computation.outputDomain.width sizes)
    (inputEncodings : ∀ name sizes value,
      encoded (target.inputDomains name) sizes value =
        encoded (computation.inputDomains name) sizes (inputMap name sizes value))
    (compatible : ∀ sizes arguments, target.precondition sizes arguments →
      computation.precondition sizes (fun name => inputMap name sizes (arguments name)))
    (outputEncodings : ∀ sizes arguments,
      encoded target.outputDomain sizes (target.compute sizes arguments) =
        encoded computation.outputDomain sizes (computation.compute sizes
          ⟨(fun name => inputMap name sizes (arguments.val name)),
            compatible sizes arguments.val arguments.property⟩)) : target.Realizable := by
  classical
  obtain ⟨Scratch, finiteScratch, scratch, State, finiteState, machine, entry, exit, certificate⟩ := realizable
  let scratchFinite := finiteScratch
  let stateFinite := finiteState
  refine ⟨Scratch, finiteScratch, scratch, State, finiteState, machine, entry, exit, ?_⟩
  obtain ⟨sizeReadonly, outputWritable, halt, bound, execute⟩ := certificate
  refine ⟨sizeReadonly, outputWritable, halt, bound, ?_⟩
  intro sizes input initial valid represented headers
  let sourceInput : Inputs (Internal.domains computation scratch) (Internal.readOnly computation) sizes := by
    intro name
    rcases name with ⟨name, immutable⟩
    rcases name with parameter | argument | result | scratchName
    · exact input ⟨.inl parameter, rfl⟩
    · exact inputMap argument sizes (input ⟨.inr (.inl argument), rfl⟩)
    · contradiction
    · contradiction
  have widths (name : Internal.TapeName computation Scratch) :
      (Internal.domains target scratch name).width sizes =
        (Internal.domains computation scratch name).width sizes := by
    rcases name with parameter | argument | result | scratchName
    · rfl
    · exact inputWidths argument sizes
    · exact outputWidths sizes
    · rfl
  have sourceEntry : Entry (Internal.domains computation scratch) (Internal.readOnly computation)
      sizes sourceInput initial := by
    constructor
    · intro name immutable
      rcases name with parameter | argument | result | scratchName
      · exact represented.1 (.inl parameter) rfl
      · exact (represented.1 (.inr (.inl argument)) rfl).trans
          (inputEncodings argument sizes _)
      · contradiction
      · contradiction
    · intro name writable
      obtain ⟨old, length, equal⟩ := represented.2 name writable
      exact ⟨old, length.trans (widths name), equal⟩
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute sizes sourceInput initial
      (compatible sizes (Internal.arguments target scratch sizes input) valid) sourceEntry headers
  have trace := trace.regions (fun name => (Internal.domains target scratch name).width sizes)
    (fun _ => 0) (by intro name writable; rw [widths]; simp)
  simp only [zero_add] at trace
  refine ⟨ticks, (fun _ => target.compute sizes ⟨Internal.arguments target scratch sizes input, valid⟩),
    final, cost, trace, ⟨valid, rfl⟩, ?_⟩
  intro name
  cases name
  have equal := correct.2
  have result := canonical ()
  change final (Internal.outputTape target) = encoded computation.outputDomain sizes (output ()) at result
  rw [equal] at result
  exact result.trans (outputEncodings sizes ⟨Internal.arguments target scratch sizes input, valid⟩).symm


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
  apply realizable.withEncoding (fun name sizes => inputEquivalence name sizes)
    inputWidths outputWidths
    (fun name sizes value => congrArg CallingConvention.tape (inputEncodings name sizes value))
    (by intros; assumption)
  intro sizes arguments
  exact congrArg CallingConvention.tape
    ((outputEncodings sizes _).trans (by simp only [Computation.reindexDomains, Equiv.apply_symm_apply]))

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
  exact realizable.withEncoding (fun _ _ value => value) (by intros; rfl)
    sameWidth (by intros; rfl) (by intros; assumption) sameEncoding

end Realizable
end Polytime2.Computation
