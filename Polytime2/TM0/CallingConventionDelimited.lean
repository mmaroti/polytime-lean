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

import Polytime2.TM0.DelimitedInput
import Polytime2.Encoding.EncodedArray

/-! # Complete TM0 execution from ordinary delimited calling-convention inputs

Input preparation, finite-track simulation, output extraction, and startup are
all charged. Output and scratch tapes begin blank; their domain widths need no
executable evaluators. The public serialization has five distinct letters.
-/

namespace Polytime2.CallingConvention

open MultiTape

-- tapeLevel: source tape roles; parameterLevel: runtime size names;
-- carrierLevel: mathematical inputs and outputs; stateLevel: source controller.
universe tapeLevel parameterLevel carrierLevel stateLevel outputLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName] [Fintype TapeName]
variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {OutputName : Type outputLevel}
variable {State : Type stateLevel} [Fintype State]

/-- Only immutable inputs are serialized; writable tapes are initially blank. -/
def inputBits (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizes : Parameter → ℕ) (input : Inputs domains readOnly sizes)
    (name : TapeName) : List Bool :=
  if immutable : readOnly name = true then
    EncodedDomain.ArrayEncoding.bits ((domains name).encode sizes (input ⟨name, immutable⟩))
  else []

noncomputable def inputTapes (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizes : Parameter → ℕ) (input : Inputs domains readOnly sizes) :
    Tapes (Alphabet TapeName) :=
  fun name => if immutable : readOnly name = true then encoded (domains name) sizes (input ⟨name, immutable⟩)
    else buffer []

omit [DecidableEq TapeName] [Fintype TapeName] in
private theorem input_entry (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizes : Parameter → ℕ) (input : Inputs domains readOnly sizes) :
    Entry domains readOnly sizes input (inputTapes domains readOnly sizes input) := by
  constructor
  · intro name immutable; simp [inputTapes, immutable]
  · intro name writable
    refine ⟨List.replicate ((domains name).width sizes) 0, by simp, ?_⟩
    simp only [inputTapes, writable, Bool.false_eq_true, ↓reduceDIte]
    have blanks := TrackOutput.mk_append_blanks ([] : List Binary.Symbol) ((domains name).width sizes)
    exact congrArg (fun right => Turing.Tape.mk' (Turing.ListBlank.mk ([] : List Binary.Symbol)) right)
      (by simpa using blanks.symm)

omit [Fintype TapeName] in
private theorem input_represents (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizes : Parameter → ℕ) (input : Inputs domains readOnly sizes)
    (names : List TapeName) (unique : names.Nodup)
    (complete : ∀ name, name ∈ names ↔ readOnly name = true) :
    Tracks.Represents (DelimitedInput.rows names (inputBits domains readOnly sizes input))
      (inputTapes domains readOnly sizes input) := by
  have represented := DelimitedInput.represents names unique (inputBits domains readOnly sizes input)
  convert represented using 1
  funext name
  by_cases immutable : readOnly name = true
  · simp [inputTapes, inputBits, immutable, (complete name).mpr immutable,
      encoded, EncodedDomain.ArrayEncoding.bits]
  · have absent : name ∉ names := fun member => immutable ((complete name).mp member)
    simp [inputTapes, immutable, absent]

/-- Complete generic export from delimited public input blocks to a canonical
binary result, starting at `TM0.init`. No simulator frame is supplied by callers. -/
theorem Realizes.tm0_delimited
    {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizeTapes : Parameter ↪ TapeName}
    {outputTapes : OutputName ↪ TapeName}
    {source : Machine (Alphabet TapeName) State} {sourceEntry sourceExit : State}
    {hypothesis : ∀ sizes, Inputs domains readOnly sizes → Prop}
    {contract : ∀ sizes, Inputs domains readOnly sizes → Outputs domains outputTapes sizes → Prop}
    (certificate : Realizes domains readOnly sizeTapes outputTapes source sourceEntry sourceExit hypothesis contract)
    (inputNames : List TapeName) (unique : inputNames.Nodup)
    (complete : ∀ name, name ∈ inputNames ↔ readOnly name = true) (resultName : OutputName) :
    let names := (Finset.univ : Finset TapeName).toList
    let resultTape := outputTapes resultName
    let simulate := MultiTape.sequence (Simulation.machine names source) (extract resultTape) 0
    let combined := MultiTape.sequence (DelimitedInput.machine resultTape inputNames) simulate
      (.inl (Simulation.entry names sourceEntry))
    let program := TM0Input.machine (SingleTape.compile combined) (.inl (.inl (DelimitedInput.entry inputNames)))
    ∃ timeBound : MvPolynomial Parameter ℕ, ∀ sizes input,
      hypothesis sizes input →
      (∀ parameter, encoded (domains (sizeTapes parameter)) sizes
        (input ⟨sizeTapes parameter, certificate.1 parameter⟩) = unary (sizes parameter)) →
      ∃ ticks output,
        ticks ≤ MvPolynomial.eval sizes timeBound ∧ contract sizes input output ∧
        (fun current => current.bind (Turing.TM0.step program))^[ticks]
          (some (Turing.TM0.init (DelimitedInput.serialize (DelimitedInput.letters resultTape)
            (inputNames.map (inputBits domains readOnly sizes input))))) =
          some (TM0Input.embed (SingleTape.configuration (.inr (.inr 7), Sweep.tape []
            (TrackOutput.word (outputLetter resultTape)
              (EncodedDomain.ArrayEncoding.bits ((domains resultTape).encode sizes (output resultName))))))) ∧
        Turing.TM0.step program
          (TM0Input.embed (SingleTape.configuration (.inr (.inr 7), Sweep.tape []
            (TrackOutput.word (outputLetter resultTape)
              (EncodedDomain.ArrayEncoding.bits ((domains resultTape).encode sizes (output resultName))))))) = none := by
  classical
  intro names resultTape simulate combined program
  let precondition := fun sizes initial => ∃ input,
    hypothesis sizes input ∧ Entry domains readOnly sizes input initial ∧
      ∀ parameter, initial (sizeTapes parameter) = unary (sizes parameter)
  let postcondition := fun sizes (initial : Tapes (Alphabet TapeName)) final => ∃ input output,
    hypothesis sizes input ∧ Entry domains readOnly sizes input initial ∧
      contract sizes input output ∧ Exit domains outputTapes sizes output final
  have physical : MultiTape.Internal.Realizes source sourceEntry sourceExit precondition postcondition := by
    obtain ⟨sizeReadOnly, outputsWritable, halted, bound, execute⟩ := certificate
    refine ⟨halted, bound, ?_⟩
    intro sizes initial valid
    obtain ⟨input, validInput, represented, headers⟩ := valid
    obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
      execute sizes input initial validInput represented headers
    exact ⟨ticks, final, cost, trace.steps, input, output, validInput, represented, correct, canonical⟩
  let widthBound := fun name => (domains name).widthPolynomial
  let rowCapacity : MvPolynomial Parameter ℕ := (inputNames.map (fun name => widthBound name + 1)).sum + 1
  obtain ⟨simulationBound, rowBound, executeSimulation⟩ := Simulation.realizes_steps names
    (Finset.nodup_toList _) (by intro name; simp [names]) physical rowCapacity
  refine ⟨2 * (2 * rowCapacity + 3 + simulationBound + 2 * rowBound + 10) + 1, ?_⟩
  intro sizes input valid headers
  let initial := inputTapes domains readOnly sizes input
  let bits := inputBits domains readOnly sizes input
  have represented : Tracks.Represents (DelimitedInput.rows inputNames bits) initial :=
    input_represents domains readOnly sizes input inputNames unique complete
  have validInitial : precondition sizes initial := by
    refine ⟨input, valid, input_entry domains readOnly sizes input, ?_⟩
    intro parameter
    simpa only [initial, inputTapes, certificate.1 parameter, ↓reduceDIte] using headers parameter
  have bitBound (name : TapeName) : (bits name).length ≤ MvPolynomial.eval sizes (widthBound name) := by
    dsimp [bits, inputBits]
    split
    · simp [EncodedDomain.ArrayEncoding.bits, widthBound]
    · simp
  have sumBound (ordered : List TapeName) :
      (ordered.map (fun name => (bits name).length + 1)).sum ≤
        MvPolynomial.eval sizes ((ordered.map (fun name => widthBound name + 1)).sum) := by
    induction ordered with
    | nil => simp
    | cons name rest induction =>
      simp only [List.map_cons, List.sum_cons, map_add, map_one]
      have localBound := bitBound name
      omega
  have rowCost : (DelimitedInput.rawRows resultTape inputNames bits).length ≤
      MvPolynomial.eval sizes rowCapacity := by
    rw [DelimitedInput.rawRows_length]
    have bounded := sumBound inputNames
    simp only [rowCapacity, map_add, map_one]
    omega
  obtain ⟨simulationTicks, finalRows, final, simulationCost, storage, correct, finalRepresentation, simulated⟩ :=
    executeSimulation sizes initial validInitial (DelimitedInput.rows inputNames bits) represented
      (by rw [DelimitedInput.rows_length resultTape]; exact rowCost)
  obtain ⟨originalInput, output, _originalValid, originalEntry, outputCorrect, canonical⟩ := correct
  have sameInput : originalInput = input := by
    funext name
    have old := originalEntry.1 name.val name.property
    have current := (input_entry domains readOnly sizes input).1 name.val name.property
    exact encoded_injective (domains name.val) sizes (old.symm.trans current)
  subst originalInput
  have outputRepresentation := finalRepresentation resultTape
  rw [canonical resultName] at outputRepresentation
  obtain ⟨extractTicks, extractCost, extracted⟩ := extract_runs resultTape (domains resultTape)
    sizes (output resultName) finalRows outputRepresentation
  have computed := MultiTape.sequence_steps (Simulation.machine names source) (extract resultTape) 0
    simulated (by intro symbols; rfl) extracted
  have prepared := DelimitedInput.steps resultTape inputNames bits
  have completeTrace := MultiTape.sequence_steps (DelimitedInput.machine resultTape inputNames) simulate
    (.inl (Simulation.entry names sourceEntry)) prepared
    (DelimitedInput.halt resultTape inputNames) computed
  refine ⟨2 * ((2 * (DelimitedInput.rawRows resultTape inputNames bits).length + 3) +
    (simulationTicks + extractTicks + 1) + 1) + 1, output, ?_, outputCorrect, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one]
    omega
  · rw [DelimitedInput.serialize_eq]
    exact TM0Input.initialized_steps _ _ _ (SingleTape.steps combined completeTrace)
  · apply (TM0Input.step_embed _ _ _).trans
    rw [SingleTape.halt combined _ (by rfl)]
    rfl

end Polytime2.CallingConvention
