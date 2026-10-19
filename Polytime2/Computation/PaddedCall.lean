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

import Polytime2.Computation.ComputedSizeRun
import Polytime2.Encoding.BoundedEvaluation
import Polytime2.Primitives.PaddedCopy

/-! # Runtime-sized calls between polynomial-capacity buffers

The headers contain actual callee sizes. Width evaluation, exact argument
extraction, callee execution, and result padding form one fixed private routine.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention EncodedDomain

variable {Parameter NewParameter : Type} [Fintype NewParameter]

abbrev PaddedCallTape (NewParameter Scratch : Type) := NewParameter ⊕ (Fin 3 ⊕ Scratch)

noncomputable def paddedCallWidths (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (inputCapacity outputCapacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (capacity : ℕ) {Scratch : Type} : PaddedCallTape NewParameter Scratch → ℕ
  | .inl parameter => MvPolynomial.eval sizes (bounds parameter)
  | .inr (.inl name) => if name = 1 then MvPolynomial.eval sizes inputCapacity
      else MvPolynomial.eval sizes outputCapacity
  | .inr (.inr _) => capacity

def paddedCallReadOnly {Scratch : Type} : PaddedCallTape NewParameter Scratch → Bool
  | .inl _ => true
  | .inr (.inl name) => decide (name ≠ 2)
  | .inr (.inr _) => false

/-- Compile a unary callee into a routine on padded buffers. The caller supplies
fresh private storage; its immutable actual-size headers need no delimiters. -/
theorem preparesPaddedCall (computation : Computation NewParameter Unit)
    (realizable : computation.Realizable) (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    ∃ (Scratch : Type) (_finiteScratch : Fintype Scratch)
      (State : Type) (_finiteState : Fintype State)
      (machine : Machine (Alphabet (PaddedCallTape NewParameter Scratch)) State)
      (entry exit : State) (capacityBound runtimeBound : MvPolynomial Parameter ℕ),
      (∀ symbols, machine exit symbols = none) ∧
      ∀ (sizes : Parameter → ℕ) (actual : NewParameter → ℕ)
        (_bounded : ∀ parameter, actual parameter ≤ MvPolynomial.eval sizes (bounds parameter))
        (arguments : computation.Arguments actual) (valid : computation.precondition actual arguments)
        (capacity : ℕ) (_fits : MvPolynomial.eval sizes capacityBound ≤ capacity)
        (initial : Tapes (Alphabet (PaddedCallTape NewParameter Scratch))),
        (∀ parameter, initial (.inl parameter) = unary (actual parameter)) →
        initial (.inr (.inl 0)) = unary (MvPolynomial.eval sizes
          (SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial)) →
        initial (.inr (.inl 1)) = buffer (Binary.word (ArrayEncoding.bits
          (((computation.inputDomains ()).encode actual (arguments ())).setWidth
            (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds
              (computation.inputDomains ()).widthPolynomial))))) →
        (∀ name, initial (.inr (.inr name)) = buffer []) →
        (∀ name, Region (paddedCallWidths bounds
          (SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial)
          (SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial)
          sizes capacity name) 0 (initial name)) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval sizes runtimeBound ∧
          Runs (paddedCallWidths bounds
            (SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial)
            (SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial) sizes capacity)
            paddedCallReadOnly machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
          final (.inr (.inl 2)) = buffer (Binary.word (ArrayEncoding.bits
            ((computation.outputDomain.encode actual (computation.compute actual ⟨arguments, valid⟩)).setWidth
              (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds
                computation.outputDomain.widthPolynomial))))) := by
  classical
  obtain ⟨SourceScratch, sourceScratchFinite, sourceScratchDomains, SourceState, sourceStateFinite,
    source, sourceEntry, sourceExit, sourceCertificate⟩ := realizable
  let _sourceScratchFinite := sourceScratchFinite
  let _sourceStateFinite := sourceStateFinite
  obtain ⟨InputScratch, inputScratchFinite, inputRole, InputState, inputStateFinite, inputMachine,
    inputEntry, inputExit, inputBound, inputHalt, evaluateInput⟩ :=
    PolynomialEvaluator.computable_bounded (computation.inputDomains ()).widthPolynomial bounds
  let _inputScratchFinite := inputScratchFinite
  let _inputStateFinite := inputStateFinite
  obtain ⟨OutputScratch, outputScratchFinite, outputRole, OutputState, outputStateFinite, outputMachine,
    outputEntry, outputExit, outputBound, outputHalt, evaluateOutput⟩ :=
    PolynomialEvaluator.computable_bounded computation.outputDomain.widthPolynomial bounds
  let _outputScratchFinite := outputScratchFinite
  let _outputStateFinite := outputStateFinite
  let Scratch := (InputScratch ⊕ OutputScratch) ⊕ (SourceScratch ⊕ Fin 4)
  let Tape := PaddedCallTape NewParameter Scratch
  let privateTape (name : Scratch) : Tape := .inr (.inr name)
  let slot (name : Fin 4) : Tape := privateTape (.inr (.inr name))
  let tag : Tape → ℕ
    | .inl _ => 0
    | .inr (.inl name) => 1 + name.val
    | .inr (.inr (.inl (.inl _))) => 4
    | .inr (.inr (.inl (.inr _))) => 5
    | .inr (.inr (.inr (.inl _))) => 6
    | .inr (.inr (.inr (.inr name))) => 7 + name.val
  have slot_ne {first second : Fin 4} (different : first ≠ second) : slot first ≠ slot second := by
    intro equal
    have values := congrArg tag equal
    apply different
    apply Fin.ext
    dsimp [tag, slot, privateTape] at values
    omega
  have scratch_ne (name : SourceScratch) (index : Fin 4) :
      privateTape (.inr (.inl name)) ≠ slot index := by
    intro equal
    have values := congrArg tag equal
    dsimp [tag, slot, privateTape] at values
    omega
  let inputWiring : PolynomialEvaluator.TapeName NewParameter InputScratch ↪ Tape :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl name) => privateTape (.inl (.inl name))
      | .inr (.inr _) => slot 0), by
      intro first second equal
      rcases first with parameter | temporary | result <;>
        rcases second with parameter' | temporary' | result'
      all_goals first
        | (cases result; cases result'; rfl)
        | (cases equal <;> rfl)⟩
  let outputWiring : PolynomialEvaluator.TapeName NewParameter OutputScratch ↪ Tape :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl name) => privateTape (.inl (.inr name))
      | .inr (.inr _) => slot 1), by
      intro first second equal
      rcases first with parameter | temporary | result <;>
        rcases second with parameter' | temporary' | result'
      all_goals first
        | (cases result; cases result'; rfl)
        | (cases equal <;> rfl)⟩
  let sourceWiring : TapeName computation SourceScratch ↪ Tape :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => slot 2
      | .inr (.inr (.inl _)) => slot 3
      | .inr (.inr (.inr name)) => privateTape (.inr (.inl name))), by
      intro first second equal
      rcases first with parameter | argument | result | temporary <;>
        rcases second with parameter' | argument' | result' | temporary'
      all_goals first
        | (cases argument; cases argument'; rfl)
        | (cases result; cases result'; rfl)
        | (cases equal <;> rfl)⟩
  let copyWiring : Fin 3 ↪ Tape :=
    ⟨![slot 0, .inr (.inl 1), slot 2], by
      intro first second equal
      fin_cases first <;> fin_cases second
      all_goals first
        | rfl
        | (have values := congrArg tag equal
           norm_num [tag, slot, privateTape] at values)⟩
  let padWiring : Fin 4 ↪ Tape :=
    ⟨![.inr (.inl 0), slot 1, slot 3, .inr (.inl 2)], by
      intro first second equal
      fin_cases first <;> fin_cases second
      all_goals first
        | rfl
        | (have values := congrArg tag equal
           norm_num [tag, slot, privateTape] at values)⟩
  let evaluateIn : Machine (Alphabet Tape) InputState := MultiTape.wire inputWiring inputMachine
  let evaluateOut : Machine (Alphabet Tape) OutputState := MultiTape.wire outputWiring outputMachine
  let evaluate := MultiTape.sequence evaluateIn evaluateOut outputEntry
  let prepare := MultiTape.sequence evaluate (PrefixCopy.machine copyWiring) 0
  let call := MultiTape.sequence prepare (MultiTape.wire sourceWiring source) sourceEntry
  let algorithm := MultiTape.sequence call (PaddedCopy.machine padWiring) (.inl (.inl ()))
  obtain ⟨sourceBound, execute⟩ := boundedWiredRuns sourceScratchDomains source sourceEntry sourceExit
    sourceCertificate sourceWiring bounds
  let inputCapacity := SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial
  let outputCapacity := SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial
  let maximum := (∑ parameter, bounds parameter) + inputCapacity + outputCapacity +
    ∑ name, SizeSubstitution.polynomial bounds (sourceScratchDomains name).widthPolynomial
  refine ⟨Scratch, inferInstance, _, inferInstance, algorithm,
    .inl (.inl (.inl (.inl inputEntry))), .inr (.inr 3), maximum,
    inputBound + outputBound + sourceBound + 3 * inputCapacity + 5 * outputCapacity + 13, ?_, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, PaddedCopy.machine, PrefixCopy.machine, MultiTape.wire, UnaryCopy.machine]
  intro sizes actual bounded arguments valid capacity fits initial headers capacityHeader inputPadded fresh regions
  let width : Tape → ℕ := paddedCallWidths bounds inputCapacity outputCapacity sizes capacity
  let readonly : Tape → Bool := paddedCallReadOnly
  have parameterFits (parameter) : actual parameter ≤ capacity := by
    have small := Finset.single_le_sum (fun other _ => Nat.zero_le (MvPolynomial.eval sizes (bounds other)))
      (Finset.mem_univ parameter)
    have cap : (∑ other, MvPolynomial.eval sizes (bounds other)) ≤ capacity := by
      simpa only [maximum, map_add, map_sum] using
        (show MvPolynomial.eval sizes (∑ other, bounds other) ≤ MvPolynomial.eval sizes maximum by
          simp only [maximum, map_add]; omega).trans fits
    exact (bounded parameter).trans (small.trans cap)
  have inputFits : (computation.inputDomains ()).width actual ≤ MvPolynomial.eval sizes inputCapacity :=
    SizeSubstitution.eval_le bounds _ sizes actual bounded
  have outputFits : computation.outputDomain.width actual ≤ MvPolynomial.eval sizes outputCapacity :=
    SizeSubstitution.eval_le bounds _ sizes actual bounded
  have inputCapacityFits : MvPolynomial.eval sizes inputCapacity ≤ capacity := by
    simp only [maximum, map_add] at fits
    omega
  have outputCapacityFits : MvPolynomial.eval sizes outputCapacity ≤ capacity := by
    simp only [maximum, map_add] at fits
    omega
  have inputWidths : ∀ name,
      PolynomialEvaluator.widths inputRole actual ((computation.inputDomains ()).width actual) name ≤
        width (inputWiring name) := by
    rintro (parameter | temporary | result)
    · exact bounded parameter
    · exact parameterFits (inputRole temporary)
    · exact inputFits.trans inputCapacityFits
  have outputWidths : ∀ name,
      PolynomialEvaluator.widths outputRole actual (computation.outputDomain.width actual) name ≤
        width (outputWiring name) := by
    rintro (parameter | temporary | result)
    · exact bounded parameter
    · exact parameterFits (outputRole temporary)
    · exact outputFits.trans outputCapacityFits
  obtain ⟨inputTicks, afterInput, inputCost, inputTrace, inputReady, inputOutside⟩ :=
    evaluateInput inputWiring sizes actual bounded width readonly initial inputWidths
      (by rintro (parameter | temporary | result) premise; rfl; contradiction; contradiction)
      headers (by
        rintro (parameter | temporary | result)
        · change Region (actual parameter) 0 (initial (.inl parameter))
          rw [headers]
          have region := encoded_region (EncodedDomain.unary parameter : EncodedDomain.{0, 0} NewParameter) actual PUnit.unit
          rw [encoded_unary] at region
          simpa [EncodedDomain.unary, EncodedDomain.ofCodec] using region
        · change Region _ 0 (initial (privateTape (.inl (.inl temporary))))
          rw [fresh]; exact blank_region _
        · change Region _ 0 (initial (slot 0))
          rw [fresh]; exact blank_region _)
  have inputFresh (name : OutputScratch ⊕ (SourceScratch ⊕ Fin 3)) :
      afterInput (match name with
        | .inl temporary => privateTape (.inl (.inr temporary))
        | .inr (.inl temporary) => privateTape (.inr (.inl temporary))
        | .inr (.inr index) => slot ⟨index.val + 1, by omega⟩) = buffer [] := by
    apply (inputOutside _ ?_).trans
    · rcases name with temporary | temporary | index <;> exact fresh _
    · rintro ⟨role, equal⟩
      have values := congrArg tag equal
      rcases role with parameter | temporary | result <;>
        rcases name with outputTemporary | sourceTemporary | index <;>
        dsimp [tag, inputWiring, privateTape, slot] at values <;> omega
  obtain ⟨outputTicks, afterOutput, outputCost, outputTrace, outputReady, outputOutside⟩ :=
    evaluateOutput outputWiring sizes actual bounded width readonly afterInput outputWidths
      (by rintro (parameter | temporary | result) premise; rfl; contradiction; contradiction)
      (fun parameter => (inputTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter)) (by
        rintro (parameter | temporary | result)
        · change Region (actual parameter) 0 (afterInput (.inl parameter))
          rw [(inputTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter)]
          have region := encoded_region (EncodedDomain.unary parameter : EncodedDomain.{0, 0} NewParameter) actual PUnit.unit
          rw [encoded_unary] at region
          simpa [EncodedDomain.unary, EncodedDomain.ofCodec] using region
        · change Region _ 0 (afterInput (privateTape (.inl (.inr temporary))))
          rw [inputFresh (.inl temporary)]; exact blank_region _
        · change Region _ 0 (afterInput (slot 1))
          have blank : afterInput (slot 1) = buffer [] := inputFresh (.inr (.inr 0))
          rw [blank]; exact blank_region _)
  have afterEvaluation := inputTrace.sequence evaluateOut outputEntry
    (by intro symbols; simp [MultiTape.wire, inputHalt]) outputTrace
  have bodyFresh (name : SourceScratch ⊕ Fin 2) :
      afterOutput (match name with
        | .inl temporary => privateTape (.inr (.inl temporary))
        | .inr index => slot ⟨index.val + 2, by omega⟩) = buffer [] := by
    apply (outputOutside _ ?_).trans
    · cases name with
      | inl temporary => exact inputFresh (.inr (.inl temporary))
      | inr index => exact inputFresh (.inr (.inr ⟨index.val + 1, by omega⟩))
    · rintro ⟨role, equal⟩
      have values := congrArg tag equal
      rcases role with parameter | temporary | result <;> cases name <;>
        dsimp [tag, outputWiring, privateTape, slot] at values <;> omega
  have inputLength : afterOutput (slot 0) = unary ((computation.inputDomains ()).width actual) := by
    apply (outputOutside (slot 0) ?_).trans (inputReady (.inr (.inr ())))
    rintro ⟨role, equal⟩
    have values := congrArg tag equal
    rcases role with parameter | temporary | result <;>
      norm_num [tag, outputWiring, privateTape, slot] at values
  have outputLength : afterOutput (slot 1) = unary (computation.outputDomain.width actual) :=
    outputReady (.inr (.inr ()))
  have payloadReady : afterOutput (.inr (.inl 1)) = initial (.inr (.inl 1)) :=
    afterEvaluation.readOnly_tape _ (by simp [readonly, paddedCallReadOnly])
  have prefixTrace := PaddedCopy.prefix_runs copyWiring width readonly rfl
    ((computation.inputDomains ()).encode actual (arguments ())) inputFits (inputFits.trans inputCapacityFits)
    afterOutput inputLength (payloadReady.trans inputPadded) (bodyFresh (.inr 0))
  let beforeCall := Function.update afterOutput (slot 2)
    (encoded (computation.inputDomains ()) actual (arguments ()))
  have prepared := afterEvaluation.sequence (PrefixCopy.machine copyWiring) 0
    (by intro symbols; simp [MultiTape.sequence, evaluateOut, MultiTape.wire, outputHalt]) prefixTrace
  have sourceWidths : ∀ name, (domains computation sourceScratchDomains name).width actual ≤
      width (sourceWiring name) := by
    rintro (parameter | argument | result | temporary)
    · simpa [domains, EncodedDomain.unary, EncodedDomain.ofCodec, width, paddedCallWidths, sourceWiring] using bounded parameter
    · cases argument; exact inputFits.trans inputCapacityFits
    · exact outputFits.trans outputCapacityFits
    · change (sourceScratchDomains temporary).width actual ≤ capacity
      have small := Finset.single_le_sum (fun other _ => Nat.zero_le
        (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds (sourceScratchDomains other).widthPolynomial)))
        (Finset.mem_univ temporary)
      have cap : MvPolynomial.eval sizes (∑ name,
          SizeSubstitution.polynomial bounds (sourceScratchDomains name).widthPolynomial) ≤ capacity := by
        simp only [maximum, map_add] at fits
        omega
      exact (SizeSubstitution.eval_le bounds _ sizes actual bounded).trans
        (small.trans (by simpa only [map_sum] using cap))
  obtain ⟨sourceTicks, afterCall, sourceCost, sourceTrace, sourceReady, sourceOutside, sourcePreserved⟩ :=
    execute sizes actual bounded arguments valid width readonly beforeCall sourceWidths
      (by rintro (parameter | argument | result | temporary) premise; rfl; contradiction; contradiction; contradiction)
      (fun parameter => (prepared.readOnly_tape (.inl parameter) rfl).trans (headers parameter))
      (by intro name; cases name; exact Function.update_self _ _ _)
      (by
        rintro (parameter | argument | result | temporary)
        · change Region ((EncodedDomain.unary parameter : EncodedDomain.{0, 0} NewParameter).width actual)
            0 (beforeCall (.inl parameter))
          have currentHeader : beforeCall (.inl parameter) = unary (actual parameter) :=
            (prepared.readOnly_tape (.inl parameter) rfl).trans (headers parameter)
          rw [currentHeader]
          have region := encoded_region (EncodedDomain.unary parameter : EncodedDomain.{0, 0} NewParameter) actual PUnit.unit
          rw [encoded_unary] at region
          simpa [EncodedDomain.unary, EncodedDomain.ofCodec] using region
        · cases argument
          change Region _ 0 (beforeCall (slot 2))
          dsimp only [beforeCall]
          rw [Function.update_self]; exact encoded_region _ _ _
        · change Region _ 0 (beforeCall (slot 3))
          simp only [beforeCall, Function.update_of_ne (show slot 3 ≠ slot 2 from slot_ne (by decide))]
          have blank : afterOutput (slot 3) = buffer [] := bodyFresh (.inr 1)
          rw [blank]; exact blank_region _
        · change Region _ 0 (beforeCall (privateTape (.inr (.inl temporary))))
          simp only [beforeCall, Function.update_of_ne (show privateTape (.inr (.inl temporary)) ≠ slot 2 from scratch_ne temporary 2)]
          have blank : afterOutput (privateTape (.inr (.inl temporary))) = buffer [] := bodyFresh (.inl temporary)
          rw [blank]; exact blank_region _)
  have executed := prepared.sequence (MultiTape.wire sourceWiring source) sourceEntry
    (by intro symbols; simp [MultiTape.sequence, PrefixCopy.machine, MultiTape.wire, UnaryCopy.machine]) sourceTrace
  have finalLength : afterCall (slot 1) = unary (computation.outputDomain.width actual) := by
    apply (sourceOutside _ ?_).trans
    · simpa [beforeCall, Function.update_of_ne (show slot 1 ≠ slot 2 from slot_ne (by decide))] using outputLength
    · rintro ⟨role, equal⟩
      have values := congrArg tag equal
      rcases role with parameter | argument | result | temporary <;>
        norm_num [tag, sourceWiring, slot, privateTape] at values
  have paddingTrace := PaddedCopy.runs padWiring width readonly rfl
    (computation.outputDomain.encode actual (computation.compute actual ⟨arguments, valid⟩))
    outputFits le_rfl afterCall
    ((executed.readOnly_tape (.inr (.inl 0)) (by simp [readonly, paddedCallReadOnly])).trans capacityHeader)
    finalLength sourceReady (executed.region (.inr (.inl 2)) (regions _))
  have combined := executed.sequence (PaddedCopy.machine padWiring) (.inl (.inl ()))
    (by intro symbols; simp [MultiTape.sequence, MultiTape.wire, sourceCertificate.2.2.1]) paddingTrace
  refine ⟨inputTicks + outputTicks + 1 + (3 * (computation.inputDomains ()).width actual + 3) + 1 + sourceTicks + 1 +
    (2 * MvPolynomial.eval sizes outputCapacity + 3 * computation.outputDomain.width actual + 6) + 1,
    _, ?_, combined, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · exact Function.update_self _ _ _

end Polytime2.Computation.Realizable.Internal
