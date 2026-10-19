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
import Polytime2.Encoding.PolynomialEvaluator

/-! # Preparing and hiding a polynomial unary width input -/

namespace Polytime2

open MultiTape CallingConvention

-- carrierLevel: mathematical values; tape and state catalogues have universe zero.
universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

namespace EncodedDomain

universe widthParameterLevel
variable {Parameter : Type widthParameterLevel} [Fintype Parameter]

/-- A singleton header encoding the exact value of a fixed polynomial in unary. -/
noncomputable def unaryOfLength (polynomial : MvPolynomial Parameter ℕ) :
    EncodedDomain.{widthParameterLevel, carrierLevel} Parameter where
  Carrier _ := PUnit.{carrierLevel + 1}
  widthPolynomial := polynomial
  encode sizes _ := BitVec.allOnes (MvPolynomial.eval sizes polynomial)
  decode sizes bits := if bits = BitVec.allOnes (MvPolynomial.eval sizes polynomial)
    then some PUnit.unit else none
  decode_encode sizes value := by cases value; simp
  encode_decode sizes bits value valid := by
    split at valid
    next equal => exact equal.symm
    next different => simp at valid

@[simp] theorem encoded_unaryOfLength (polynomial : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) :
    encoded (unaryOfLength polynomial : EncodedDomain.{widthParameterLevel, carrierLevel} Parameter) sizes PUnit.unit =
      CallingConvention.unary (MvPolynomial.eval sizes polynomial) := by
  have equal : (fun index : Fin (MvPolynomial.eval sizes polynomial) =>
      (BitVec.allOnes (MvPolynomial.eval sizes polynomial)).getLsbD index.val) = fun _ => true := by
    funext index; simp [index.isLt]
  simp only [encoded, unaryOfLength, EncodedDomain.ArrayEncoding.bits, equal, List.ofFn_const, CallingConvention.unary]

end EncodedDomain

namespace Computation

/-- Supply a polynomial width as one additional immutable singleton argument. -/
noncomputable def withUnaryWidth (computation : Computation.{carrierLevel} Parameter InputName)
    (polynomial : MvPolynomial Parameter ℕ) : Computation Parameter (InputName ⊕ Unit) where
  inputDomains := Sum.elim computation.inputDomains (fun _ => EncodedDomain.unaryOfLength polynomial)
  outputDomain := computation.outputDomain
  precondition sizes arguments := computation.precondition sizes (fun name => arguments (.inl name))
  compute sizes arguments := computation.compute sizes
    ⟨fun name => arguments.val (.inl name), arguments.property⟩

namespace Realizable

open Internal

set_option maxHeartbeats 800000 in
/-- Compute a polynomial unary header privately before invoking its consumer.
The public computation has no extra input tape or size parameter. -/
theorem withComputedWidth (computation : Computation.{carrierLevel} Parameter InputName)
    (polynomial : MvPolynomial Parameter ℕ)
    (realizable : (computation.withUnaryWidth polynomial).Realizable) : computation.Realizable := by
  classical
  obtain ⟨SourceScratch, finiteSourceScratch, sourceScratchDomains, SourceState, finiteSourceState,
    source, sourceEntry, sourceExit, sourceCertificate⟩ := realizable
  let sourceScratchFiniteInstance := finiteSourceScratch
  let sourceStateFiniteInstance := finiteSourceState
  obtain ⟨EvalScratch, finiteEvalScratch, role, EvalState, finiteEvalState,
    evaluator, evalEntry, evalExit, evalBound, evalHalt, evaluate⟩ :=
    PolynomialEvaluator.computable polynomial
  let evalScratchFiniteInstance := finiteEvalScratch
  let evalStateFiniteInstance := finiteEvalState
  let scratch : EvalScratch ⊕ (Unit ⊕ SourceScratch) → EncodedDomain.{0, carrierLevel} Parameter :=
    Sum.elim (fun name => EncodedDomain.unary (role name))
      (Sum.elim (fun _ => EncodedDomain.unaryOfLength polynomial) sourceScratchDomains)
  let widthTape : TapeName computation (EvalScratch ⊕ (Unit ⊕ SourceScratch)) :=
    scratchTape computation (.inr (.inl ()))
  let evalWiring : PolynomialEvaluator.TapeName Parameter EvalScratch ↪
      TapeName computation (EvalScratch ⊕ (Unit ⊕ SourceScratch)) :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl name) => scratchTape computation (.inl name)
      | .inr (.inr _) => widthTape), by
      intro first second equal
      rcases first with parameter | name | result <;>
        rcases second with parameter' | name' | result' <;> simp_all [widthTape]⟩
  let sourceWiring : TapeName (computation.withUnaryWidth polynomial) SourceScratch ↪
      TapeName computation (EvalScratch ⊕ (Unit ⊕ SourceScratch)) :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl (.inl argument)) => inputTape computation argument
      | .inr (.inl (.inr _)) => widthTape
      | .inr (.inr (.inl _)) => outputTape computation
      | .inr (.inr (.inr name)) => scratchTape computation (.inr (.inr name))), by
      intro first second equal
      rcases first with parameter | argument | result | name <;>
        rcases second with parameter' | argument' | result' | name'
      all_goals first
        | (cases argument <;> cases argument' <;> simp_all [widthTape])
        | (cases argument <;> simp_all [widthTape])
        | (cases argument' <;> simp_all [widthTape])
        | simp_all⟩
  let prepare := wire (Alphabet := Alphabet (TapeName computation (EvalScratch ⊕ (Unit ⊕ SourceScratch))))
    evalWiring evaluator
  let algorithm := MultiTape.sequence prepare (wire sourceWiring source) sourceEntry
  refine ⟨EvalScratch ⊕ (Unit ⊕ SourceScratch), inferInstance, scratch,
    EvalState ⊕ SourceState, inferInstance, algorithm, .inl evalEntry, .inr sourceExit, ?_⟩
  obtain ⟨sourceBound, execute⟩ := Internal.wiredRuns sourceScratchDomains source sourceEntry sourceExit
    sourceCertificate sourceWiring
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_, evalBound + sourceBound + 1, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, wire, sourceCertificate.2.2.1]
  · intro sizes input initial valid represented headers
    let arguments := Internal.arguments computation scratch sizes input
    let width := fun name => (Internal.domains computation scratch name).width sizes
    let readonly : TapeName computation (EvalScratch ⊕ (Unit ⊕ SourceScratch)) → Bool :=
      Internal.readOnly computation
    have evalWidths : ∀ name, width (evalWiring name) =
        PolynomialEvaluator.widths role sizes (MvPolynomial.eval sizes polynomial) name := by
      intro name
      rcases name with parameter | name | result
      · change (EncodedDomain.unary.{0, carrierLevel} parameter).width sizes = sizes parameter
        simp [EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (EncodedDomain.unary.{0, carrierLevel} (role name)).width sizes = sizes (role name)
        simp [EncodedDomain.unary, EncodedDomain.ofCodec]
      · rfl
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := evaluate sizes (fun name => initial (evalWiring name))
      (by intro parameter; exact headers parameter)
      (by intro name; rw [← evalWidths]; exact represented.region (evalWiring name))
    have prepared := prepared.wire evalWiring width readonly evalWidths
      (by intro name premise; rcases name with parameter | name | result <;> exact premise)
      initial (fun _ => 0)
    rw [install_self] at prepared
    have zeroPositions : install evalWiring (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) = fun _ => 0 :=
      install_self evalWiring _
    rw [zeroPositions] at prepared
    let middle := install evalWiring (PolynomialEvaluator.result role sizes (MvPolynomial.eval sizes polynomial)) initial
    have marker : middle widthTape = unary (MvPolynomial.eval sizes polynomial) := by
      exact install_at evalWiring _ initial (.inr (.inr ()))
    let sourceArguments : (computation.withUnaryWidth polynomial).Arguments sizes :=
      fun name => match name with
        | .inl argument => arguments argument
        | .inr _ => PUnit.unit
    have sourceWidths : ∀ name, width (sourceWiring name) =
        (Internal.domains (computation.withUnaryWidth polynomial) sourceScratchDomains name).width sizes := by
      intro name
      rcases name with parameter | argument | result | name
      · rfl
      · cases argument <;> rfl
      · rfl
      · rfl
    obtain ⟨sourceTicks, final, sourceCost, trace, correct, _, _⟩ := execute sizes sourceArguments valid
      width readonly middle sourceWidths
      (by intro name premise; rcases name with parameter | argument | result | name
          · rfl
          · cases argument <;> rfl
          · exact premise
          · exact premise)
      (by intro parameter; exact (prepared.readOnly_tape (.inl parameter) rfl).trans (headers parameter))
      (by intro name; cases name with
          | inl argument =>
            exact (prepared.readOnly_tape (inputTape computation argument) rfl).trans
              (represented.1 (inputTape computation argument) rfl)
          | inr result =>
            cases result
            exact marker.trans (EncodedDomain.encoded_unaryOfLength polynomial sizes).symm)
      (by intro name; exact prepared.region (sourceWiring name) (represented.region (sourceWiring name)))
    have combined := prepared.sequence (wire sourceWiring source) sourceEntry
      (by intro symbols; simp [wire, evalHalt]) trace
    refine ⟨prepareTicks + (sourceTicks + 1),
      (fun _ => computation.compute sizes ⟨arguments, valid⟩), final, ?_, combined, ⟨valid, rfl⟩, ?_⟩
    · simp only [map_add, map_one]
      omega
    · intro name; cases name
      exact correct

end Realizable
end Computation
end Polytime2
