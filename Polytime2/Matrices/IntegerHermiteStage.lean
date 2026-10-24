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

import Polytime2.Matrices.HermiteStageController

/-! # Certified interleaved Hermite stage

Given distinct source and incoming rows, a positive source pivot, and an array
of distinct earlier rows excluding both, eliminate the incoming entry and
normalize all earlier entries. The stage prepares its accumulator internally
and returns the actual matrix and left basis in a derived polynomial width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width length : MvPolynomial Parameter ℕ) : Fin 6 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width
  | 5 => (boundedIndex rows).arrayOfLength length

private def allowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 0) (arguments 2) ∧
    (List.ofFn (arguments 5)).Nodup ∧ arguments 0 ∉ List.ofFn (arguments 5) ∧ arguments 1 ∉ List.ofFn (arguments 5)

/-- Eliminate and normalize every supplied earlier row, deriving the workspace internally. -/
noncomputable def integerHermiteRowStage (rows columns width length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) where
  inputDomains := inputs rows columns width length
  outputDomain := hermiteColumnState rows columns (hermiteStageWorkspace width)
  precondition := allowed rows columns width length
  compute sizes arguments :=
    let result := IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
      (List.ofFn (arguments.val 5)) (arguments.val 3).val (arguments.val 4).val
    have bound := IntegerMatrix.hermiteRowStage_bound (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
      (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width) (arguments.val 0) (arguments.val 1)
      arguments.property.1 (arguments.val 2) (List.ofFn (arguments.val 5)) arguments.property.2.2.1
      arguments.property.2.2.2.1 (arguments.val 3).val (arguments.val 4).val arguments.property.2.1
      (fun row => (arguments.val 3).property row (arguments.val 2)) (arguments.val 3).property (arguments.val 4).property
    have capacity : MvPolynomial.eval sizes width + (3 * MvPolynomial.eval sizes width + 3) =
        MvPolynomial.eval sizes (hermiteStageWorkspace width) := by
      simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]
      omega
    (⟨result.1, fun row column => (bound.1 row column).trans_le (pow_le_pow_right₀ (by decide) capacity.le)⟩,
      ⟨result.2, fun row column => (bound.2 row column).trans_le (pow_le_pow_right₀ (by decide) capacity.le)⟩)

private noncomputable def elimination (rows columns width length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) :=
  ((integerHermiteRowStep rows columns width).withArguments (inputs rows columns width length)
    (Fin.castLEEmb (by decide : 5 ≤ 6)) (by intro name; fin_cases name <;> rfl)).withPrecondition
    (allowed rows columns width length) (fun _ _ valid => ⟨valid.1, valid.2.1⟩)

private theorem elimination_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (elimination rows columns width length).Realizable :=
  ((integerHermiteRowStep_realizable rows columns width).withArguments (inputs rows columns width length)
    (Fin.castLEEmb (by decide : 5 ≤ 6)) (by intro name; fin_cases name <;> rfl)).withPrecondition
    (allowed rows columns width length) (fun _ _ valid => ⟨valid.1, valid.2.1⟩)

private noncomputable def controllerArguments (rows columns width length : MvPolynomial Parameter ℕ)
    (name : Fin 3 ⊕ Bool) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStage rows columns width length).Arguments sizes //
      (integerHermiteRowStage rows columns width length).precondition sizes arguments}) :
    ((hermiteStageController rows columns width length).inputDomains name).Carrier sizes :=
  match name with
  | .inl 0 => arguments.val 0
  | .inl 1 => arguments.val 1
  | .inl 2 => arguments.val 2
  | .inr false => (elimination rows columns width length).compute sizes arguments
  | .inr true => arguments.val 5

private theorem controller_permitted (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStage rows columns width length).Arguments sizes //
      (integerHermiteRowStage rows columns width length).precondition sizes arguments}) :
    (hermiteStageController rows columns width length).precondition sizes
      (fun name => controllerArguments rows columns width length name sizes arguments) := by
  refine ⟨arguments.property.2.2.1, arguments.property.2.2.2.1, arguments.property.2.2.2.2,
    (arguments.val 3).val, (arguments.val 4).val, ?_⟩
  exact ⟨arguments.property.1, arguments.property.2.1, (arguments.val 3).property, (arguments.val 4).property, rfl⟩

/-- The complete stage includes preparation, array traversal, normalization, and result storage. -/
theorem integerHermiteRowStage_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStage rows columns width length).Realizable := by
  let computation := integerHermiteRowStage rows columns width length
  have complete := (hermiteStageController_realizable rows columns width length).onResults
    computation.inputDomains computation.precondition (controllerArguments rows columns width length)
    (controller_permitted rows columns width length) (by
      intro name
      rcases name with name | choice
      · fin_cases name
        · exact Realizable.argument computation.inputDomains 0 computation.precondition
        · exact Realizable.argument computation.inputDomains 1 computation.precondition
        · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · cases choice
        · exact elimination_realizable rows columns width length
        · exact Realizable.argument computation.inputDomains 5 computation.precondition)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  have raw := hermiteStageController_correct rows columns width length sizes
    ⟨fun name => controllerArguments rows columns width length name sizes ⟨arguments, valid⟩,
      controller_permitted rows columns width length sizes ⟨arguments, valid⟩⟩
    (arguments 3).val (arguments 4).val
    ⟨valid.1, valid.2.1, (arguments 3).property, (arguments 4).property, rfl⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst raw)) (Subtype.ext (congrArg Prod.snd raw))

/-- The returned ordinary matrices agree exactly with the complete mathematical stage. -/
theorem integerHermiteRowStage_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStage rows columns width length).Arguments sizes //
      (integerHermiteRowStage rows columns width length).precondition sizes arguments}) :
    let result := (integerHermiteRowStage rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (List.ofFn (arguments.val 5))
      (arguments.val 3).val (arguments.val 4).val := rfl

end Polytime2.Computation

