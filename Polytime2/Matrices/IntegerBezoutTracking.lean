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

import Polytime2.Matrices.IntegerBezout
import Polytime2.Matrices.IntegerPairTranspose
import Polytime2.Matrices.BezoutTrackingMath

/-! # Certified Bézout elimination with an accumulated left transformation

Inputs are a bounded current matrix, a bounded square left transformation, two
distinct rows, and a selected column. One coefficient result, computed from the
current matrix, is retained and applied to both matrices. Column elimination
reuses this construction through transposition, accumulating the right basis.
The sufficient output
width `4*w+3` is derived internally. Unimodularity is preserved when the supplied
left transformation is unimodular; it is not needed to execute the operation.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def trackingInputs (rows columns width : MvPolynomial Parameter ℕ) :
    Fin 5 → EncodedDomain Parameter := fun name => match name with
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width

private def originalSelection : Fin 4 ↪ Fin 5 :=
  ⟨(fun name => match name with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

private def applicationSelection (left : Bool) : Fin 4 ↪ Fin 5 ⊕ Unit :=
  ⟨(fun name => match name with
    | 0 => .inl 0 | 1 => .inl 1 | 2 => .inr () | 3 => .inl (if left then 4 else 3)), by
    intro first second equal
    cases left <;> fin_cases first <;> fin_cases second <;> simp_all⟩

private noncomputable def trackingApplication (rows columns width : MvPolynomial Parameter ℕ)
    (left : Bool) :=
  (Realizable.Internal.BezoutRows.application rows (if left then rows else columns) width).withArguments
    (Sum.elim (trackingInputs rows columns width)
      (fun _ : Unit => Realizable.Internal.BezoutCoefficients.domain width))
    (applicationSelection left) (by intro name; cases left <;> fin_cases name <;> rfl)

private theorem trackingApplication_realizable (rows columns width : MvPolynomial Parameter ℕ)
    (left : Bool) : (trackingApplication rows columns width left).Realizable :=
  (Realizable.Internal.BezoutRows.application_realizable rows (if left then rows else columns) width).withArguments
    _ (applicationSelection left) (by intro name; cases left <;> fin_cases name <;> rfl)

/-- Eliminate a column entry and return both the current matrix and its updated left basis. -/
noncomputable def integerBezoutRowsWithLeft (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) where
  inputDomains := trackingInputs rows columns width
  outputDomain := (integerMatrices rows columns (2 * (2 * width + 1) + 1)).prod
    (integerMatrices rows rows (2 * (2 * width + 1) + 1))
  precondition _ arguments := arguments 0 ≠ arguments 1
  compute sizes arguments :=
    let coefficients := (Realizable.Internal.BezoutRows.coefficients rows columns width).compute sizes
      ⟨(fun name => match name with
        | 0 => arguments.val 0 | 1 => arguments.val 1 | 2 => arguments.val 2 | 3 => arguments.val 3), trivial⟩
    let host : ∀ name, ((trackingApplication rows columns width false).inputDomains name).Carrier sizes :=
      fun name => match name with | .inl original => arguments.val original | .inr _ => coefficients
    ((trackingApplication rows columns width false).compute sizes ⟨host, arguments.property⟩,
      (trackingApplication rows columns width true).compute sizes ⟨host, arguments.property⟩)

theorem integerBezoutRowsWithLeft_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutRowsWithLeft rows columns width).Realizable := by
  let computation := integerBezoutRowsWithLeft rows columns width
  let allowed := computation.precondition
  have prepared := ((Realizable.Internal.BezoutRows.coefficients_realizable rows columns width).withArguments
    computation.inputDomains originalSelection (by intro name; fin_cases name <;> rfl)).withPrecondition allowed
      (by intros; trivial)
  have stage := Realizable.pairOutputs _ _ _ (trackingApplication rows columns width false).precondition
    (trackingApplication rows columns width false).compute (trackingApplication rows columns width true).compute
    (trackingApplication_realizable rows columns width false) (trackingApplication_realizable rows columns width true)
  have complete := prepared.letThen stage (fun _ => rfl) rfl (by intros; assumption)
  exact complete.withSpecification allowed computation.compute (by intros; assumption) (by intros; rfl)

/-- Both returned matrices use exactly the coefficients computed from the current matrix. -/
theorem integerBezoutRowsWithLeft_compute (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutRowsWithLeft rows columns width).Arguments sizes //
      (integerBezoutRowsWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerBezoutRowsWithLeft rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.bezoutRowsWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := by
  let coefficientArguments : (Realizable.Internal.BezoutCoefficients.computation width).Arguments sizes :=
    fun choice => ⟨(arguments.val 3).val (if choice then arguments.val 1 else arguments.val 0)
      (arguments.val 2), (arguments.val 3).property _ _⟩
  apply Prod.ext
  all_goals
    change IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes rows))
      (arguments.val 0) (arguments.val 1)
      !![((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 0).val,
        ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 1).val;
        ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 2).val,
        ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 3).val] _ = _
    erw [Realizable.Internal.BezoutCoefficients.compute_matrix]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Preserve the accumulated transformation equation and unimodularity together. -/
theorem integerBezoutRowsWithLeft_preserves (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutRowsWithLeft rows columns width).Arguments sizes //
      (integerBezoutRowsWithLeft rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 4).val * original * right = (arguments.val 3).val)
    (leftUnit : IsUnit (arguments.val 4).val.det) :
    let result := (integerBezoutRowsWithLeft rows columns width).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det := by
  have computed := integerBezoutRowsWithLeft_compute rows columns width sizes arguments
  have currentEqual := congrArg Prod.fst computed
  have leftEqual := congrArg Prod.snd computed
  dsimp only at currentEqual leftEqual
  constructor
  · erw [leftEqual, currentEqual]
    exact IntegerMatrix.bezoutRowsWithLeft_equation
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      _ _ _ _ _ _ _ equation
  · erw [leftEqual]
    exact IntegerMatrix.bezoutRowsWithLeft_unimodular
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      _ _ arguments.property _ _ _ leftUnit

private noncomputable def columnTrackingInputs (rows columns width : MvPolynomial Parameter ℕ) :
    Fin 5 → EncodedDomain Parameter := fun name => match name with
  | 0 | 1 => boundedIndex columns
  | 2 => boundedIndex rows
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices columns columns width

private noncomputable def prepareColumnTracking (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerBezoutRowsWithLeft columns rows width).onResults (columnTrackingInputs rows columns width)
    (fun _ arguments => arguments 0 ≠ arguments 1)
    (fun name _ arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => ⟨(arguments.val 3).val.transpose, fun column row => (arguments.val 3).property row column⟩
      | 4 => ⟨(arguments.val 4).val.transpose, fun column row => (arguments.val 4).property row column⟩)
    (fun _ arguments => arguments.property)

/-- Eliminate a row entry, retaining the actual updated right transformation. -/
noncomputable def integerBezoutColumnsWithRight (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  (prepareColumnTracking rows columns width).followedBy
    (integerMatrixPairTranspose columns rows columns columns (2 * (2 * width + 1) + 1)) rfl (by intros; trivial)

theorem integerBezoutColumnsWithRight_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutColumnsWithRight rows columns width).Realizable := by
  let inputs := columnTrackingInputs rows columns width
  let allowed sizes (arguments : ∀ name, (inputs name).Carrier sizes) := arguments 0 ≠ arguments 1
  have first := ((integerMatrixTranspose_realizable rows columns width).withArguments inputs
    (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  have second := ((integerMatrixTranspose_realizable columns columns width).withArguments inputs
    (MultiTape.oneTape 4) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  have prepared : (prepareColumnTracking rows columns width).Realizable := by
    apply (integerBezoutRowsWithLeft_realizable columns rows width).onResults inputs allowed
      (fun name _ arguments => match name with
        | 0 => arguments.val 0
        | 1 => arguments.val 1
        | 2 => arguments.val 2
        | 3 => ⟨(arguments.val 3).val.transpose, fun column row => (arguments.val 3).property row column⟩
        | 4 => ⟨(arguments.val 4).val.transpose, fun column row => (arguments.val 4).property row column⟩)
      (fun _ arguments => arguments.property)
    intro name
    fin_cases name
    · exact Realizable.argument inputs 0 allowed
    · exact Realizable.argument inputs 1 allowed
    · exact Realizable.argument inputs 2 allowed
    · exact first
    · exact second
  exact prepared.followedBy
    (integerMatrixPairTranspose_realizable columns rows columns columns (2 * (2 * width + 1) + 1)) rfl (by intros; trivial)

/-- Column accumulation is precisely the transpose of the certified row accumulation. -/
theorem integerBezoutColumnsWithRight_compute (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutColumnsWithRight rows columns width).Arguments sizes //
      (integerBezoutColumnsWithRight rows columns width).precondition sizes arguments}) :
    let result := (integerBezoutColumnsWithRight rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.bezoutColumnsWithRight
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := by
  let transposed : (integerBezoutRowsWithLeft columns rows width).Arguments sizes := fun name => match name with
    | 0 => arguments.val 0
    | 1 => arguments.val 1
    | 2 => arguments.val 2
    | 3 => ⟨(arguments.val 3).val.transpose, fun column row => (arguments.val 3).property row column⟩
    | 4 => ⟨(arguments.val 4).val.transpose, fun column row => (arguments.val 4).property row column⟩
  have computed := integerBezoutRowsWithLeft_compute columns rows width sizes ⟨transposed, arguments.property⟩
  exact congrArg (fun pair => (pair.1.transpose, pair.2.transpose)) computed

set_option backward.isDefEq.respectTransparency false in
/-- Preserve the full transformation equation and unimodularity of the right basis. -/
theorem integerBezoutColumnsWithRight_preserves (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutColumnsWithRight rows columns width).Arguments sizes //
      (integerBezoutColumnsWithRight rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (equation : left * original * (arguments.val 4).val = (arguments.val 3).val)
    (rightUnit : IsUnit (arguments.val 4).val.det) :
    let result := (integerBezoutColumnsWithRight rows columns width).compute sizes arguments
    left * original * result.2.val = result.1.val ∧ IsUnit result.2.val.det := by
  have computed := integerBezoutColumnsWithRight_compute rows columns width sizes arguments
  have currentEqual := congrArg Prod.fst computed
  have rightEqual := congrArg Prod.snd computed
  dsimp only at currentEqual rightEqual
  constructor
  · erw [rightEqual, currentEqual]
    exact IntegerMatrix.bezoutColumnsWithRight_equation
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      _ _ _ _ _ _ _ equation
  · erw [rightEqual]
    exact IntegerMatrix.bezoutColumnsWithRight_unimodular
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      _ _ arguments.property _ _ _ rightUnit

end Polytime2.Computation
