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

import Polytime2.Matrices.IntegerPairTranspose
import Polytime2.Matrices.EuclideanMath
import Polytime2.Matrices.IntegerOperations
import Polytime2.Arithmetic.SignedDivision

/-! # Certified Euclidean row reduction with left-basis tracking

Inputs are distinct source and target rows, a column, the current integer
matrix, and its left basis. The source pivot must be positive. Compute one
negated quotient from the current matrix and apply it to both matrices. The
source row stays unchanged and the selected target entry becomes the Euclidean
remainder. Widths are derived internally; no global sweep bound is asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 5 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 0) (arguments 2)

private noncomputable def coefficient (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) where
  inputDomains := inputs rows columns width
  outputDomain := binaryIntegers width
  precondition := allowed rows columns width
  compute _ arguments := ⟨-((arguments.val 3).val (arguments.val 1) (arguments.val 2) /
    (arguments.val 3).val (arguments.val 0) (arguments.val 2)), by
    rw [Int.natAbs_neg]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt ((arguments.val 3).property _ _)⟩

private theorem coefficient_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (coefficient rows columns width).Realizable := by
  let computation := coefficient rows columns width
  let entry (source : Bool) sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (binaryIntegers width).Carrier sizes :=
    ⟨(arguments.val 3).val (if source then arguments.val 0 else arguments.val 1) (arguments.val 2),
      (arguments.val 3).property _ _⟩
  have entryReady (source : Bool) :
      (Computation.mk computation.inputDomains (binaryIntegers width) computation.precondition (entry source)).Realizable := by
    exact (integerMatrixEntry_realizable rows columns width).onResults computation.inputDomains computation.precondition
      (fun name _ arguments => match name with
        | 0 => if source then arguments.val 0 else arguments.val 1
        | 1 => arguments.val 2
        | 2 => arguments.val 3) (by intros; trivial) (by
          intro name
          fin_cases name
          · cases source
            · exact Realizable.argument computation.inputDomains 1 computation.precondition
            · exact Realizable.argument computation.inputDomains 0 computation.precondition
          · exact Realizable.argument computation.inputDomains 2 computation.precondition
          · exact Realizable.argument computation.inputDomains 3 computation.precondition)
  have divided := (integerQuotient_realizable width).onResults computation.inputDomains computation.precondition entry
    (fun _ arguments => ne_of_gt arguments.property.2) entryReady
  have negated := divided.followedBy (integerNegate_realizable width) rfl (by intros; trivial)
  exact negated.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

private noncomputable def host (rows columns width : MvPolynomial Parameter ℕ) :=
  Sum.elim (inputs rows columns width) (fun _ : Unit => binaryIntegers width)

private def selection (left : Bool) : Fin 4 ↪ Fin 5 ⊕ Unit :=
  ⟨(fun name => match name with
    | 0 => .inl 1 | 1 => .inl 0 | 2 => .inr () | 3 => .inl (if left then 4 else 3)), by
    intro first second equal
    cases left <;> fin_cases first <;> fin_cases second <;> simp_all⟩

private noncomputable def application (rows columns width : MvPolynomial Parameter ℕ) (left : Bool) :=
  (integerRowAdd rows (if left then rows else columns) width).withArguments (host rows columns width)
    (selection left) (by intro name; cases left <;> fin_cases name <;> rfl)

private theorem application_realizable (rows columns width : MvPolynomial Parameter ℕ) (left : Bool) :
    (application rows columns width left).Realizable :=
  (integerRowAdd_realizable rows (if left then rows else columns) width).withArguments (host rows columns width)
    (selection left) (by intro name; cases left <;> fin_cases name <;> rfl)

private noncomputable def stage (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5 ⊕ Unit) where
  inputDomains := host rows columns width
  outputDomain := (integerMatrices rows columns (2 * width + 1)).prod (integerMatrices rows rows (2 * width + 1))
  precondition sizes arguments := allowed rows columns width sizes (fun name => arguments (.inl name))
  compute sizes arguments := ((application rows columns width false).compute sizes ⟨arguments.val, trivial⟩,
    (application rows columns width true).compute sizes ⟨arguments.val, trivial⟩)

private theorem stage_realizable (rows columns width : MvPolynomial Parameter ℕ) : (stage rows columns width).Realizable := by
  let computation := stage rows columns width
  have first := (application_realizable rows columns width false).withPrecondition computation.precondition (by intros; trivial)
  have second := (application_realizable rows columns width true).withPrecondition computation.precondition (by intros; trivial)
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ first second

/-- Reduce a target entry modulo a positive pivot and update the actual left basis. -/
noncomputable def integerRowRemainderWithLeft (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  (coefficient rows columns width).letThen (stage rows columns width) (fun _ => rfl) rfl (by intros; assumption)

theorem integerRowRemainderWithLeft_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowRemainderWithLeft rows columns width).Realizable :=
  (coefficient_realizable rows columns width).letThen (stage_realizable rows columns width)
    (fun _ => rfl) rfl (by intros; assumption)

/-- The one prepared quotient is applied to the working matrix and its basis. -/
theorem integerRowRemainderWithLeft_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRowRemainderWithLeft rows columns width).Arguments sizes //
      (integerRowRemainderWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerRowRemainderWithLeft rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.rowRemainderWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := rfl

/-- The selected output is a genuine nonnegative remainder below the unchanged pivot. -/
theorem integerRowRemainderWithLeft_range (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRowRemainderWithLeft rows columns width).Arguments sizes //
      (integerRowRemainderWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerRowRemainderWithLeft rows columns width).compute sizes arguments
    0 ≤ result.1.val (arguments.val 1) (arguments.val 2) ∧
      result.1.val (arguments.val 1) (arguments.val 2) < (arguments.val 3).val (arguments.val 0) (arguments.val 2) := by
  have pure := IntegerMatrix.rowRemainder_range (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
    (arguments.val 3).val arguments.property.2
  have transfer := congrArg (fun matrices =>
    0 ≤ matrices.1 (arguments.val 1) (arguments.val 2) ∧
      matrices.1 (arguments.val 1) (arguments.val 2) < (arguments.val 3).val (arguments.val 0) (arguments.val 2))
    (integerRowRemainderWithLeft_correct rows columns width sizes arguments)
  exact transfer.mpr pure

/-- Both the original-to-current equation and unimodularity of the left basis survive. -/
theorem integerRowRemainderWithLeft_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRowRemainderWithLeft rows columns width).Arguments sizes //
      (integerRowRemainderWithLeft rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 4).val * original * right = (arguments.val 3).val)
    (unit : IsUnit (arguments.val 4).val.det) :
    let result := (integerRowRemainderWithLeft rows columns width).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det := by
  have pure := And.intro
    (IntegerMatrix.rowRemainderWithLeft_equation (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
      (arguments.val 3).val original (arguments.val 4).val right equation)
    (IntegerMatrix.rowRemainderWithLeft_unimodular (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) arguments.property.1
      (arguments.val 2) (arguments.val 3).val (arguments.val 4).val unit)
  have transfer := congrArg (fun matrices => matrices.2 * original * right = matrices.1 ∧ IsUnit matrices.2.det)
    (integerRowRemainderWithLeft_correct rows columns width sizes arguments)
  exact transfer.mpr pure

private noncomputable def columnInputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 5 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex columns
  | 2 => boundedIndex rows
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices columns columns width

private def columnAllowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (columnInputs rows columns width name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 2) (arguments 0)

private noncomputable def columnPrepared (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerRowRemainderWithLeft columns rows width).onResults (columnInputs rows columns width) (columnAllowed rows columns width)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => (integerMatrixTranspose rows columns width).compute sizes ⟨(fun _ => arguments.val 3), trivial⟩
      | 4 => (integerMatrixTranspose columns columns width).compute sizes ⟨(fun _ => arguments.val 4), trivial⟩)
    (fun _ arguments => arguments.property)

private theorem columnPrepared_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (columnPrepared rows columns width).Realizable := by
  let computation := columnPrepared rows columns width
  apply (integerRowRemainderWithLeft_realizable columns rows width).onResults computation.inputDomains computation.precondition
    _ (by
      intro sizes arguments
      change arguments.val 0 ≠ arguments.val 1 ∧
        0 < (arguments.val 3).val (arguments.val 2) (arguments.val 0)
      exact arguments.property)
  intro name
  fin_cases name
  · exact Realizable.argument computation.inputDomains 0 computation.precondition
  · exact Realizable.argument computation.inputDomains 1 computation.precondition
  · exact Realizable.argument computation.inputDomains 2 computation.precondition
  · exact ((integerMatrixTranspose_realizable rows columns width).withArguments computation.inputDomains
      (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition computation.precondition (by intros; trivial)
  · exact ((integerMatrixTranspose_realizable columns columns width).withArguments computation.inputDomains
      (MultiTape.oneTape 4) (fun _ => rfl)).withPrecondition computation.precondition (by intros; trivial)

/-- Reduce a column entry modulo a positive pivot and update the actual right basis. -/
noncomputable def integerColumnRemainderWithRight (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  (columnPrepared rows columns width).followedBy (integerMatrixPairTranspose columns rows columns columns (2 * width + 1)) rfl (by intros; trivial)

theorem integerColumnRemainderWithRight_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnRemainderWithRight rows columns width).Realizable :=
  (columnPrepared_realizable rows columns width).followedBy (integerMatrixPairTranspose_realizable columns rows columns columns (2 * width + 1)) rfl (by intros; trivial)

/-- The column computation is precisely the transposed mathematical quotient operation. -/
theorem integerColumnRemainderWithRight_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerColumnRemainderWithRight rows columns width).Arguments sizes //
      (integerColumnRemainderWithRight rows columns width).precondition sizes arguments}) :
    let result := (integerColumnRemainderWithRight rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.columnRemainderWithRight
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := rfl

/-- The transposed computation retains the presentation and unimodularity of the right basis. -/
theorem integerColumnRemainderWithRight_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerColumnRemainderWithRight rows columns width).Arguments sizes //
      (integerColumnRemainderWithRight rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (equation : left * original * (arguments.val 4).val = (arguments.val 3).val)
    (unit : IsUnit (arguments.val 4).val.det) :
    let result := (integerColumnRemainderWithRight rows columns width).compute sizes arguments
    left * original * result.2.val = result.1.val ∧ IsUnit result.2.val.det := by
  have pure := And.intro
    (IntegerMatrix.columnRemainderWithRight_equation (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
      (arguments.val 3).val original left (arguments.val 4).val equation)
    (IntegerMatrix.columnRemainderWithRight_unimodular (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) arguments.property.1
      (arguments.val 2) (arguments.val 3).val (arguments.val 4).val unit)
  have transfer := congrArg (fun matrices => left * original * matrices.2 = matrices.1 ∧ IsUnit matrices.2.det)
    (integerColumnRemainderWithRight_correct rows columns width sizes arguments)
  exact transfer.mpr pure

end Polytime2.Computation
