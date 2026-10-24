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

import Polytime2.Matrices.IntegerRowDiagonal
import Polytime2.Arithmetic.SignedQuotient
import Polytime2.Matrices.IntegerResize

/-! # Recovering integer coordinates from a Smith diagonal

For a rectangular integer matrix and a target vector, divide each target
coordinate by its diagonal entry and put zero in columns without a matching
row. Division by zero also returns zero. On a Smith diagonal these are exactly
the usual active solution coordinates, without requiring a rank input.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.IntegerMatrix

/-- Divide matching target and diagonal entries; unmatched columns receive zero. -/
def diagonalQuotientSolution {rows columns : ℕ}
    (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (target : Fin rows → ℤ) (column : Fin columns) : ℤ :=
  if within : column.val < rows then target ⟨column.val, within⟩ / diagonal ⟨column.val, within⟩ column else 0

/-- Zero divisors at inactive entries recover the ordinary active solution coordinates. -/
theorem diagonalQuotientSolution_eq {rows columns : ℕ}
    (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ) :
    diagonalQuotientSolution diagonal target = diagonalSolution diagonal rank smith.1 target := by
  funext column
  by_cases active : column.val < rank
  · have within : column.val < rows := active.trans_le (smith.1.trans (Nat.min_le_left _ _))
    simp [diagonalQuotientSolution, diagonalSolution, active, within]
  · by_cases within : column.val < rows
    · simp [diagonalQuotientSolution, diagonalSolution, active, within,
        smith.2.2.1 ⟨column.val, within⟩ column (by change rank ≤ column.val; omega)]
    · simp [diagonalQuotientSolution, diagonalSolution, active, within]

/-- The rank-free quotient coordinates solve every feasible Smith diagonal system. -/
theorem diagonalQuotientSolution_correct {rows columns : ℕ}
    (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ)
    (feasible : diagonalFeasible diagonal rank smith.1 target) :
    diagonal.mulVec (diagonalQuotientSolution diagonal target) = target := by
  rw [diagonalQuotientSolution_eq diagonal rank smith target]
  exact diagonalSolution_correct diagonal rank smith target feasible

end Polytime2.IntegerMatrix

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def context (rows columns width : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun choice => if choice then (binaryIntegers width).arrayOfLength rows else integerMatrices rows columns width

private noncomputable def solutionEntry (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (context rows columns width name).Carrier sizes)
    (column : Fin (MvPolynomial.eval sizes columns)) : (binaryIntegers width).Carrier sizes :=
  ⟨IntegerMatrix.diagonalQuotientSolution (arguments false).val (fun row => (arguments true row).val) column, by
    unfold IntegerMatrix.diagonalQuotientSolution
    split
    · exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments true _).property
    · simp⟩

private noncomputable def atWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  arrayTabulate (context rows columns width) (binaryIntegers width) columns (solutionEntry rows columns width)

private theorem atWidth_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (atWidth rows columns width).Realizable := by
  let step := arrayTransformStep (context rows columns width) (arrayPosition columns) (binaryIntegers width)
    (solutionEntry rows columns width)
  let within sizes (arguments : step.Arguments sizes) :=
    decide ((arguments (.inr ())).val < MvPolynomial.eval sizes rows)
  have tested := (positionWithin_realizable columns rows).withArguments step.inputDomains
    (MultiTape.oneTape (.inr ())) (by intros; rfl)
  apply arrayTabulate_realizable (context rows columns width) (binaryIntegers width) columns (solutionEntry rows columns width)
  apply Realizable.ofCases (computation := step) within tested
  · let allowed sizes arguments := step.precondition sizes arguments ∧ within sizes arguments = true
    have row := (integerMatrixRowWithIndex_realizable rows columns width (arrayPosition columns)
      (fun _ index => index.val) (arrayPosition_value columns)).onArguments step.inputDomains allowed
        (fun choice => match choice with
        | false => (.inr ()) | true => (.inl false)) (by intro choice; cases choice <;> rfl) (by
        intro sizes arguments
        change (arguments.val (.inr ())).val < MvPolynomial.eval sizes rows
        exact of_decide_eq_true arguments.property.2)
    let divisorArguments choice sizes (arguments : {arguments : step.Arguments sizes // allowed sizes arguments}) :
        ((arrayLookupWithIndex (binaryIntegers width) (arrayPosition columns) (fun _ index => index.val) columns).inputDomains choice).Carrier sizes :=
      match choice with
      | false => arguments.val (.inr ())
      | true => (integerMatrixRowWithIndex rows columns width (arrayPosition columns) (fun _ index => index.val)).compute sizes
          ⟨(fun choice => match choice with
            | false => arguments.val (.inr ()) | true => arguments.val (.inl false)), (by
            change (arguments.val (.inr ())).val < MvPolynomial.eval sizes rows
            exact of_decide_eq_true arguments.property.2)⟩
    have divisor := (arrayLookupWithIndex_realizable (binaryIntegers width) (arrayPosition columns)
      (fun _ index => index.val) (arrayPosition_value columns) columns).onResults step.inputDomains allowed divisorArguments
      (by intro sizes arguments; exact (arguments.val (.inr ())).isLt) (by
        intro choice
        cases choice
        · exact Realizable.argument step.inputDomains (.inr ()) allowed
        · exact row)
    have numerator := (arrayLookupWithIndex_realizable (binaryIntegers width) (arrayPosition columns)
      (fun _ index => index.val) (arrayPosition_value columns) rows).onArguments step.inputDomains allowed
        (fun choice => match choice with
        | false => (.inr ()) | true => (.inl true)) (by intro choice; cases choice <;> rfl) (by
        intro sizes arguments
        change (arguments.val (.inr ())).val < MvPolynomial.eval sizes rows
        exact of_decide_eq_true arguments.property.2)
    let quotientArguments choice sizes (arguments : {arguments : step.Arguments sizes // allowed sizes arguments}) :
        (binaryIntegers width).Carrier sizes :=
      match choice with
      | false => ⟨(arguments.val (.inl true) ⟨(arguments.val (.inr ())).val, of_decide_eq_true arguments.property.2⟩).val,
          (arguments.val (.inl true) _).property⟩
      | true => ⟨(arguments.val (.inl false)).val
          ⟨(arguments.val (.inr ())).val, of_decide_eq_true arguments.property.2⟩ (arguments.val (.inr ())),
          (arguments.val (.inl false)).property _ _⟩
    have divided := (integerTotalQuotient_realizable width).onResults step.inputDomains allowed quotientArguments
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact numerator
        · exact divisor)
    apply divided.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    have inside := of_decide_eq_true valid.2
    dsimp only [step, arrayTransformStep, solutionEntry]
    simp [IntegerMatrix.diagonalQuotientSolution, inside, Computation.onResults, integerTotalQuotient_correct, quotientArguments]
  · let rejected sizes arguments := step.precondition sizes arguments ∧ within sizes arguments = false
    have zero := (integerZero_realizable width).onResults step.inputDomains rejected
      (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
    apply zero.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    have outside := of_decide_eq_false valid.2
    dsimp only [step, arrayTransformStep, solutionEntry]
    simp [IntegerMatrix.diagonalQuotientSolution, outside, Computation.onResults, integerZero]

private noncomputable def inputs (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    Bool → EncodedDomain Parameter :=
  fun choice => if choice then (binaryIntegers targetWidth).arrayOfLength rows
    else integerMatrices rows columns matrixWidth

private theorem matrixFits (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (matrix : (integerMatrices rows columns matrixWidth).Carrier sizes) :
    ∀ row column, (matrix.val row column).natAbs < 2 ^ MvPolynomial.eval sizes (matrixWidth + targetWidth) := by
  intro row column
  exact (matrix.property row column).trans_le (pow_le_pow_right₀ (by decide) (by simp only [map_add]; omega))

private noncomputable def widenedTarget (rows matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  mapArray (binaryIntegers targetWidth) (binaryIntegers (matrixWidth + targetWidth)) rows
    (fun sizes value => (integerWidenTo targetWidth matrixWidth (matrixWidth + targetWidth) (by ring)).compute sizes
      ⟨fun _ => value, trivial⟩)

private theorem widenedTarget_realizable (rows matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (widenedTarget rows matrixWidth targetWidth).Realizable :=
  mapArray_realizable _ _ rows _ (integerWidenTo_realizable targetWidth matrixWidth (matrixWidth + targetWidth) (by ring))

/-- Recover diagonal solution coordinates with independently bounded matrix and target entries. -/
noncomputable def integerDiagonalSolution
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (atWidth rows columns (matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (integerMatrixNarrow rows columns matrixWidth (matrixWidth + targetWidth)).compute sizes
          ⟨fun _ => arguments.val false, matrixFits rows columns matrixWidth targetWidth sizes (arguments.val false)⟩
      | true => (widenedTarget rows matrixWidth targetWidth).compute sizes ⟨fun _ => arguments.val true, trivial⟩)
    (by intros; trivial)

/-- Input widening and rank-free coordinate recovery compose without extra preconditions. -/
theorem integerDiagonalSolution_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalSolution rows columns matrixWidth targetWidth).Realizable := by
  apply (atWidth_realizable rows columns (matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · apply (integerMatrixResize_realizable rows columns matrixWidth (matrixWidth + targetWidth)).onResults
      (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) (fun _ _ arguments => arguments.val false)
      (fun sizes arguments => matrixFits rows columns matrixWidth targetWidth sizes (arguments.val false))
    intro singleton
    cases singleton
    exact Realizable.argument _ false _
  · exact (widenedTarget_realizable rows matrixWidth targetWidth).withArguments
      (inputs rows columns matrixWidth targetWidth) (MultiTape.oneTape true) (by intros; rfl)

/-- The result is exactly the ordinary rank-free diagonal quotient vector. -/
theorem integerDiagonalSolution_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerDiagonalSolution rows columns matrixWidth targetWidth).Arguments sizes) :
    (fun column => ((integerDiagonalSolution rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ column).val) =
      IntegerMatrix.diagonalQuotientSolution (arguments false).val (fun row => (arguments true row).val) := by
  rfl

/-- Whenever a Smith diagonal system is feasible, the computed coordinates solve it. -/
theorem integerDiagonalSolution_solves
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerDiagonalSolution rows columns matrixWidth targetWidth).Arguments sizes)
    (rank : ℕ) (smith : IntegerMatrix.IsSmithDiagonal (arguments false).val rank)
    (feasible : IntegerMatrix.diagonalFeasible (arguments false).val rank smith.1 (fun row => (arguments true row).val)) :
    (arguments false).val.mulVec (fun column =>
      ((integerDiagonalSolution rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ column).val) =
      fun row => (arguments true row).val := by
  rw [integerDiagonalSolution_correct]
  exact IntegerMatrix.diagonalQuotientSolution_correct (arguments false).val rank smith _ feasible

end Polytime2.Computation
