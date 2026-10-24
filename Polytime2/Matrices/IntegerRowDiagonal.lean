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

import Polytime2.Arithmetic.SignedZero
import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.SmithMath
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.PositionArithmetic

/-! # Reading the zero-extended rectangular diagonal

Input an arbitrary bounded rectangular integer matrix. Return one signed entry
per row: its diagonal entry when the corresponding column exists, and zero
otherwise. Width is unchanged. This total read supports Smith feasibility,
including singular inputs and empty column sets.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.IntegerMatrix

/-- Extend a rectangular matrix's diagonal by zero to its row count. -/
def rowDiagonal {rows columns : ℕ} (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (row : Fin rows) : ℤ :=
  if within : row.val < columns then matrix row ⟨row.val, within⟩ else 0

/-- The zero-extended diagonal combines active divisibility and inactive zero tests. -/
theorem diagonalFeasible_iff_rowDiagonal {rows columns : ℕ}
    (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ) :
    diagonalFeasible diagonal rank smith.1 target ↔ ∀ row, rowDiagonal diagonal row ∣ target row := by
  apply forall_congr'
  intro row
  by_cases active : row.val < rank
  · have within : row.val < columns := active.trans_le (smith.1.trans (Nat.min_le_right _ _))
    simp [rowDiagonal, active, within]
  · by_cases within : row.val < columns
    · simp [rowDiagonal, active, within,
        smith.2.2.1 row ⟨row.val, within⟩ (by omega)]
    · simp [rowDiagonal, active, within]

end Polytime2.IntegerMatrix

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def entry (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : Unit → (integerMatrices rows columns width).Carrier sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) : (binaryIntegers width).Carrier sizes :=
  ⟨IntegerMatrix.rowDiagonal (arguments ()).val row, by
    unfold IntegerMatrix.rowDiagonal
    split
    · exact (arguments ()).property _ _
    · simp⟩

/-- Read the full rectangular diagonal, using zero when a row has no matching column. -/
noncomputable def integerMatrixRowDiagonal (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ : Unit => integerMatrices rows columns width) (binaryIntegers width) rows
    (entry rows columns width)

/-- Row access, guarded column access, and zero construction retain the input width. -/
theorem integerMatrixRowDiagonal_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerMatrixRowDiagonal rows columns width).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => integerMatrices rows columns width
  let step := arrayTransformStep context (arrayPosition rows) (binaryIntegers width) (entry rows columns width)
  let within sizes (arguments : step.Arguments sizes) :=
    decide ((arguments (.inr ())).val < MvPolynomial.eval sizes columns)
  have tested := (positionWithin_realizable rows columns).withArguments step.inputDomains
    (MultiTape.oneTape (.inr ())) (by intros; rfl)
  apply arrayTabulate_realizable context (binaryIntegers width) rows (entry rows columns width)
  apply Realizable.ofCases (computation := step) within tested
  · let allowed sizes arguments := step.precondition sizes arguments ∧ within sizes arguments = true
    have row := (integerMatrixRowWithIndex_realizable rows columns width (arrayPosition rows)
      (fun _ index => index.val) (arrayPosition_value rows)).onResults step.inputDomains allowed
      (fun choice _ arguments => match choice with
        | false => arguments.val (.inr ()) | true => arguments.val (.inl ()))
      (by intro sizes arguments; exact (arguments.val (.inr ())).isLt) (by
        intro choice
        cases choice
        · exact Realizable.argument step.inputDomains (.inr ()) allowed
        · exact Realizable.argument step.inputDomains (.inl ()) allowed)
    have read := (arrayLookupWithIndex_realizable (binaryIntegers width) (arrayPosition rows)
      (fun _ index => index.val) (arrayPosition_value rows) columns).onResults step.inputDomains allowed
      (fun choice sizes arguments => match choice with
        | false => arguments.val (.inr ())
        | true => (integerMatrixRowWithIndex rows columns width (arrayPosition rows) (fun _ index => index.val)).compute sizes
            ⟨(fun choice => match choice with
              | false => arguments.val (.inr ()) | true => arguments.val (.inl ())), (arguments.val (.inr ())).isLt⟩)
      (by
        intro sizes arguments
        change (arguments.val (.inr ())).val < MvPolynomial.eval sizes columns
        exact of_decide_eq_true arguments.property.2) (by
        intro choice
        cases choice
        · exact Realizable.argument step.inputDomains (.inr ()) allowed
        · exact row)
    apply read.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    have inside := of_decide_eq_true valid.2
    change _ = IntegerMatrix.rowDiagonal _ _
    simp [IntegerMatrix.rowDiagonal, inside, Computation.onResults, arrayLookupWithIndex,
      integerMatrixRowWithIndex]
  · let rejected sizes arguments := step.precondition sizes arguments ∧ within sizes arguments = false
    have zero := (integerZero_realizable width).onResults step.inputDomains rejected
      (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
    apply zero.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    have outside := of_decide_eq_false valid.2
    change (0 : ℤ) = IntegerMatrix.rowDiagonal _ _
    simp [IntegerMatrix.rowDiagonal, outside]

end Polytime2.Computation
