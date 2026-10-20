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

import Polytime2.Computation.Conditional
import Polytime2.Arrays.Operations
import Polytime2.Matrices.AddressOperations
import Polytime2.Matrices.RowsPresentation
import Polytime2.Computation.Reindex

/-! # Row-and-column access to ordinary mathematical matrices -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open StandardMatrixRows

noncomputable section MatrixCoordinates

/-- Arguments are binary row and column indices and the immutable matrix. -/
def matrixEntry (scalar : EncodedDomain Empty) : Computation (Fin 3) (Fin 3) where
  inputDomains
    | 0 | 1 => EncodedDomain.binaryNaturals 0
    | 2 => matrixDomain scalar
  outputDomain := scalar.constant
  precondition sizes arguments := sizes 2 < 2 ^ sizes 0 ∧
    (arguments 0).val < sizes 1 ∧ (arguments 1).val < sizes 2 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments := (arguments.val 2)
    ⟨(arguments.val 0).val, arguments.property.2.1⟩
    ⟨(arguments.val 1).val, arguments.property.2.2.1⟩

/-- Arguments are row, column, immutable matrix, and replacement scalar.
The result changes exactly that coordinate and has the same mathematical shape. -/
def matrixReplace (scalar : EncodedDomain Empty) : Computation (Fin 3) (Fin 4) where
  inputDomains
    | 0 | 1 => EncodedDomain.binaryNaturals 0
    | 2 => matrixDomain scalar
    | 3 => scalar.constant
  outputDomain := matrixDomain scalar
  precondition sizes arguments := sizes 2 < 2 ^ sizes 0 ∧
    (arguments 0).val < sizes 1 ∧ (arguments 1).val < sizes 2 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments :=
    let row := ⟨(arguments.val 0).val, arguments.property.2.1⟩
    let column := ⟨(arguments.val 1).val, arguments.property.2.2.1⟩
    Function.update (arguments.val 2) row
      (Function.update (arguments.val 2 row) column (arguments.val 3))

private def lookupDomains (scalar : EncodedDomain Empty) : Bool → EncodedDomain (Fin 3)
  | false => EncodedDomain.binaryNaturals 0
  | true => matrixDomain scalar

private def lookupEquivalence (scalar : EncodedDomain Empty) (name : Bool) (sizes : Fin 3 → ℕ) :
    (lookupDomains scalar name).Carrier sizes ≃
      ((arrayLookup scalar.constant 0 StandardMatrixEntry.length).inputDomains name).Carrier sizes :=
  match name with
  | false => Equiv.refl _
  | true => matrixEquiv sizes

private def lookup (scalar : EncodedDomain Empty) : Computation (Fin 3) Bool :=
  (arrayLookup scalar.constant 0 StandardMatrixEntry.length).reindexDomains
    (lookupDomains scalar) scalar.constant (lookupEquivalence scalar) (fun _ => Equiv.refl _)

private theorem lookup_realizable (scalar : EncodedDomain Empty) : (lookup scalar).Realizable :=
  (arrayLookup_realizable scalar.constant 0 StandardMatrixEntry.length).reindexDomains _ _ _ _
    (by intro name sizes; cases name <;> rfl) (by intro sizes; rfl)
    (by intro name sizes value; cases name <;> rfl) (by intro sizes value; rfl)

theorem matrixEntry_realizable (scalar : EncodedDomain Empty) : (matrixEntry scalar).Realizable := by
  let computation := matrixEntry scalar
  have address := matrixAddress_realizable.onResults computation.inputDomains computation.precondition
    (fun flag _ arguments => if flag then arguments.val 1 else arguments.val 0)
    (by
      intro sizes arguments
      exact ⟨arguments.property.1, lt_of_lt_of_le (StandardMatrixEntry.index_lt sizes _ _
        arguments.property.2.1 arguments.property.2.2.1) (by simpa [StandardMatrixEntry.length] using arguments.property.2.2.2)⟩)
    (by
      intro flag
      cases flag
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have realizable := (lookup_realizable scalar).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | true => arguments.val 2
      | false => matrixAddress.compute sizes ⟨(fun flag => if flag then arguments.val 1 else arguments.val 0),
          ⟨arguments.property.1, lt_of_lt_of_le (StandardMatrixEntry.index_lt sizes _ _
            arguments.property.2.1 arguments.property.2.2.1) (by simpa [StandardMatrixEntry.length] using arguments.property.2.2.2)⟩⟩)
    (by
      intro sizes arguments
      change (arguments.val 0).val * sizes 2 + (arguments.val 1).val <
        MvPolynomial.eval sizes StandardMatrixEntry.length
      exact StandardMatrixEntry.index_lt sizes _ _ arguments.property.2.1 arguments.property.2.2.1)
    (by
      intro choice
      cases choice
      · exact address
      · exact Realizable.argument computation.inputDomains 2 computation.precondition)
  exact realizable.withSpecification computation.precondition computation.compute
    (by intro sizes arguments valid; exact valid)
    (by
      intro sizes arguments valid
      change matrixEquiv sizes (arguments 2) _ = _
      refine (congrArg (matrixEquiv sizes (arguments 2)) ?_).trans
        (matrixEquiv_apply sizes (arguments 2) ⟨(arguments 0).val, valid.2.1⟩
          ⟨(arguments 1).val, valid.2.2.1⟩)
      apply Fin.ext
      exact (matrixIndex_val sizes ⟨(arguments 0).val, valid.2.1⟩
        ⟨(arguments 1).val, valid.2.2.1⟩).symm)

private def updateDomains (scalar : EncodedDomain Empty) : Fin 3 → EncodedDomain (Fin 3)
  | 0 => EncodedDomain.binaryNaturals 0
  | 1 => matrixDomain scalar
  | 2 => scalar.constant

private def updateEquivalence (scalar : EncodedDomain Empty) (name : Fin 3) (sizes : Fin 3 → ℕ) :
    (updateDomains scalar name).Carrier sizes ≃
      ((arrayUpdate scalar.constant 0 StandardMatrixEntry.length).inputDomains name).Carrier sizes :=
  match name with
  | 0 => Equiv.refl _
  | 1 => matrixEquiv sizes
  | 2 => Equiv.refl _

private def update (scalar : EncodedDomain Empty) : Computation (Fin 3) (Fin 3) :=
  (arrayUpdate scalar.constant 0 StandardMatrixEntry.length).reindexDomains
    (updateDomains scalar) (matrixDomain scalar) (updateEquivalence scalar) (fun sizes => matrixEquiv sizes)

private theorem update_realizable (scalar : EncodedDomain Empty) : (update scalar).Realizable :=
  (arrayUpdate_realizable scalar.constant 0 StandardMatrixEntry.length).reindexDomains _ _ _ _
    (by intro name sizes; fin_cases name <;> rfl) (by intro sizes; rfl)
    (by intro name sizes value; fin_cases name <;> rfl) (by intro sizes value; rfl)

theorem matrixReplace_realizable (scalar : EncodedDomain Empty) : (matrixReplace scalar).Realizable := by
  let computation := matrixReplace scalar
  have address := matrixAddress_realizable.onResults computation.inputDomains computation.precondition
    (fun flag _ arguments => if flag then arguments.val 1 else arguments.val 0)
    (by
      intro sizes arguments
      exact ⟨arguments.property.1, lt_of_lt_of_le (StandardMatrixEntry.index_lt sizes _ _
        arguments.property.2.1 arguments.property.2.2.1) (by simpa [StandardMatrixEntry.length] using arguments.property.2.2.2)⟩)
    (by
      intro flag
      cases flag
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have realizable := (update_realizable scalar).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
      | 0 => matrixAddress.compute sizes ⟨(fun flag => if flag then arguments.val 1 else arguments.val 0),
          ⟨arguments.property.1, lt_of_lt_of_le (StandardMatrixEntry.index_lt sizes _ _
            arguments.property.2.1 arguments.property.2.2.1) (by simpa [StandardMatrixEntry.length] using arguments.property.2.2.2)⟩⟩
      | 1 => arguments.val 2
      | 2 => arguments.val 3)
    (by
      intro sizes arguments
      change (arguments.val 0).val * sizes 2 + (arguments.val 1).val <
        MvPolynomial.eval sizes StandardMatrixEntry.length
      exact StandardMatrixEntry.index_lt sizes _ _ arguments.property.2.1 arguments.property.2.2.1)
    (by
      intro name
      fin_cases name
      · exact address
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 3 computation.precondition)
  exact realizable.withSpecification computation.precondition computation.compute
    (by intro sizes arguments valid; exact valid)
    (by
      intro sizes arguments valid
      change computation.Arguments sizes at arguments
      dsimp only [computation, matrixReplace] at arguments
      change (matrixEquiv sizes).symm (Function.update (matrixEquiv sizes (arguments 2)) _ (arguments 3)) = _
      have indexEqual : (⟨(arguments 0).val * sizes 2 + (arguments 1).val,
          StandardMatrixEntry.index_lt sizes _ _ valid.2.1 valid.2.2.1⟩ :
          Fin (MvPolynomial.eval sizes StandardMatrixEntry.length)) =
          matrixIndex sizes (⟨(arguments 0).val, valid.2.1⟩, ⟨(arguments 1).val, valid.2.2.1⟩) := by
        apply Fin.ext
        exact (matrixIndex_val sizes ⟨(arguments 0).val, valid.2.1⟩ ⟨(arguments 1).val, valid.2.2.1⟩).symm
      erw [indexEqual]
      let matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) (scalar.Carrier Empty.elim) := arguments 2
      let replacement : scalar.Carrier Empty.elim := arguments 3
      let selectedRow : Fin (sizes 1) := ⟨(arguments 0).val, valid.2.1⟩
      let selectedColumn : Fin (sizes 2) := ⟨(arguments 1).val, valid.2.2.1⟩
      change (matrixEquiv sizes).symm
        (Function.update (matrixEquiv sizes matrix) (matrixIndex sizes (selectedRow, selectedColumn)) replacement) =
        Function.update matrix selectedRow (Function.update (matrix selectedRow) selectedColumn replacement)
      funext row column
      change Function.update (matrixEquiv sizes matrix) (matrixIndex sizes (selectedRow, selectedColumn))
        replacement (matrixIndex sizes (row, column)) =
        Function.update matrix selectedRow (Function.update (matrix selectedRow) selectedColumn replacement) row column
      by_cases sameRow : row = selectedRow <;> by_cases sameColumn : column = selectedColumn <;>
        simp_all [Function.update, (matrixIndex sizes).injective.eq_iff, matrixEquiv_apply])

end MatrixCoordinates
end Polytime2.Computation
