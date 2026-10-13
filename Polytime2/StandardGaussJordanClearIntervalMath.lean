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

import Polytime2.StandardGaussJordanClearIntervalLoop
import Polytime2.StandardMatrixRowsPresentation

/-! # Mathematical matrix invariant for a row-clear interval -/

namespace Polytime2.StandardGaussJordanClearInterval

open CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality rows columns : ℕ}

/-- Clear exactly the rows in the half-open interval, retaining every other
row from the original matrix. The pivot row is unchanged in all cases. -/
def clearedInterval (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) (start count : ℕ) :
    Matrix (Fin rows) (Fin columns) Scalar := fun row other =>
  if start ≤ row.val ∧ row.val < count then
    MatrixOperations.clearColumn matrix pivot column row other else matrix row other

theorem clearedInterval_start (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) (start : ℕ) :
    clearedInterval matrix pivot column start start = matrix := by
  ext row other
  simp [clearedInterval, show ¬ (start ≤ row.val ∧ row.val < start) by omega]

theorem clearedInterval_next (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot target : Fin rows) (column : Fin columns) (start : ℕ)
    (lower : start ≤ target.val) (distinct : target ≠ pivot) :
    Function.update (clearedInterval matrix pivot column start target.val) target
      (fun other => clearedInterval matrix pivot column start target.val target other +
        (-clearedInterval matrix pivot column start target.val target column) *
          clearedInterval matrix pivot column start target.val pivot other) =
      clearedInterval matrix pivot column start (target.val + 1) := by
  ext row other
  by_cases same : row = target
  · subst row
    simp [Function.update, clearedInterval, MatrixOperations.clearColumn,
      MatrixOperations.addPivotRow, distinct, lower]
  · have unequal : row.val ≠ target.val := fun equal => same (Fin.ext equal)
    have before : row.val < target.val + 1 ↔ row.val < target.val := by omega
    simp [Function.update, same, clearedInterval, before]

/-- The intervals below and above the pivot together clear the entire column.
The second interval retains the rows already processed by the first. -/
theorem clearedInterval_join (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) :
    clearedInterval (clearedInterval matrix pivot column 0 pivot.val)
      pivot column (pivot.val + 1) rows = MatrixOperations.clearColumn matrix pivot column := by
  ext row other
  by_cases same : row = pivot
  · subst row
    simp [clearedInterval, MatrixOperations.clearColumn, MatrixOperations.addPivotRow]
  · have unequal : row.val ≠ pivot.val := fun equal => same (Fin.ext equal)
    by_cases below : row.val < pivot.val
    · have notAbove : ¬ pivot.val + 1 ≤ row.val := by omega
      simp [clearedInterval, notAbove, below]
    · have above : pivot.val + 1 ≤ row.val := by omega
      simp [clearedInterval, above, row.isLt, MatrixOperations.clearColumn,
        MatrixOperations.addPivotRow, same, below]

/-- The encoded row machine realizes the next mathematical interval update.
The array coordinate and the ordinary matrix entry denote the same scalar. -/
theorem processed_interval_next (enumeration : Scalar ≃ Fin cardinality)
    (sizes : Fin 3 → ℕ) (sourceRow column : Fin (2 ^ sizes 0))
    (sourceValid : sourceRow.val < sizes 1) (columnValid : column.val < sizes 2)
    (start count : ℕ) (counterFits : count < 2 ^ sizes 0)
    (targetValid : count < sizes 1) (lower : start ≤ count)
    (distinct : count ≠ sourceRow.val)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) :
    let pivot : Fin (sizes 1) := ⟨sourceRow.val, sourceValid⟩
    let pivotColumn : Fin (sizes 2) := ⟨column.val, columnValid⟩
    let partialMatrix := clearedInterval matrix pivot pivotColumn start count
    let array := matrixEquiv sizes partialMatrix
    StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
      (StandardGaussJordanClearTarget.additionOperation enumeration)
      sizes sourceRow ⟨count, counterFits⟩ sourceValid targetValid
      (Neg.neg (α := Scalar) (array ⟨count * sizes 2 + column.val,
        StandardMatrixEntry.index_lt sizes count column.val targetValid columnValid⟩))
      array (sizes 2) = matrixEquiv sizes
        (clearedInterval matrix pivot pivotColumn start (count + 1)) := by
  intro pivot pivotColumn partialMatrix array
  let target : Fin (sizes 1) := ⟨count, targetValid⟩
  have indexEq := matrixIndex_eq sizes target pivotColumn
  have valueEq : array ⟨count * sizes 2 + column.val,
      StandardMatrixEntry.index_lt sizes count column.val targetValid columnValid⟩ =
      partialMatrix target pivotColumn := by
    change matrixEquiv sizes partialMatrix _ = _
    rw [← indexEq]
    exact matrixEquiv_apply sizes partialMatrix target pivotColumn
  rw [valueEq]
  let coefficient : Scalar := -partialMatrix target pivotColumn
  have computed := processed_eq_matrix false (FieldRow.scalarDomain enumeration)
    (StandardGaussJordanClearTarget.additionOperation enumeration) sizes sourceRow
    ⟨count, counterFits⟩ sourceValid targetValid coefficient partialMatrix (sizes 2) (le_refl _)
  have complete := MatrixRows.processedColumns_complete false
    (StandardGaussJordanClearTarget.additionOperation enumeration Empty.elim)
    coefficient partialMatrix pivot target
  have transformed : MatrixRows.transform false
      (StandardGaussJordanClearTarget.additionOperation enumeration Empty.elim)
      coefficient partialMatrix pivot target =
      Function.update partialMatrix target (fun other => partialMatrix target other +
        coefficient * partialMatrix pivot other) :=
    MatrixRowField.add_transform coefficient partialMatrix pivot target
  have next := clearedInterval_next matrix pivot target pivotColumn start lower
    (fun equal => distinct (congrArg Fin.val equal))
  exact computed.trans (congrArg (matrixEquiv sizes)
    (complete.trans (transformed.trans next)))

/-- The interval controller computes the ordinary matrix operation on exactly
the selected non-pivot rows. Its private workspace is supplied by its caller. -/
theorem mathematical_loop_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : MultiTape.Tapes Alphabet)
      (sourceRow column start limit : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      limit.val ≤ sizes 1 → start.val ≤ limit.val →
      (limit.val ≤ sourceRow.val ∨ sourceRow.val < start.val) →
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
        initial name = encoded (domains enumeration name) sizes value) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (machine enumeration) ticks (entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial (exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (clearedInterval (Scalar := Scalar) matrix ⟨sourceRow.val, sourceValid⟩
            ⟨column.val, columnValid⟩ start.val limit.val) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨bound, execute⟩ := loop_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow column start limit sourceValid columnValid matrix limitWithin
    startWithin separated columnsFit capacity sourceEq counterEq columnEq matrixEq limitEq
    headers regions canonical
  let pivot : Fin (sizes 1) := ⟨sourceRow.val, sourceValid⟩
  let pivotColumn : Fin (sizes 2) := ⟨column.val, columnValid⟩
  let current := fun count => matrixEquiv (Carrier := Scalar) sizes
    (clearedInterval (Scalar := Scalar) matrix pivot pivotColumn start.val count)
  have updateLaw : ∀ count (before : count < limit.val), start.val ≤ count →
      StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
        (StandardGaussJordanClearTarget.additionOperation enumeration)
        sizes sourceRow ⟨count, lt_trans before limit.isLt⟩ sourceValid
        (lt_of_lt_of_le before limitWithin)
        (Neg.neg (α := Scalar) (current count
          ⟨count * sizes 2 + column.val, StandardMatrixEntry.index_lt sizes count
            column.val (lt_of_lt_of_le before limitWithin) columnValid⟩))
        (current count) (sizes 2) = current (count + 1) := by
    intro count before lower
    apply processed_interval_next enumeration sizes sourceRow column sourceValid columnValid
      start.val count (lt_trans before limit.isLt) (lt_of_lt_of_le before limitWithin) lower
      (by rcases separated with below | above <;> omega) matrix
  have initialMatrix : initial workingTape =
      encoded (domains enumeration workingTape) sizes (current start.val) := by
    change initial workingTape = encoded (domains enumeration workingTape) sizes
      (matrixEquiv (Carrier := Scalar) sizes matrix) at matrixEq
    simpa only [current, clearedInterval_start] using matrixEq
  exact execute sizes initial sourceRow column start limit sourceValid columnValid limitWithin
    startWithin current updateLaw columnsFit capacity sourceEq counterEq columnEq initialMatrix
    limitEq headers regions canonical

end Polytime2.StandardGaussJordanClearInterval

