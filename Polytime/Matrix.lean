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

import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.Tactic

/-! # Executable finite-field row operations

Matrices retain their exact rectangular shape. Row equivalence is Mathlib's
left action by an invertible matrix, rather than only equality of row spaces.
-/

namespace Polytime.MatrixOperations

-- scalarLevel: the mathematical field carrier.
universe scalarLevel
variable {Scalar : Type scalarLevel} [Field Scalar]
variable {rows columns : ℕ}

/-- Exchange rows using only indexed entry reads. -/
def swapRows (matrix : Matrix (Fin rows) (Fin columns) Scalar) (first second : Fin rows) :
    Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  matrix (Equiv.swap first second row) column

/-- Scale a single row; the correctness theorem requires a nonzero coefficient. -/
def scaleRow (matrix : Matrix (Fin rows) (Fin columns) Scalar) (target : Fin rows)
    (coefficient : Scalar) : Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  if row = target then coefficient * matrix row column else matrix row column

/-- Add multiples of one pivot row to the other rows. -/
def addPivotRow (matrix : Matrix (Fin rows) (Fin columns) Scalar) (pivot : Fin rows)
    (coefficients : Fin rows → Scalar) : Matrix (Fin rows) (Fin columns) Scalar :=
  fun row column => matrix row column + coefficients row * matrix pivot column

private def combination (pivot : Fin rows) (coefficients : Fin rows → Scalar) :
    Matrix (Fin rows) (Fin rows) Scalar := fun row column =>
  (if row = column then 1 else 0) + (if column = pivot then coefficients row else 0)

private theorem combination_mul (pivot : Fin rows) (coefficients : Fin rows → Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    combination pivot coefficients * matrix = addPivotRow matrix pivot coefficients := by
  ext row column
  simp [Matrix.mul_apply, combination, addPivotRow, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem combination_inverse (pivot : Fin rows) (coefficients : Fin rows → Scalar)
    (pivotZero : coefficients pivot = 0) :
    combination pivot coefficients * combination pivot (fun row => -coefficients row) = 1 := by
  rw [combination_mul]
  ext row column
  simp only [addPivotRow, combination, pivotZero, neg_zero, ite_self, add_zero, Matrix.one_apply]
  by_cases equal : column = pivot
  · subst column; simp
  · simp [equal, Ne.symm equal]

/-- The simultaneous row additions have an explicit invertible realization. -/
theorem addPivotRow_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (coefficients : Fin rows → Scalar) (pivotZero : coefficients pivot = 0) :
    Matrix.RowEquivalent matrix (addPivotRow matrix pivot coefficients) := by
  let transformation : Matrix.GeneralLinearGroup (Fin rows) Scalar :=
    { val := combination pivot coefficients
      inv := combination pivot (fun row => -coefficients row)
      val_inv := combination_inverse pivot coefficients pivotZero
      inv_val := by
        simpa only [neg_neg] using combination_inverse pivot (fun row => -coefficients row)
          (by simp [pivotZero]) }
  refine ⟨transformation, ?_⟩
  exact combination_mul pivot coefficients matrix

/-- Adding a multiple of a distinct source row preserves row equivalence. -/
theorem addRow_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (coefficient : Scalar) (distinct : source ≠ target) :
    Matrix.RowEquivalent matrix (Function.update matrix target
      (fun column => matrix target column + coefficient * matrix source column)) := by
  classical
  have equality : addPivotRow matrix source (Function.update (fun _ => 0) target coefficient) =
      Function.update matrix target
        (fun column => matrix target column + coefficient * matrix source column) := by
    funext row column
    by_cases same : row = target <;> simp [addPivotRow, Function.update, same]
  rw [← equality]
  exact addPivotRow_rowEquivalent matrix source _ (by simp [Function.update, distinct])

theorem swapRows_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (first second : Fin rows) : Matrix.RowEquivalent matrix (swapRows matrix first second) := by
  have equality : Matrix.swap Scalar first second * matrix = swapRows matrix first second := by
    ext row column
    by_cases atFirst : row = first
    · subst row; simp [swapRows]
    by_cases atSecond : row = second
    · subst row; simp [swapRows]
    simp [Matrix.swap_mul_of_ne atFirst atSecond, swapRows,
      Equiv.swap_apply_of_ne_of_ne atFirst atSecond]
  rw [← equality]
  exact Matrix.rowEquivalent_swap matrix first second

theorem scaleRow_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target : Fin rows) (coefficient : Scalar) (nonzero : coefficient ≠ 0) :
    Matrix.RowEquivalent matrix (scaleRow matrix target coefficient) := by
  have equality : Matrix.rowScale target coefficient * matrix = scaleRow matrix target coefficient := by
    rw [Matrix.rowScale_mul]
    ext row column
    by_cases same : row = target <;> simp [Matrix.updateRow_apply, scaleRow, Matrix.row,
      Pi.smul_apply, smul_eq_mul, same]
  rw [← equality]
  exact Matrix.rowEquivalent_rowScale matrix target (Units.mk0 coefficient nonzero)

/-- Eliminate the pivot column without changing the normalized pivot row. -/
def clearColumn (matrix : Matrix (Fin rows) (Fin columns) Scalar) (pivot : Fin rows)
    (column : Fin columns) : Matrix (Fin rows) (Fin columns) Scalar :=
  addPivotRow matrix pivot (fun row => if row = pivot then 0 else -matrix row column)

theorem clearColumn_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) :
    Matrix.RowEquivalent matrix (clearColumn matrix pivot column) :=
  addPivotRow_rowEquivalent matrix pivot _ (by simp)

@[simp] theorem clearColumn_pivot (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column other : Fin columns) :
    clearColumn matrix pivot column pivot other = matrix pivot other := by
  simp [clearColumn, addPivotRow]

theorem clearColumn_zero (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot row : Fin rows) (column : Fin columns) (normalized : matrix pivot column = 1)
    (otherRow : row ≠ pivot) : clearColumn matrix pivot column row column = 0 := by
  simp [clearColumn, addPivotRow, otherRow, normalized]

theorem clearColumn_preserves_column (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column other : Fin columns) (zero : matrix pivot other = 0) :
    ∀ row, clearColumn matrix pivot column row other = matrix row other := by
  intro row
  simp [clearColumn, addPivotRow, zero]

/-- One nonzero pivot: swap, normalize, then clear every other row. -/
def pivotStep (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target source : Fin rows) (column : Fin columns) : Matrix (Fin rows) (Fin columns) Scalar :=
  let swapped := swapRows matrix target source
  clearColumn (scaleRow swapped target (matrix source column)⁻¹) target column

theorem pivotStep_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target source : Fin rows) (column : Fin columns) (nonzero : matrix source column ≠ 0) :
    Matrix.RowEquivalent matrix (pivotStep matrix target source column) := by
  exact (swapRows_rowEquivalent matrix target source).trans
    ((scaleRow_rowEquivalent (swapRows matrix target source) target _ (inv_ne_zero nonzero)).trans
      (clearColumn_rowEquivalent _ target column))

@[simp] theorem pivotStep_pivot (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target source : Fin rows) (column : Fin columns) (nonzero : matrix source column ≠ 0) :
    pivotStep matrix target source column target column = 1 := by
  simp [pivotStep, scaleRow, swapRows, nonzero]

theorem pivotStep_zero (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target source row : Fin rows) (column : Fin columns) (nonzero : matrix source column ≠ 0)
    (otherRow : row ≠ target) : pivotStep matrix target source column row column = 0 := by
  apply clearColumn_zero _ target row column _ otherRow
  simp [scaleRow, swapRows, nonzero]

/-- Earlier columns are unchanged when both exchanged rows vanish there. -/
theorem pivotStep_preserves_column (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (target source : Fin rows) (column other : Fin columns)
    (targetZero : matrix target other = 0) (sourceZero : matrix source other = 0) :
    ∀ row, pivotStep matrix target source column row other = matrix row other := by
  intro row
  have swapPreserves : ∀ row, swapRows matrix target source row other = matrix row other := by
    intro row
    by_cases atTarget : row = target
    · subst row; simp [swapRows, targetZero, sourceZero]
    by_cases atSource : row = source
    · subst row; simp [swapRows, targetZero, sourceZero]
    simp [swapRows, Equiv.swap_apply_of_ne_of_ne atTarget atSource]
  by_cases atTarget : row = target
  · subst row; simp [pivotStep, clearColumn, addPivotRow, scaleRow, swapPreserves, targetZero]
  · simp [pivotStep, clearColumn, addPivotRow, scaleRow, swapPreserves, targetZero, atTarget]

end Polytime.MatrixOperations
