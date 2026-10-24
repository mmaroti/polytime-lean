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

import Polytime2.Matrices.IntegerOperationsMath

/-! # Euclidean row reduction for Hermite sweeps

Given distinct source and target rows and a positive source entry in a chosen
column, subtract the integer quotient times the source row from the target.
The target entry becomes its Euclidean remainder, the source row is unchanged,
and columns where the source is zero remain unchanged. Apply the same row
operation to the accumulated left basis to retain the full presentation.
These are local statements; they do not assert global sweep growth bounds.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- Reduce a selected entry modulo the positive source pivot. -/
def rowRemainder (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ) : Matrix Row Column ℤ :=
  rowAdd target source (-(matrix target column / matrix source column)) matrix

/-- Apply the same quotient operation to the working matrix and its left basis. -/
def rowRemainderWithLeft (source target : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  (rowRemainder source target column matrix,
    rowAdd target source (-(matrix target column / matrix source column)) left)

theorem rowRemainder_entry (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ) :
    rowRemainder source target column matrix target column = matrix target column % matrix source column := by
  have division := Int.emod_add_mul_ediv (matrix target column) (matrix source column)
  simp only [rowRemainder, rowAdd, Matrix.updateRow_self]
  linear_combination -division

theorem rowRemainder_source (source target : Row) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (other : Column) :
    rowRemainder source target column matrix source other = matrix source other := by
  simp [rowRemainder, rowAdd, Matrix.updateRow_ne different]

theorem rowRemainder_range (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ)
    (positive : 0 < matrix source column) :
    0 ≤ rowRemainder source target column matrix target column ∧
      rowRemainder source target column matrix target column < matrix source column := by
  rw [rowRemainder_entry]
  exact ⟨Int.emod_nonneg _ (ne_of_gt positive), Int.emod_lt_of_pos _ positive⟩

/-- Earlier zero entries in the source prevent any disturbance of those columns. -/
theorem rowRemainder_zero_column (source target : Row) (column other : Column) (matrix : Matrix Row Column ℤ)
    (zero : matrix source other = 0) (row : Row) :
    rowRemainder source target column matrix row other = matrix row other :=
  rowAdd_zero_column target source _ matrix other zero row

/-- Divisible entries are cancelled without changing the pivot row. -/
theorem rowRemainder_divisible (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ)
    (divides : matrix source column ∣ matrix target column) :
    rowRemainder source target column matrix target column = 0 := by
  rw [rowRemainder_entry]
  exact Int.emod_eq_zero_of_dvd divides

theorem rowRemainderWithLeft_equation [Fintype Row] [Fintype Column]
    (source target : Row) (column : Column) (matrix original : Matrix Row Column ℤ)
    (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) :
    (rowRemainderWithLeft source target column matrix left).2 * original * right =
      (rowRemainderWithLeft source target column matrix left).1 := by
  simp only [rowRemainderWithLeft, rowRemainder, rowAdd_eq_mul, Matrix.mul_assoc]
  have associated : left * (original * right) = matrix := by simpa only [Matrix.mul_assoc] using equation
  rw [associated]

theorem rowRemainderWithLeft_unimodular [Fintype Row] (source target : Row) (different : source ≠ target)
    (column : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (unit : IsUnit left.det) :
    IsUnit (rowRemainderWithLeft source target column matrix left).2.det := by
  simp only [rowRemainderWithLeft, rowAdd_eq_mul, Matrix.det_mul,
    rowAdd_unimodular target source different.symm, one_mul]
  exact unit

/-- Column reduction reuses the row operation and tracks the right basis. -/
def columnRemainderWithRight (source target : Column) (row : Row)
    (matrix : Matrix Row Column ℤ) (right : Matrix Column Column ℤ) : Matrix Row Column ℤ × Matrix Column Column ℤ :=
  let changed := rowRemainderWithLeft source target row matrix.transpose right.transpose
  (changed.1.transpose, changed.2.transpose)

theorem columnRemainderWithRight_equation [Fintype Row] [Fintype Column]
    (source target : Column) (row : Row) (matrix original : Matrix Row Column ℤ)
    (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) :
    left * original * (columnRemainderWithRight source target row matrix right).2 =
      (columnRemainderWithRight source target row matrix right).1 := by
  have transposed : right.transpose * original.transpose * left.transpose = matrix.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose equation
  have changed := rowRemainderWithLeft_equation source target row matrix.transpose original.transpose
    right.transpose left.transpose transposed
  simpa only [columnRemainderWithRight, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
    congrArg Matrix.transpose changed

theorem columnRemainderWithRight_unimodular [Fintype Column] (source target : Column) (different : source ≠ target)
    (row : Row) (matrix : Matrix Row Column ℤ) (right : Matrix Column Column ℤ) (unit : IsUnit right.det) :
    IsUnit (columnRemainderWithRight source target row matrix right).2.det := by
  rw [columnRemainderWithRight, Matrix.det_transpose]
  exact rowRemainderWithLeft_unimodular source target different row matrix.transpose right.transpose
    (by simpa only [Matrix.det_transpose] using unit)

end Polytime2.IntegerMatrix
