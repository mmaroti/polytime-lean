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
import Polytime2.Arithmetic.SignedBounds

/-! # Integer row and column additions

The input is an ordinary rectangular integer matrix, a target index, a source
index, and an integer coefficient. The result adds the indicated multiple of
the source to the target. Distinct indices give a unimodular transformation.
If matrix entries and the coefficient have magnitude width `w`, the result
has magnitude width `2*w+1`, independently of numeric magnitudes.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- Add an integer multiple of one row to another. -/
def rowAdd (target source : Row) (coefficient : ℤ) (matrix : Matrix Row Column ℤ) :
    Matrix Row Column ℤ :=
  Matrix.updateRow matrix target (fun column => matrix target column + coefficient * matrix source column)

omit [DecidableEq Column] in
/-- A zero source entry keeps the entire corresponding column fixed. -/
theorem rowAdd_zero_column (target source : Row) (coefficient : ℤ) (matrix : Matrix Row Column ℤ)
    (column : Column) (zero : matrix source column = 0) (row : Row) :
    rowAdd target source coefficient matrix row column = matrix row column := by
  by_cases same : row = target
  · subst row; simp only [rowAdd, Matrix.updateRow_self, zero, mul_zero, add_zero]
  · simp only [rowAdd, Matrix.updateRow_ne same]

/-- Column addition reuses row addition through transposition. -/
def columnAdd (target source : Column) (coefficient : ℤ) (matrix : Matrix Row Column ℤ) :
    Matrix Row Column ℤ :=
  (rowAdd target source coefficient matrix.transpose).transpose

omit [DecidableEq Column] in
theorem rowAdd_eq_mul [Fintype Row] (target source : Row) (coefficient : ℤ)
    (matrix : Matrix Row Column ℤ) :
    rowAdd target source coefficient matrix = Matrix.transvection target source coefficient * matrix := by
  ext row column
  by_cases same : row = target
  · subst row
    simp [rowAdd]
  · simp [rowAdd, Matrix.updateRow_ne same,
      Matrix.transvection_mul_apply_of_ne target source row column same]

theorem rowAdd_unimodular [Fintype Row] (target source : Row) (different : target ≠ source)
    (coefficient : ℤ) : (Matrix.transvection target source coefficient).det = 1 :=
  Matrix.det_transvection_of_ne target source different coefficient

omit [DecidableEq Row] in
theorem columnAdd_eq_mul [Fintype Column] (target source : Column) (coefficient : ℤ)
    (matrix : Matrix Row Column ℤ) :
    columnAdd target source coefficient matrix = matrix * Matrix.transvection source target coefficient := by
  ext row column
  by_cases same : column = target
  · subst column
    simp [columnAdd, rowAdd]
  · simp [columnAdd, rowAdd, Matrix.updateRow_ne same,
      Matrix.mul_transvection_apply_of_ne source target row column same]

omit [DecidableEq Column] in
/-- Row addition accepts independent coefficient and matrix widths. -/
theorem rowAdd_bound_of_widths (coefficientWidth matrixWidth : ℕ) (target source : Row) (coefficient : ℤ)
    (matrix : Matrix Row Column ℤ)
    (coefficientBound : coefficient.natAbs < 2 ^ coefficientWidth)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ matrixWidth) :
    ∀ row column, (rowAdd target source coefficient matrix row column).natAbs <
      2 ^ (coefficientWidth + matrixWidth + 1) := by
  intro row column
  by_cases same : row = target
  · subst row
    simpa only [rowAdd, Matrix.updateRow_self] using
      IntegerArithmetic.multiplyAdd_bound_of_widths coefficientWidth matrixWidth _ _ _
        (matrixBound target column) coefficientBound (matrixBound source column)
  · rw [rowAdd, Matrix.updateRow_ne same]
    exact (matrixBound row column).trans_le
      (pow_le_pow_right₀ (by decide) (by omega))

omit [DecidableEq Column] in
/-- Equal-width row addition specializes the heterogeneous bound. -/
theorem rowAdd_bound (width : ℕ) (target source : Row) (coefficient : ℤ)
    (matrix : Matrix Row Column ℤ)
    (coefficientBound : coefficient.natAbs < 2 ^ width)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (rowAdd target source coefficient matrix row column).natAbs < 2 ^ (2 * width + 1) := by
  simpa only [two_mul] using rowAdd_bound_of_widths width width target source coefficient matrix
    coefficientBound matrixBound

omit [DecidableEq Row] in
theorem columnAdd_bound (width : ℕ) (target source : Column) (coefficient : ℤ)
    (matrix : Matrix Row Column ℤ)
    (coefficientBound : coefficient.natAbs < 2 ^ width)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (columnAdd target source coefficient matrix row column).natAbs < 2 ^ (2 * width + 1) :=
  fun row column => rowAdd_bound width target source coefficient matrix.transpose coefficientBound
    (fun column row => matrixBound row column) column row


omit [DecidableEq Row] [DecidableEq Column] in
/-- Matrix-vector multiplication derives a polynomial magnitude width from the
operand widths and the mathematical number of columns. -/
theorem mulVec_bound [Fintype Column] (matrixWidth valueWidth : ℕ)
    (matrix : Matrix Row Column ℤ) (values : Column → ℤ)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ matrixWidth)
    (valueBound : ∀ column, (values column).natAbs < 2 ^ valueWidth) (row : Row) :
    (matrix.mulVec values row).natAbs <
      2 ^ (matrixWidth + valueWidth + Fintype.card Column + 1) := by
  classical
  calc
    (matrix.mulVec values row).natAbs ≤ ∑ column, (matrix row column * values column).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _column : Column, 2 ^ matrixWidth * 2 ^ valueWidth := by
      apply Finset.sum_le_sum
      intro column _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (matrixBound row column).le (valueBound column).le
    _ = Fintype.card Column * 2 ^ (matrixWidth + valueWidth) := by simp [pow_add]
    _ < 2 ^ (Fintype.card Column + 1) * 2 ^ (matrixWidth + valueWidth) := by
      apply Nat.mul_lt_mul_of_pos_right
      · exact (Nat.le_succ _).trans_lt Nat.lt_two_pow_self
      · positivity
    _ = 2 ^ (matrixWidth + valueWidth + Fintype.card Column + 1) := by
      rw [← pow_add]
      congr 1
      omega

omit [DecidableEq Row] [DecidableEq Column] in
/-- Matrix multiplication reuses the matrix-vector bound column by column. -/
theorem mul_bound {Inner : Type} [Fintype Inner] (leftWidth rightWidth : ℕ)
    (left : Matrix Row Inner ℤ) (right : Matrix Inner Column ℤ)
    (leftBound : ∀ row index, (left row index).natAbs < 2 ^ leftWidth)
    (rightBound : ∀ index column, (right index column).natAbs < 2 ^ rightWidth) :
    ∀ row column, ((left * right) row column).natAbs < 2 ^ (leftWidth + rightWidth + Fintype.card Inner + 1) := by
  intro row column
  exact mulVec_bound leftWidth rightWidth left (fun index => right index column)
    leftBound (fun index => rightBound index column) row

end Polytime2.IntegerMatrix
