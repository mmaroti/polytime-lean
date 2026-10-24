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

import Polytime2.Matrices.BezoutMath
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Simultaneous transformations of two integer rows

Both new rows are linear combinations of the original two rows. Distinct row
indices give the usual left multiplication by an embedded two-by-two matrix.
A determinant-one coefficient matrix induces a unimodular transformation on
the whole rectangular matrix. The output magnitude width is derived internally.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row]

/-- Replace two rows simultaneously, reading both rows from the original matrix. -/
def rowPair (first second : Row) (coefficients : Matrix (Fin 2) (Fin 2) ℤ)
    (matrix : Matrix Row Column ℤ) : Matrix Row Column ℤ :=
  (matrix.updateRow first (fun column =>
    coefficients 0 0 * matrix first column + coefficients 0 1 * matrix second column)).updateRow second
      (fun column => coefficients 1 0 * matrix first column + coefficients 1 1 * matrix second column)

/-- Combining two zero entries preserves the entire column. -/
theorem rowPair_zero_column (first second : Row) (coefficients : Matrix (Fin 2) (Fin 2) ℤ)
    (matrix : Matrix Row Column ℤ) (column : Column)
    (firstZero : matrix first column = 0) (secondZero : matrix second column = 0) (row : Row) :
    rowPair first second coefficients matrix row column = matrix row column := by
  by_cases atSecond : row = second
  · subst row
    simp [rowPair, firstZero, secondZero]
  · by_cases atFirst : row = first
    · subst row
      simp [rowPair, Matrix.updateRow_ne atSecond, firstZero, secondZero]
    · simp [rowPair, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst]

theorem rowPair_one (first second : Row) (matrix : Matrix Row Column ℤ) :
    rowPair first second 1 matrix = matrix := by
  simp [rowPair]

theorem rowPair_comp (first second : Row) (different : first ≠ second)
    (outer inner : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ) :
    rowPair first second outer (rowPair first second inner matrix) =
      rowPair first second (outer * inner) matrix := by
  ext row column
  by_cases atSecond : row = second
  · subst row
    simp [rowPair, Matrix.updateRow_ne different, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  · by_cases atFirst : row = first
    · subst row
      simp [rowPair, Matrix.updateRow_ne different, Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    · simp [rowPair, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst]

theorem rowPair_eq_mul [Fintype Row] (first second : Row)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ) :
    rowPair first second coefficients matrix = rowPair first second coefficients 1 * matrix := by
  ext row column
  by_cases atSecond : row = second
  · subst row
    simp [rowPair, Matrix.mul_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib]
  · by_cases atFirst : row = first
    · subst row
      simp [rowPair, Matrix.updateRow_ne atSecond, Matrix.mul_apply, Matrix.one_apply,
        add_mul, Finset.sum_add_distrib]
    · simp [rowPair, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst,
        Matrix.mul_apply, Matrix.one_apply]

/-- A determinant-one local row operation lifts to an integer-unimodular matrix. -/
theorem rowPair_unimodular [Fintype Row] (first second : Row) (different : first ≠ second)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (determinant : coefficients.det = 1) :
    IsUnit (rowPair first second coefficients (1 : Matrix Row Row ℤ)).det := by
  have inverse : rowPair first second coefficients (1 : Matrix Row Row ℤ) *
      rowPair first second coefficients.adjugate (1 : Matrix Row Row ℤ) = 1 := by
    rw [← rowPair_eq_mul, rowPair_comp first second different, Matrix.mul_adjugate,
      determinant, one_smul, rowPair_one]
  apply isUnit_iff_dvd_one.mpr
  refine ⟨(rowPair first second coefficients.adjugate (1 : Matrix Row Row ℤ)).det, ?_⟩
  rw [← Matrix.det_mul, inverse, Matrix.det_one]

theorem rowPair_bound_of_widths (coefficientWidth matrixWidth : ℕ) (first second : Row)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ)
    (coefficientBound : ∀ row column, (coefficients row column).natAbs < 2 ^ coefficientWidth)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ matrixWidth) :
    ∀ row column, (rowPair first second coefficients matrix row column).natAbs < 2 ^ (coefficientWidth + matrixWidth + 1) := by
  intro row column
  by_cases atSecond : row = second
  · subst row
    simpa only [rowPair, Matrix.updateRow_self] using
      IntegerArithmetic.twoProducts_bound_of_widths coefficientWidth matrixWidth _ _ _ _ (coefficientBound 1 0) (matrixBound first column)
        (coefficientBound 1 1) (matrixBound second column)
  · by_cases atFirst : row = first
    · subst row
      simpa only [rowPair, Matrix.updateRow_ne atSecond, Matrix.updateRow_self] using
        IntegerArithmetic.twoProducts_bound_of_widths coefficientWidth matrixWidth _ _ _ _ (coefficientBound 0 0) (matrixBound first column)
          (coefficientBound 0 1) (matrixBound second column)
    · rw [rowPair, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst]
      exact (matrixBound row column).trans_le (pow_le_pow_right₀ (by decide) (by omega))

/-- Equal-width callers share the same two-row bound. -/
theorem rowPair_bound (width : ℕ) (first second : Row)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ)
    (coefficientBound : ∀ row column, (coefficients row column).natAbs < 2 ^ width)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (rowPair first second coefficients matrix row column).natAbs < 2 ^ (2 * width + 1) := by
  simpa only [two_mul] using rowPair_bound_of_widths width width first second coefficients matrix
    coefficientBound matrixBound

/-- The Bézout specialization eliminates the selected entry without changing other rows. -/
theorem rowPair_bezout (first second : Row) (different : first ≠ second)
    (matrix : Matrix Row Column ℤ) (column : Column) :
    let result := rowPair first second (bezoutMatrix (matrix first column) (matrix second column)) matrix
    result first column = (Int.gcd (matrix first column) (matrix second column) : ℤ) ∧
      result second column = 0 := by
  have elimination := bezoutMatrix_eliminates (matrix first column) (matrix second column)
  constructor
  · have entry := congrFun elimination 0
    simpa [rowPair, Matrix.updateRow_ne different, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using entry
  · have entry := congrFun elimination 1
    simpa [rowPair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using entry

/-- Apply a right two-by-two transformation to two columns of the original matrix. -/
def columnPair [DecidableEq Column] (first second : Column)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ) : Matrix Row Column ℤ :=
  (rowPair first second coefficients.transpose matrix.transpose).transpose

omit [DecidableEq Row] in
/-- The column operation is right multiplication by the embedded coefficient matrix. -/
theorem columnPair_eq_mul [DecidableEq Column] [Fintype Column] (first second : Column)
    (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ) :
    columnPair first second coefficients matrix = matrix *
      (rowPair first second coefficients.transpose (1 : Matrix Column Column ℤ)).transpose := by
  have equation := congrArg Matrix.transpose (rowPair_eq_mul first second coefficients.transpose matrix.transpose)
  simpa only [columnPair, Matrix.transpose_mul, Matrix.transpose_transpose] using equation

end Polytime2.IntegerMatrix
