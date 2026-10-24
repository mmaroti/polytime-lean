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

import Polytime2.Matrices.RowPairMath

/-! # Accumulating an integer Bézout row transformation

The input is a current rectangular matrix and the accumulated left change of
basis. Both matrices receive the same two-row transformation, whose coefficients
are computed from the current matrix alone. This preserves the equation with the
original matrix and any accumulated right change of basis. No invertibility of
the rectangular matrix is required.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row]

/-- Update the current matrix and its left transformation with shared coefficients. -/
def bezoutRowsWithLeft (first second : Row) (column : Column)
    (current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    Matrix Row Column ℤ × Matrix Row Row ℤ :=
  let coefficients := bezoutMatrix (current first column) (current second column)
  (rowPair first second coefficients current, rowPair first second coefficients left)

/-- The updated left matrix continues to describe the actual current matrix. -/
theorem bezoutRowsWithLeft_equation [Fintype Row] [Fintype Column] (first second : Row) (column : Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (right : Matrix Column Column ℤ) (equation : left * original * right = current) :
    (bezoutRowsWithLeft first second column current left).2 * original * right =
      (bezoutRowsWithLeft first second column current left).1 := by
  dsimp only [bezoutRowsWithLeft]
  rw [rowPair_eq_mul first second _ left, rowPair_eq_mul first second _ current]
  simpa only [Matrix.mul_assoc] using congrArg
    (fun matrix => rowPair first second
      (bezoutMatrix (current first column) (current second column)) 1 * matrix) equation

/-- Accumulation preserves unimodularity of the left transformation. -/
theorem bezoutRowsWithLeft_unimodular [Fintype Row] (first second : Row) (different : first ≠ second)
    (column : Column) (current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (leftUnit : IsUnit left.det) :
    IsUnit (bezoutRowsWithLeft first second column current left).2.det := by
  dsimp only [bezoutRowsWithLeft]
  rw [rowPair_eq_mul first second _ left, Matrix.det_mul]
  exact (rowPair_unimodular first second different _ (bezoutMatrix_det _ _)).mul leftUnit

/-- The accumulated update still performs the required gcd elimination. -/
theorem bezoutRowsWithLeft_eliminates (first second : Row) (different : first ≠ second)
    (column : Column) (current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    let updated := bezoutRowsWithLeft first second column current left
    updated.1 first column = (Int.gcd (current first column) (current second column) : ℤ) ∧
      updated.1 second column = 0 :=
  rowPair_bezout first second different current column

/-- The dual column update acts on the transpose of the accumulated right basis. -/
def bezoutColumnsWithRight [DecidableEq Column] (first second : Column) (row : Row)
    (current : Matrix Row Column ℤ) (right : Matrix Column Column ℤ) :
    Matrix Row Column ℤ × Matrix Column Column ℤ :=
  let updated := bezoutRowsWithLeft first second row current.transpose right.transpose
  (updated.1.transpose, updated.2.transpose)

/-- Right accumulation preserves the same original-to-current transformation equation. -/
theorem bezoutColumnsWithRight_equation [DecidableEq Column] [Fintype Row] [Fintype Column]
    (first second : Column) (row : Row) (original current : Matrix Row Column ℤ)
    (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = current) :
    left * original * (bezoutColumnsWithRight first second row current right).2 =
      (bezoutColumnsWithRight first second row current right).1 := by
  have transposed : right.transpose * original.transpose * left.transpose = current.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose equation
  have updated := bezoutRowsWithLeft_equation first second row original.transpose current.transpose
    right.transpose left.transpose transposed
  simpa only [bezoutColumnsWithRight, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc] using congrArg Matrix.transpose updated

/-- Right accumulation preserves unimodularity, including for singular current matrices. -/
theorem bezoutColumnsWithRight_unimodular [DecidableEq Column] [Fintype Column]
    (first second : Column) (different : first ≠ second) (row : Row)
    (current : Matrix Row Column ℤ) (right : Matrix Column Column ℤ)
    (rightUnit : IsUnit right.det) :
    IsUnit (bezoutColumnsWithRight first second row current right).2.det := by
  simpa only [bezoutColumnsWithRight, Matrix.det_transpose] using
    bezoutRowsWithLeft_unimodular first second different row current.transpose right.transpose
      (by simpa only [Matrix.det_transpose] using rightUnit)

end Polytime2.IntegerMatrix
