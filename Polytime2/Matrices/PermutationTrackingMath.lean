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

/-! # Permuting an integer presentation with its actual bases

Permute current rows and columns. Apply the same row permutation to the left
basis and the same column permutation to the right basis. The presentation and
both unimodularity proofs are preserved, with no change in entry widths.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type}

/-- Reindex the matrix and its two accumulated transformations together. -/
def permuteWithBases (rows : Equiv.Perm Row) (columns : Equiv.Perm Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ) :
    Matrix Row Column ℤ × Matrix Row Row ℤ × Matrix Column Column ℤ :=
  (matrix.submatrix rows columns, left.submatrix rows id, right.submatrix id columns)

/-- Row and column permutation retain the full presentation and unit determinants. -/
theorem permuteWithBases_preserves [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (rows : Equiv.Perm Row) (columns : Equiv.Perm Column)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) :
    (permuteWithBases rows columns matrix left right).2.1 * original *
        (permuteWithBases rows columns matrix left right).2.2 = (permuteWithBases rows columns matrix left right).1 ∧
      IsUnit (permuteWithBases rows columns matrix left right).2.1.det ∧
      IsUnit (permuteWithBases rows columns matrix left right).2.2.det := by
  have first : left.submatrix rows id * original = (left * original).submatrix rows id := by
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv left original rows (Equiv.refl Row) id
  have second : (left * original).submatrix rows id * right.submatrix id columns =
      (left * original * right).submatrix rows columns := by
    simpa only [Equiv.coe_refl] using
      Matrix.submatrix_mul_equiv (left * original) right rows (Equiv.refl Column) columns
  refine ⟨?_, ?_, ?_⟩
  · change left.submatrix rows id * original * right.submatrix id columns = matrix.submatrix rows columns
    rw [first, second, equation]
  · change IsUnit (left.submatrix rows id).det
    rw [Matrix.det_permute]
    exact (Units.isUnit _).mul leftUnit
  · change IsUnit (right.submatrix id columns).det
    rw [Matrix.det_permute']
    exact (Units.isUnit _).mul rightUnit

/-- Reindexing introduces no coefficient growth in the matrix or either basis. -/
theorem permuteWithBases_bound (matrixWidth leftWidth rightWidth : ℕ)
    (rows : Equiv.Perm Row) (columns : Equiv.Perm Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ matrixWidth)
    (leftBound : ∀ row column, (left row column).natAbs < 2 ^ leftWidth)
    (rightBound : ∀ row column, (right row column).natAbs < 2 ^ rightWidth) :
    (∀ row column, ((permuteWithBases rows columns matrix left right).1 row column).natAbs < 2 ^ matrixWidth) ∧
    (∀ row column, ((permuteWithBases rows columns matrix left right).2.1 row column).natAbs < 2 ^ leftWidth) ∧
    (∀ row column, ((permuteWithBases rows columns matrix left right).2.2 row column).natAbs < 2 ^ rightWidth) :=
  ⟨fun row column => matrixBound (rows row) (columns column),
    fun row column => leftBound (rows row) column,
    fun row column => rightBound row (columns column)⟩

end Polytime2.IntegerMatrix
