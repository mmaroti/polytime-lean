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

import Polytime2.Matrices.HermiteSweepMath
import Polytime2.Matrices.PivotPermutationMath
import Polytime2.Matrices.PermutationTrackingMath

/-! # Compact row normalization with both transformations

The row traversal returns active row and column embeddings. Deterministic
permutations move them into the leading block, applying the same permutations
to the accumulated bases. The resulting matrix has a positive normalized upper
triangular leading block and zero inactive rows, with polynomial entry widths.
This is one row normalization, not the alternating Smith normalization schedule.
-/

namespace Polytime2.IntegerMatrix

/-- A normalized leading pivot block and zero rows beyond its mathematical rank. -/
def IsCompactRowHermite {rows columns : ℕ} (rank : ℕ) (matrix : Matrix (Fin rows) (Fin columns) ℤ) : Prop :=
  ∃ rowBound : rank ≤ rows, ∃ columnBound : rank ≤ columns,
    (∀ row : Fin rows, rank ≤ row.val → matrix row = 0) ∧
    (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).IsUpperTriangular ∧
    (∀ index : Fin rank, 0 < matrix (Fin.castLE rowBound index) (Fin.castLE columnBound index)) ∧
    (∀ row column : Fin rank, row < column →
      0 ≤ matrix (Fin.castLE rowBound row) (Fin.castLE columnBound column) ∧
        matrix (Fin.castLE rowBound row) (Fin.castLE columnBound column) <
          matrix (Fin.castLE rowBound column) (Fin.castLE columnBound column))

/-- The active determinant is positive, including the rank-zero empty determinant. -/
theorem IsCompactRowHermite.det_pos {rows columns rank : ℕ} {matrix : Matrix (Fin rows) (Fin columns) ℤ}
    (normalized : IsCompactRowHermite rank matrix) (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) :
    0 < (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det := by
  obtain ⟨_, _, _, upper, positive, _⟩ := normalized
  rw [Matrix.det_of_isUpperTriangular upper]
  exact Finset.prod_pos (fun index _ => positive index)

/-- Compact the pivot embeddings, returning rank, the actual matrix, and both bases. -/
def compactHermiteRows {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    ℕ × Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let state := hermiteRowsSweep original
  ⟨state.2.1, permuteWithBases (pivotPermutation state.2.2.1) (pivotPermutation state.2.2.2)
    state.1.1 state.1.2 1⟩

/-- Compaction retains the presentation, both unit determinants, and the normalized leading block. -/
theorem compactHermiteRows_correct {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    let result := compactHermiteRows original
    result.2.2.1 * original * result.2.2.2 = result.2.1 ∧
      IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧ IsCompactRowHermite result.1 result.2.1 := by
  let state := hermiteRowsSweep original
  let rowPermutation := pivotPermutation state.2.2.1
  let columnPermutation := pivotPermutation state.2.2.2
  have rankBound := hermiteRowState_rank_le state
  have leadingRows (index) : rowPermutation (Fin.castLE rankBound.1 index) = state.2.2.1 index :=
    pivotPermutation_apply state.2.2.1 index
  have leadingColumns (index) : columnPermutation (Fin.castLE rankBound.2 index) = state.2.2.2 index :=
    pivotPermutation_apply state.2.2.2 index
  have invariant := hermiteRowsSweep_correct original
  obtain ⟨equation, unit, oldRows, support, upper, positive, reduced, basisSupport, future⟩ := invariant
  let result := permuteWithBases rowPermutation columnPermutation state.1.1 state.1.2 1
  change result.2.1 * original * result.2.2 = result.1 ∧
    IsUnit result.2.1.det ∧ IsUnit result.2.2.det ∧ IsCompactRowHermite state.2.1 result.1
  have preserved := permuteWithBases_preserves rowPermutation columnPermutation state.1.1 original state.1.2 1
    (by simpa only [Matrix.mul_one] using equation) unit (by simp)
  refine ⟨preserved.1, preserved.2.1, preserved.2.2, rankBound.1, rankBound.2, ?_, ?_, ?_, ?_⟩
  · intro row after
    funext column
    change state.1.1 (rowPermutation row) (columnPermutation column) = 0
    exact congrFun (support _ (rowPermutation row).isLt (pivotPermutation_outside state.2.2.1 row after)) _
  · intro row column below
    change state.1.1 (rowPermutation (Fin.castLE rankBound.1 row))
      (columnPermutation (Fin.castLE rankBound.2 column)) = 0
    rw [leadingRows, leadingColumns]
    exact upper below
  · intro index
    change 0 < state.1.1 (rowPermutation (Fin.castLE rankBound.1 index))
      (columnPermutation (Fin.castLE rankBound.2 index))
    rw [leadingRows, leadingColumns]
    exact positive index
  · intro row column before
    change 0 ≤ state.1.1 (rowPermutation (Fin.castLE rankBound.1 row))
        (columnPermutation (Fin.castLE rankBound.2 column)) ∧
      state.1.1 (rowPermutation (Fin.castLE rankBound.1 row)) (columnPermutation (Fin.castLE rankBound.2 column)) <
        state.1.1 (rowPermutation (Fin.castLE rankBound.1 column)) (columnPermutation (Fin.castLE rankBound.2 column))
    simp only [leadingRows, leadingColumns]
    exact reduced row column before

/-- Both transformations and the compact matrix retain original-input polynomial entry widths. -/
theorem compactHermiteRows_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    let result := compactHermiteRows original
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ (2 * (rows * (width + rows) + 1) + width + 2 * rows + 2)) ∧
    (∀ row column, (result.2.2.1 row column).natAbs < 2 ^ (1 + rows * hermiteSweepBasisIncrement rows width)) ∧
    (∀ row column, (result.2.2.2 row column).natAbs < 2 ^ 1) := by
  apply permuteWithBases_bound
  · exact hermiteRowsSweep_matrix_bound width original entryBound
  · exact hermiteRowsSweep_basis_bound width original entryBound
  · intro row column
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num

/-- The dual compact column normalization reuses the row traversal by transposition. -/
def compactHermiteColumns {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    ℕ × Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let result := compactHermiteRows original.transpose
  (result.1, result.2.1.transpose, result.2.2.2.transpose, result.2.2.1.transpose)

/-- Column normalization retains both actual bases and the transposed normalized-block contract. -/
theorem compactHermiteColumns_correct {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    let result := compactHermiteColumns original
    result.2.2.1 * original * result.2.2.2 = result.2.1 ∧
      IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧ IsCompactRowHermite result.1 result.2.1.transpose := by
  have correct := compactHermiteRows_correct original.transpose
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [compactHermiteColumns, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
      congrArg Matrix.transpose correct.1
  · simpa only [compactHermiteColumns, Matrix.det_transpose] using correct.2.2.1
  · simpa only [compactHermiteColumns, Matrix.det_transpose] using correct.2.1
  · simpa only [compactHermiteColumns, Matrix.transpose_transpose] using correct.2.2.2

/-- The dual widths exchange the dimension and accumulated-basis roles. -/
theorem compactHermiteColumns_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    let result := compactHermiteColumns original
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ (2 * (columns * (width + columns) + 1) + width + 2 * columns + 2)) ∧
    (∀ row column, (result.2.2.1 row column).natAbs < 2 ^ 1) ∧
    (∀ row column, (result.2.2.2 row column).natAbs < 2 ^ (1 + columns * hermiteSweepBasisIncrement columns width)) := by
  have bounded := compactHermiteRows_bound width original.transpose (fun row column => entryBound column row)
  exact ⟨fun row column => bounded.1 column row,
    fun row column => bounded.2.2 column row, fun row column => bounded.2.1 column row⟩

end Polytime2.IntegerMatrix
