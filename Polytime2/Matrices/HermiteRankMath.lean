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

import Polytime2.Matrices.CompactHermiteMath
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Rank preservation for compact Hermite passes

A normalized positive triangular leading block gives a nonzero minor of its
reported rank. Zero inactive rows give the matching upper bound. Thus the
reported rank is Mathlib's matrix rank over the integers, and unimodular
presentation changes preserve it across row and column normalization.
-/

namespace Polytime2.IntegerMatrix

/-- The compact-block contract determines the ordinary matrix rank. -/
theorem IsCompactRowHermite.rank_eq {rows columns rank : ℕ} {matrix : Matrix (Fin rows) (Fin columns) ℤ}
    (normalized : IsCompactRowHermite rank matrix) : matrix.rank = rank := by
  have compact := normalized
  obtain ⟨rowBound, columnBound, zero, _, _, _⟩ := normalized
  have nonzero : (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det ≠ 0 :=
    ne_of_gt (compact.det_pos rowBound columnBound)
  have blockRank : (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).rank = rank := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero nonzero
  have lower := Matrix.rank_submatrix_le matrix (Fin.castLE rowBound) (Fin.castLE columnBound)
  rw [blockRank] at lower
  let active : Finset (Fin rows) := Finset.univ.image (Fin.castLE rowBound)
  have card : active.card = rank := by
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective rowBound), Finset.card_univ, Fintype.card_fin]
  have supported : Function.support matrix.row ⊆ active := by
    rw [Function.support_subset_iff']
    intro row outside
    apply zero row
    by_contra before
    have rowLt : row.val < rank := by omega
    apply outside
    exact Finset.mem_image.mpr ⟨⟨row.val, rowLt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have higher := Matrix.rank_le_card_of_support_subset matrix active supported
  rw [card] at higher
  exact le_antisymm higher lower

/-- The transpose of a compact block has the same rank over the integers. -/
theorem IsCompactRowHermite.transpose_rank_eq {rows columns rank : ℕ} {matrix : Matrix (Fin rows) (Fin columns) ℤ}
    (normalized : IsCompactRowHermite rank matrix) : matrix.transpose.rank = rank := by
  have compact := normalized
  obtain ⟨rowBound, columnBound, zero, _, _, _⟩ := normalized
  have nonzero : (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det ≠ 0 :=
    ne_of_gt (compact.det_pos rowBound columnBound)
  have transposedNonzero : (matrix.transpose.submatrix (Fin.castLE columnBound) (Fin.castLE rowBound)).det ≠ 0 := by
    simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using nonzero
  have blockRank : (matrix.transpose.submatrix (Fin.castLE columnBound) (Fin.castLE rowBound)).rank = rank := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero transposedNonzero
  have lower := Matrix.rank_submatrix_le matrix.transpose (Fin.castLE columnBound) (Fin.castLE rowBound)
  rw [blockRank] at lower
  have factor := supported_minor_factorization (id : Fin rows → Fin rows) (Fin.castLEEmb rowBound)
    (id : Fin columns → Fin columns) matrix matrix 1 (by simp) (by
      intro row outside column
      have after : rank ≤ row.val := by
        by_contra before
        have rowLt : row.val < rank := by omega
        exact outside ⟨⟨row.val, rowLt⟩, Fin.ext rfl⟩
      exact congrFun (zero row after) column)
  have transposed := congrArg Matrix.transpose factor
  simp only [Matrix.submatrix_id_id, Matrix.transpose_mul] at transposed
  have higher : matrix.transpose.rank ≤ rank := by
    rw [transposed]
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa only [Fintype.card_fin, Fin.coe_castLEEmb] using Matrix.rank_le_card_width (matrix.submatrix (Fin.castLE rowBound) id).transpose)
  exact le_antisymm higher lower

/-- Compact row normalization reports the rank of its original mathematical input. -/
theorem compactHermiteRows_rank {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    (compactHermiteRows original).1 = original.rank := by
  have correct := compactHermiteRows_correct original
  have matrixRank : (compactHermiteRows original).2.1.rank = original.rank := by
    rw [← correct.1, Matrix.rank_mul_eq_left_of_isUnit_det _ _ correct.2.2.1,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ correct.2.1]
  exact correct.2.2.2.rank_eq.symm.trans matrixRank

/-- Transposing an integer matrix preserves rank, via its certified compact presentation. -/
theorem integerMatrix_rank_transpose {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    original.transpose.rank = original.rank := by
  have correct := compactHermiteRows_correct original
  have equation := congrArg Matrix.transpose correct.1
  have transposedRank : (compactHermiteRows original).2.1.transpose.rank = original.transpose.rank := by
    rw [← equation]
    simp only [Matrix.transpose_mul]
    rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa only [Matrix.det_transpose] using correct.2.2.1),
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by simpa only [Matrix.det_transpose] using correct.2.1)]
  exact transposedRank.symm.trans (correct.2.2.2.transpose_rank_eq.trans (compactHermiteRows_rank original))

/-- Compact column normalization reports the same rank, including rectangular inputs. -/
theorem compactHermiteColumns_rank {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    (compactHermiteColumns original).1 = original.rank := by
  change (compactHermiteRows original.transpose).1 = original.rank
  rw [compactHermiteRows_rank, integerMatrix_rank_transpose]

end Polytime2.IntegerMatrix
