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

import Polytime2.Matrices.HermiteStabilizationMath
import Polytime2.Matrices.SupportedDeterminantMath

/-! # Fixed determinant after Hermite support stabilization

For a matrix supported in a leading square block, unimodular presentation
changes preserve that block's determinant magnitude whenever the result has the
same support. Subsequent row and column passes have that property. A normalized
compact block is entrywise bounded by its determinant, so this magnitude can
control coefficient growth across alternating passes rather than recursively
widening each preceding matrix bound.
-/

namespace Polytime2.IntegerMatrix

private theorem outside_prefix {rank dimension : ℕ} (within : rank ≤ dimension) (index : Fin dimension)
    (outside : index ∉ Set.range (Fin.castLEEmb within)) : rank ≤ index.val := by
  simpa only [Fin.coe_castLEEmb, Fin.range_castLE, Set.mem_ofPred_eq, not_lt] using outside

/-- Fully supported leading blocks have invariant determinant magnitude under a presentation change. -/
theorem leading_presentation_det_natAbs {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (original current : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (equation : left * original * right = current) (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det)
    (originalRows : ∀ row : Fin rows, rank ≤ row.val → original row = 0)
    (originalColumns : ∀ column : Fin columns, rank ≤ column.val → original.transpose column = 0)
    (currentRows : ∀ row : Fin rows, rank ≤ row.val → current row = 0)
    (currentColumns : ∀ column : Fin columns, rank ≤ column.val → current.transpose column = 0) :
    (current.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs =
      (original.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  exact supported_presentation_det_natAbs (Fin.castLEEmb rowBound) (Fin.castLEEmb columnBound)
    original current left right equation leftUnit rightUnit
    (fun row outside column => congrFun (originalRows row (outside_prefix rowBound row outside)) column)
    (fun column outside row => congrFun (originalColumns column (outside_prefix columnBound column outside)) row)
    (fun row outside column => congrFun (currentRows row (outside_prefix rowBound row outside)) column)
    (fun column outside row => congrFun (currentColumns column (outside_prefix columnBound column outside)) row)

/-- After stabilization, a row pass keeps the active determinant magnitude fixed. -/
theorem compactHermiteRows_det_natAbs {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original.transpose)
    (zeroRows : ∀ row : Fin rows, rank ≤ row.val → original row = 0) :
    ((compactHermiteRows original).2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs =
      (original.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  have originalRank : original.rank = rank := by
    simpa only [Matrix.transpose_transpose] using normalized.transpose_rank_eq
  have sameRank : (compactHermiteRows original).1 = rank := (compactHermiteRows_rank original).trans originalRank
  have correct := compactHermiteRows_correct original
  have newShape := correct.2.2.2
  rw [sameRank] at newShape
  obtain ⟨_, _, newZeroRows, _, _, _⟩ := newShape
  have oldShape := normalized
  obtain ⟨_, _, zeroColumns, _, _, _⟩ := oldShape
  exact leading_presentation_det_natAbs rowBound columnBound original _ _ _ correct.1 correct.2.1 correct.2.2.1
    zeroRows zeroColumns newZeroRows (compactHermiteRows_zero_columns original normalized)

/-- The dual column pass keeps the same active determinant magnitude. -/
theorem compactHermiteColumns_det_natAbs {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original)
    (zeroColumns : ∀ column : Fin columns, rank ≤ column.val → original.transpose column = 0) :
    ((compactHermiteColumns original).2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs =
      (original.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  have preserved := compactHermiteRows_det_natAbs columnBound rowBound original.transpose
    (by simpa only [Matrix.transpose_transpose] using normalized) zeroColumns
  simpa only [compactHermiteColumns, ← Matrix.transpose_submatrix, Matrix.det_transpose] using preserved

/-- A normalized fully supported compact matrix is bounded by its active determinant magnitude. -/
theorem IsCompactRowHermite.entry_le_det {rows columns rank : ℕ} {matrix : Matrix (Fin rows) (Fin columns) ℤ}
    (normalized : IsCompactRowHermite rank matrix) (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (zeroColumns : ∀ column : Fin columns, rank ≤ column.val → matrix.transpose column = 0) :
    ∀ row column, (matrix row column).natAbs ≤
      (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  obtain ⟨_, _, zeroRows, upper, positive, reduced⟩ := normalized
  have blockBound := normalized_block_entry_le_det
    (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)) upper positive reduced
  intro row column
  by_cases rowBefore : row.val < rank
  · by_cases columnBefore : column.val < rank
    · let rowIndex : Fin rank := ⟨row.val, rowBefore⟩
      let columnIndex : Fin rank := ⟨column.val, columnBefore⟩
      have rowEq : Fin.castLE rowBound rowIndex = row := Fin.ext rfl
      have columnEq : Fin.castLE columnBound columnIndex = column := Fin.ext rfl
      simpa only [Matrix.submatrix_apply, rowEq, columnEq] using blockBound rowIndex columnIndex
    · have zero := congrFun (zeroColumns column (by omega)) row
      change matrix row column = 0 at zero
      rw [zero, Int.natAbs_zero]
      exact Nat.zero_le _
  · rw [congrFun (zeroRows row (by omega)) column, Pi.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

/-- The output of a stabilized row pass is bounded by the input's active determinant. -/
theorem compactHermiteRows_entry_le_det {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original.transpose)
    (zeroRows : ∀ row : Fin rows, rank ≤ row.val → original row = 0) :
    ∀ row column, ((compactHermiteRows original).2.1 row column).natAbs ≤
      (original.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  have originalRank : original.rank = rank := by
    simpa only [Matrix.transpose_transpose] using normalized.transpose_rank_eq
  have sameRank : (compactHermiteRows original).1 = rank := (compactHermiteRows_rank original).trans originalRank
  have shape := (compactHermiteRows_correct original).2.2.2
  rw [sameRank] at shape
  have bounded := shape.entry_le_det rowBound columnBound (compactHermiteRows_zero_columns original normalized)
  rw [compactHermiteRows_det_natAbs rowBound columnBound original normalized zeroRows] at bounded
  exact bounded

/-- The dual column output has the same fixed-determinant coefficient bound. -/
theorem compactHermiteColumns_entry_le_det {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original)
    (zeroColumns : ∀ column : Fin columns, rank ≤ column.val → original.transpose column = 0) :
    ∀ row column, ((compactHermiteColumns original).2.1 row column).natAbs ≤
      (original.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs := by
  have bounded := compactHermiteRows_entry_le_det columnBound rowBound original.transpose
    (by simpa only [Matrix.transpose_transpose] using normalized) zeroColumns
  intro row column
  simpa only [compactHermiteColumns, Matrix.transpose_apply, ← Matrix.transpose_submatrix, Matrix.det_transpose] using
    bounded column row

end Polytime2.IntegerMatrix
