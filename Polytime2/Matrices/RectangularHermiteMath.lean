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

import Polytime2.Matrices.HermiteAlternatingBounds

/-! # Rectangular extension of bounded Hermite diagonalization

A supported rectangular matrix has a positive lower triangular active square
block. Run bounded alternating reduction on that block and extend both actual
bases by identities on the independent row and column complements.
-/

namespace Polytime2.IntegerMatrix

/-- Diagonalize the active square block and retain full-sized transformations. -/
def rectangularHermiteRun {rows columns rank : ℕ} (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ) :
    Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let result := hermiteAlternatingRun (width * rank * rank + 2) matrix
  (rectangularBlock rowBound columnBound result.1,
    extendDiagonalBasis rows rowBound result.2.1, extendDiagonalBasis columns columnBound result.2.2)

/-- Active coordinates of the full result read the same computed square result. -/
theorem rectangularHermiteRun_active_apply {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ) (row column : Fin rank) :
    (rectangularHermiteRun rowBound columnBound width matrix).1
      (Fin.castLE rowBound row) (Fin.castLE columnBound column) =
      (hermiteAlternatingRun (width * rank * rank + 2) matrix).1 row column := by
  simp only [rectangularHermiteRun, rectangularBlock_apply, Fin.val_castLE, row.isLt, column.isLt, dite_true]

/-- The full rectangular presentation and unimodularity hold without normalization assumptions. -/
theorem rectangularHermiteRun_preserves {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ) :
    (rectangularHermiteRun rowBound columnBound width matrix).2.1 *
      rectangularBlock rowBound columnBound matrix *
      (rectangularHermiteRun rowBound columnBound width matrix).2.2 =
        (rectangularHermiteRun rowBound columnBound width matrix).1 ∧
    IsUnit (rectangularHermiteRun rowBound columnBound width matrix).2.1.det ∧
    IsUnit (rectangularHermiteRun rowBound columnBound width matrix).2.2.det := by
  have correct := hermiteAlternatingRun_preserves (width * rank * rank + 2) matrix
  refine ⟨extendDiagonalBasis_block_equation _ _ rowBound columnBound _ _ correct.1, ?_, ?_⟩
  · simpa only [rectangularHermiteRun, extendDiagonalBasis_det] using correct.2.1
  · simpa only [rectangularHermiteRun, extendDiagonalBasis_det] using correct.2.2

/-- The returned full matrix is the positive active diagonal with zero inactive strips. -/
theorem rectangularHermiteRun_diagonal {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    (rectangularHermiteRun rowBound columnBound width matrix).1 =
      rectangularDiagonal rows columns
        (fun index => ((hermiteAlternatingRun (width * rank * rank + 2) matrix).1 index index).natAbs) := by
  exact rectangularBlock_of_positive_diagonal rowBound columnBound _
    (hermiteAlternatingRun_polynomial_budget width matrix lower positive entryBound)
    (hermiteAlternatingRun_triangular _ matrix lower positive).2

/-- A supported rectangular input reuses the active-block presentation directly. -/
theorem rectangularHermiteRun_of_supported {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (zeroRows : ∀ row : Fin rows, rank ≤ row.val → matrix row = 0)
    (zeroColumns : ∀ column : Fin columns, rank ≤ column.val → matrix.transpose column = 0) :
    let result := rectangularHermiteRun rowBound columnBound width
      (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound))
    result.2.1 * matrix * result.2.2 = result.1 ∧ IsUnit result.2.1.det ∧ IsUnit result.2.2.det := by
  have correct := rectangularHermiteRun_preserves rowBound columnBound width
    (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound))
  simpa only [rectangularBlock_submatrix rowBound columnBound matrix zeroRows zeroColumns] using correct

/-- Extending the square run preserves its polynomial widths for the matrix and both full bases. -/
theorem rectangularHermiteRun_bound {rows columns rank : ℕ}
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    let commonWidth := width + rank * (width + rank) + 1
    let basisWidth := 1 + (width * rank * rank + 2) *
      (1 + rank * hermiteSweepBasisIncrement rank commonWidth + rank + 1)
    (∀ row column, ((rectangularHermiteRun rowBound columnBound width matrix).1 row column).natAbs <
      2 ^ commonWidth) ∧
    (∀ row column, ((rectangularHermiteRun rowBound columnBound width matrix).2.1 row column).natAbs <
      2 ^ basisWidth) ∧
    (∀ row column, ((rectangularHermiteRun rowBound columnBound width matrix).2.2 row column).natAbs <
      2 ^ basisWidth) := by
  have bounded := hermiteAlternatingRun_bound width (width * rank * rank + 2) matrix lower positive entryBound
  refine ⟨rectangularBlock_bound rowBound columnBound _ _ bounded.1, ?_, ?_⟩
  · exact extendDiagonalBasis_bound rows _ rowBound (by omega) _ bounded.2.1
  · exact extendDiagonalBasis_bound columns _ columnBound (by omega) _ bounded.2.2

/-- Equal dimensions, widths, and active entries give equal full output entries. -/
theorem rectangularHermiteRun_congr
    {rows columns rank otherRows otherColumns otherRank width otherWidth : ℕ}
    (rowsEqual : rows = otherRows) (columnsEqual : columns = otherColumns)
    (rankEqual : rank = otherRank) (widthEqual : width = otherWidth)
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (otherRowBound : otherRank ≤ otherRows) (otherColumnBound : otherRank ≤ otherColumns)
    (matrix : Matrix (Fin rank) (Fin rank) ℤ) (otherMatrix : Matrix (Fin otherRank) (Fin otherRank) ℤ)
    (entries : ∀ row column otherRow otherColumn, row.val = otherRow.val → column.val = otherColumn.val →
      matrix row column = otherMatrix otherRow otherColumn) :
    let first := rectangularHermiteRun rowBound columnBound width matrix
    let second := rectangularHermiteRun otherRowBound otherColumnBound otherWidth otherMatrix
    (∀ row column otherRow otherColumn, row.val = otherRow.val → column.val = otherColumn.val →
      first.1 row column = second.1 otherRow otherColumn) ∧
    (∀ row column otherRow otherColumn, row.val = otherRow.val → column.val = otherColumn.val →
      first.2.1 row column = second.2.1 otherRow otherColumn) ∧
    (∀ row column otherRow otherColumn, row.val = otherRow.val → column.val = otherColumn.val →
      first.2.2 row column = second.2.2 otherRow otherColumn) := by
  subst otherRows
  subst otherColumns
  subst otherRank
  subst otherWidth
  have same : matrix = otherMatrix := by
    ext row column
    exact entries row column row column rfl rfl
  subst otherMatrix
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro row column otherRow otherColumn rowSame columnSame
    have rowEqual : row = otherRow := Fin.ext rowSame
    have columnEqual : column = otherColumn := Fin.ext columnSame
    subst otherRow
    subst otherColumn
    rfl

end Polytime2.IntegerMatrix
