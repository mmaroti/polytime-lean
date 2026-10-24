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

import Polytime2.Matrices.SmithConstructionMath

/-! # Polynomial widths for the complete Smith construction

A single polynomial in the original row count, column count, and entry width
bounds the returned diagonal and both accumulated full-sized bases. Rank and
all intermediate capacities are derived inside the bound.
-/

namespace Polytime2.IntegerMatrix

/-- A common output width derived solely from the mathematical input sizes. -/
def smithNormalFormWidth (rows columns width : ℕ) : ℕ :=
  let dimension := rows + columns
  let firstWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
  let initialWidth := hermiteInitialWidth rows columns width
  let diagonalWidth := initialWidth + dimension * (initialWidth + dimension) + 1
  let reductionWidth := 1 + (initialWidth * dimension * dimension + 2) *
    (1 + dimension * hermiteSweepBasisIncrement dimension diagonalWidth + dimension + 1)
  let cleanupWidth := 1 + (diagonalWidth * dimension * dimension + 1) *
    (4 * (diagonalWidth * dimension + 1) + 3)
  let initialLeftWidth := 1 + rows * hermiteSweepBasisIncrement rows width + rows + 2
  let initialRightWidth := 1 + columns * hermiteSweepBasisIncrement columns firstWidth + columns + 2
  diagonalWidth * dimension + 1 + cleanupWidth + reductionWidth + initialLeftWidth + initialRightWidth +
    2 * rows + 2 * columns + 4

/-- All three actual returned matrices have polynomial input-size widths. -/
theorem smithNormalForm_bound {rows columns : ℕ} (width : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    (∀ row column, ((smithNormalForm width matrix).2.1 row column).natAbs <
      2 ^ smithNormalFormWidth rows columns width) ∧
    (∀ row column, ((smithNormalForm width matrix).2.2.1 row column).natAbs <
      2 ^ smithNormalFormWidth rows columns width) ∧
    (∀ row column, ((smithNormalForm width matrix).2.2.2 row column).natAbs <
      2 ^ smithNormalFormWidth rows columns width) := by
  let initial := compactHermiteInitial matrix
  let rowBound := (compactHermiteInitial_dimensions matrix).1
  let columnBound := (compactHermiteInitial_dimensions matrix).2
  let active := initial.2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)
  let initialWidth := hermiteInitialWidth rows columns width
  let reduced := rectangularHermiteRun rowBound columnBound initialWidth active
  let diagonal := fun index : Fin initial.1 =>
    (reduced.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index)).natAbs
  let diagonalWidth := initialWidth + initial.1 * (initialWidth + initial.1) + 1
  let cleaned := rectangularDiagonalCleanup rows columns rowBound columnBound diagonalWidth diagonal
  have prepared := compactHermiteInitial_active width matrix entryBound
  have initialBound := compactHermiteInitial_bound width matrix entryBound
  have reducedBound := rectangularHermiteRun_bound rowBound columnBound initialWidth active
    prepared.1 prepared.2.1 prepared.2.2
  have diagonalPositive : ∀ index, 0 < diagonal index := by
    intro index
    change 0 < (reduced.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index)).natAbs
    rw [show reduced.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index) =
      (hermiteAlternatingRun (initialWidth * initial.1 * initial.1 + 2) active).1 index index from
        rectangularHermiteRun_active_apply rowBound columnBound initialWidth active index index]
    exact Int.natAbs_pos.mpr (ne_of_gt ((hermiteAlternatingRun_triangular _ active prepared.1 prepared.2.1).2 index))
  have diagonalBound : ∀ index, diagonal index < 2 ^ diagonalWidth := fun index => reducedBound.1 _ _
  have cleanupEntries := rectangularDiagonalCleanup_entry_bound rowBound columnBound diagonalWidth diagonal
    diagonalPositive diagonalBound
  have cleanupBases := rectangularDiagonalCleanup_basis_bound rowBound columnBound diagonalWidth diagonal
    diagonalPositive diagonalBound
  have firstLeft := mul_bound _ _ _ _ reducedBound.2.1 initialBound.2.1
  have fullLeft := mul_bound _ _ _ _ cleanupBases.1 firstLeft
  have firstRight := mul_bound _ _ _ _ initialBound.2.2 reducedBound.2.2
  have fullRight := mul_bound _ _ _ _ firstRight cleanupBases.2
  let dimension := rows + columns
  let commonDiagonalWidth := initialWidth + dimension * (initialWidth + dimension) + 1
  let commonReductionWidth := 1 + (initialWidth * dimension * dimension + 2) *
    (1 + dimension * hermiteSweepBasisIncrement dimension commonDiagonalWidth + dimension + 1)
  let commonCleanupWidth := 1 + (commonDiagonalWidth * dimension * dimension + 1) *
    (4 * (commonDiagonalWidth * dimension + 1) + 3)
  have rankLe : initial.1 ≤ dimension := rowBound.trans (Nat.le_add_right rows columns)
  have diagonalLe : diagonalWidth ≤ commonDiagonalWidth := by
    dsimp [diagonalWidth, commonDiagonalWidth]
    gcongr
  have incrementLe : hermiteSweepBasisIncrement initial.1 diagonalWidth ≤
      hermiteSweepBasisIncrement dimension commonDiagonalWidth := by
    dsimp only [hermiteSweepBasisIncrement]
    gcongr
  have reductionLe : 1 + (initialWidth * initial.1 * initial.1 + 2) *
      (1 + initial.1 * hermiteSweepBasisIncrement initial.1 diagonalWidth + initial.1 + 1) ≤ commonReductionWidth := by
    dsimp only [commonReductionWidth]
    gcongr
  have cleanupLe : 1 + (diagonalWidth * initial.1 * initial.1 + 1) *
      (4 * (diagonalWidth * initial.1 + 1) + 3) ≤ commonCleanupWidth := by
    dsimp only [commonCleanupWidth]
    gcongr
  have outputLe : diagonalWidth * initial.1 + 1 ≤ commonDiagonalWidth * dimension + 1 := by gcongr
  let firstWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
  let initialLeftWidth := 1 + rows * hermiteSweepBasisIncrement rows width + rows + 2
  let initialRightWidth := 1 + columns * hermiteSweepBasisIncrement columns firstWidth + columns + 2
  let reductionWidth := 1 + (initialWidth * initial.1 * initial.1 + 2) *
    (1 + initial.1 * hermiteSweepBasisIncrement initial.1 diagonalWidth + initial.1 + 1)
  let cleanupWidth := 1 + (diagonalWidth * initial.1 * initial.1 + 1) *
    (4 * (diagonalWidth * initial.1 + 1) + 3)
  have widthEq : smithNormalFormWidth rows columns width =
      commonDiagonalWidth * dimension + 1 + commonCleanupWidth + commonReductionWidth +
        initialLeftWidth + initialRightWidth + 2 * rows + 2 * columns + 4 := rfl
  change (∀ row column, (cleaned.1 row column).natAbs < _) ∧
    (∀ row column, ((cleaned.2.1 * (reduced.2.1 * initial.2.2.1)) row column).natAbs < _) ∧
    (∀ row column, (((initial.2.2.2 * reduced.2.2) * cleaned.2.2) row column).natAbs < _)
  refine ⟨?_, ?_, ?_⟩
  · intro row column
    exact (cleanupEntries row column).trans_le (pow_le_pow_right₀ (by decide) (by
      change diagonalWidth * initial.1 + 1 ≤ smithNormalFormWidth rows columns width
      rw [widthEq]
      omega))
  · intro row column
    exact (fullLeft row column).trans_le (pow_le_pow_right₀ (by decide) (by
      simp only [Fintype.card_fin]
      change cleanupWidth + (reductionWidth + initialLeftWidth + rows + 1) + rows + 1 ≤
        smithNormalFormWidth rows columns width
      rw [widthEq]
      change reductionWidth ≤ commonReductionWidth at reductionLe
      change cleanupWidth ≤ commonCleanupWidth at cleanupLe
      omega))
  · intro row column
    exact (fullRight row column).trans_le (pow_le_pow_right₀ (by decide) (by
      simp only [Fintype.card_fin]
      change initialRightWidth + reductionWidth + columns + 1 + cleanupWidth + columns + 1 ≤
        smithNormalFormWidth rows columns width
      rw [widthEq]
      change reductionWidth ≤ commonReductionWidth at reductionLe
      change cleanupWidth ≤ commonCleanupWidth at cleanupLe
      omega))

end Polytime2.IntegerMatrix
