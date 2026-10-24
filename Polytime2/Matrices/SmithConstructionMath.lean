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

import Polytime2.Matrices.RectangularHermiteMath
import Polytime2.Matrices.HermiteStabilizationMath

/-! # Smith normal form by bounded Hermite reduction and divisibility cleanup

For an arbitrary rectangular integer matrix of input entry width `w`, compact
the active block, diagonalize it with the polynomial alternating schedule,
and normalize divisibility. Return the rank, diagonal matrix, and both actual
unimodular bases. No sign, nonsingularity, or nonempty-dimension assumption is
part of the mathematical input contract.
-/

namespace Polytime2.IntegerMatrix

/-- The compact initialization's active square fits both original dimensions. -/
theorem compactHermiteInitial_dimensions {rows columns : ℕ}
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    (compactHermiteInitial matrix).1 ≤ rows ∧ (compactHermiteInitial matrix).1 ≤ columns := by
  obtain ⟨columnBound, rowBound, _⟩ := (compactHermiteInitial_correct matrix).2.2.2.1
  exact ⟨rowBound, columnBound⟩

/-- Initialization supplies a positive lower triangular active block at its derived width. -/
theorem compactHermiteInitial_active {rows columns : ℕ} (width : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    let initial := compactHermiteInitial matrix
    let active := initial.2.1.submatrix
      (Fin.castLE (compactHermiteInitial_dimensions matrix).1)
      (Fin.castLE (compactHermiteInitial_dimensions matrix).2)
    active.IsLowerTriangular ∧ (∀ index, 0 < active index index) ∧
      (∀ row column, (active row column).natAbs < 2 ^ hermiteInitialWidth rows columns width) := by
  obtain ⟨_, _, _, upper, positive, _⟩ := (compactHermiteInitial_correct matrix).2.2.2.1
  exact ⟨upper.transpose, positive, fun row column => (compactHermiteInitial_bound width matrix entryBound).1 _ _⟩

/-- Bounded Smith construction, returning rank and full mathematical matrices. -/
def smithNormalForm {rows columns : ℕ} (width : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    ℕ × Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let initial := compactHermiteInitial matrix
  have rowBound := (compactHermiteInitial_dimensions matrix).1
  have columnBound := (compactHermiteInitial_dimensions matrix).2
  let active := initial.2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)
  let initialWidth := hermiteInitialWidth rows columns width
  let reduced := rectangularHermiteRun rowBound columnBound initialWidth active
  let diagonal := fun index : Fin initial.1 =>
    (reduced.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index)).natAbs
  let diagonalWidth := initialWidth + initial.1 * (initialWidth + initial.1) + 1
  let cleaned := rectangularDiagonalCleanup rows columns rowBound columnBound diagonalWidth diagonal
  (initial.1, cleaned.1, cleaned.2.1 * (reduced.2.1 * initial.2.2.1),
    (initial.2.2.2 * reduced.2.2) * cleaned.2.2)

/-- The reported rank is the integer matrix rank, independently of the supplied width. -/
theorem smithNormalForm_rank {rows columns : ℕ} (width : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    (smithNormalForm width matrix).1 = matrix.rank := compactHermiteInitial_rank matrix

/-- Input entry bounds certify the complete rectangular Smith contract. -/
theorem smithNormalForm_isSmithForm {rows columns : ℕ} (width : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    let result := smithNormalForm width matrix
    IsSmithForm matrix result.2.1 result.2.2.1 result.2.2.2 result.1 := by
  let initial := compactHermiteInitial matrix
  let rowBound := (compactHermiteInitial_dimensions matrix).1
  let columnBound := (compactHermiteInitial_dimensions matrix).2
  let active := initial.2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)
  let initialWidth := hermiteInitialWidth rows columns width
  let reduced := rectangularHermiteRun rowBound columnBound initialWidth active
  let diagonal := fun index : Fin initial.1 =>
    (reduced.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index)).natAbs
  let diagonalWidth := initialWidth + initial.1 * (initialWidth + initial.1) + 1
  have correct := compactHermiteInitial_correct matrix
  obtain ⟨_, _, zeroColumns, upper, positive, _⟩ := correct.2.2.2.1
  have prepared := compactHermiteInitial_active width matrix entryBound
  have lower : active.IsLowerTriangular := prepared.1
  have activePositive : ∀ index, 0 < active index index := prepared.2.1
  have activeBound : ∀ row column, (active row column).natAbs < 2 ^ initialWidth := prepared.2.2
  have runCorrect := rectangularHermiteRun_of_supported rowBound columnBound initialWidth initial.2.1
    correct.2.2.2.2 zeroColumns
  have reducedDiagonal := rectangularHermiteRun_diagonal rowBound columnBound initialWidth active
    lower activePositive activeBound
  have diagonalEqual : diagonal = fun index =>
      ((hermiteAlternatingRun (initialWidth * initial.1 * initial.1 + 2) active).1 index index).natAbs := by
    funext index
    exact congrArg Int.natAbs (rectangularHermiteRun_active_apply rowBound columnBound initialWidth active index index)
  have diagonalPositive : ∀ index, 0 < diagonal index := by
    rw [diagonalEqual]
    intro index
    exact Int.natAbs_pos.mpr (ne_of_gt ((hermiteAlternatingRun_triangular _ active lower activePositive).2 index))
  have diagonalBound : ∀ index, diagonal index < 2 ^ diagonalWidth := by
    have reducedBound := rectangularHermiteRun_bound rowBound columnBound initialWidth active
      lower activePositive activeBound
    intro index
    exact reducedBound.1 _ _
  have equation : (reduced.2.1 * initial.2.2.1) * matrix * (initial.2.2.2 * reduced.2.2) =
      rectangularDiagonal rows columns diagonal := by
    calc
      _ = reduced.2.1 * (initial.2.2.1 * matrix * initial.2.2.2) * reduced.2.2 := by
        simp only [Matrix.mul_assoc]
      _ = reduced.2.1 * initial.2.1 * reduced.2.2 := by rw [correct.1]
      _ = reduced.1 := runCorrect.1
      _ = _ := by simpa only [diagonalEqual] using reducedDiagonal
  have leftUnit : IsUnit (reduced.2.1 * initial.2.2.1).det := by
    rw [Matrix.det_mul]
    exact runCorrect.2.1.mul correct.2.1
  have rightUnit : IsUnit (initial.2.2.2 * reduced.2.2).det := by
    rw [Matrix.det_mul]
    exact correct.2.2.1.mul runCorrect.2.2
  exact rectangularDiagonalCleanup_of_presentation rowBound columnBound diagonalWidth diagonal
    diagonalPositive diagonalBound matrix _ _ equation leftUnit rightUnit

end Polytime2.IntegerMatrix
