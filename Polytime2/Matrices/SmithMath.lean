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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! # Rectangular Smith contracts and integer feasibility

The contract retains the actual diagonal and both integer transformation
matrices. The active length is at most both dimensions; active diagonal
entries are positive and divide the next entry, and every other entry is zero.

For a certified diagonal presentation, feasibility means divisibility on the
active rows and vanishing on the remaining rows. Division constructs diagonal
solution coordinates, and the right transformation transports them back to
an integer solution of the original system. These are mathematical statements,
independent of the algorithm and its bit-capacity bounds.
-/

namespace Polytime2.IntegerMatrix

variable {rows columns : ℕ}

/-- An entry on the common diagonal of a rectangular matrix. -/
def diagonalEntry (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (index : Fin (min rows columns)) : ℤ :=
  diagonal (index.castLE (Nat.min_le_left rows columns))
    (index.castLE (Nat.min_le_right rows columns))

/-- Positive Smith diagonal with an explicit active length, including rank zero. -/
def IsSmithDiagonal (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ) : Prop :=
  rank ≤ min rows columns ∧
  (∀ row column, row.val ≠ column.val → diagonal row column = 0) ∧
  (∀ row column, rank ≤ row.val → diagonal row column = 0) ∧
  (∀ row column, row.val = column.val → row.val < rank → 0 < diagonal row column) ∧
  (∀ first second : Fin (min rows columns), second.val = first.val + 1 → second.val < rank →
    diagonalEntry diagonal first ∣ diagonalEntry diagonal second)

/-- The complete mathematical contract for the matrices returned by Smith reduction. -/
def IsSmithForm (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ)
    (right : Matrix (Fin columns) (Fin columns) ℤ) (rank : ℕ) : Prop :=
  left * matrix * right = diagonal ∧ IsUnit left.det ∧ IsUnit right.det ∧
    IsSmithDiagonal diagonal rank

/-- Equal matrix triples have the same Smith contract, independently of codecs. -/
theorem IsSmithForm.of_values {matrix : Matrix (Fin rows) (Fin columns) ℤ} {rank : ℕ}
    {source target : Matrix (Fin rows) (Fin columns) ℤ ×
      Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ}
    (same : target = source)
    (form : IsSmithForm matrix source.1 source.2.1 source.2.2 rank) :
    IsSmithForm matrix target.1 target.2.1 target.2.2 rank := by
  subst target
  exact form

/-- Changing equal finite dimensions preserves the complete Smith contract. -/
theorem IsSmithForm.cast {otherRows otherColumns rank otherRank : ℕ}
    (rowEq : rows = otherRows) (columnEq : columns = otherColumns)
    (rankEq : rank = otherRank)
    {matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ}
    {left : Matrix (Fin rows) (Fin rows) ℤ}
    {right : Matrix (Fin columns) (Fin columns) ℤ}
    (form : IsSmithForm matrix diagonal left right rank) :
    IsSmithForm
      (fun row column => matrix (Fin.cast rowEq.symm row) (Fin.cast columnEq.symm column))
      (fun row column => diagonal (Fin.cast rowEq.symm row) (Fin.cast columnEq.symm column))
      (fun row column => left (Fin.cast rowEq.symm row) (Fin.cast rowEq.symm column))
      (fun row column => right (Fin.cast columnEq.symm row) (Fin.cast columnEq.symm column)) otherRank := by
  subst otherRows otherColumns otherRank
  simpa using form

/-- Compose a Smith reduction with an existing unimodular presentation of the input. -/
theorem IsSmithForm.of_equation {matrix current diagonal : Matrix (Fin rows) (Fin columns) ℤ}
    {left initialLeft : Matrix (Fin rows) (Fin rows) ℤ}
    {right initialRight : Matrix (Fin columns) (Fin columns) ℤ} {rank : ℕ}
    (form : IsSmithForm current diagonal left right rank)
    (equation : initialLeft * matrix * initialRight = current)
    (leftUnit : IsUnit initialLeft.det) (rightUnit : IsUnit initialRight.det) :
    IsSmithForm matrix diagonal (left * initialLeft) (initialRight * right) rank := by
  refine ⟨?_, ?_, ?_, form.2.2.2⟩
  · calc
      _ = left * (initialLeft * matrix * initialRight) * right := by simp only [Matrix.mul_assoc]
      _ = diagonal := by rw [equation]; exact form.1
  · rw [Matrix.det_mul]
    exact form.2.1.mul leftUnit
  · rw [Matrix.det_mul]
    exact rightUnit.mul form.2.2.1

/-- Divisibility on active rows, and zero on every remaining row. -/
def diagonalFeasible (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) : Prop :=
  ∀ row, if active : row.val < rank then
    diagonal row ⟨row.val, active.trans_le (within.trans (Nat.min_le_right rows columns))⟩ ∣ target row
  else target row = 0

/-- Divide active coordinates by their diagonal entries; use zero elsewhere. -/
def diagonalSolution (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) : Fin columns → ℤ :=
  fun column => if active : column.val < rank then
    let row : Fin rows := ⟨column.val, active.trans_le (within.trans (Nat.min_le_left rows columns))⟩
    target row / diagonal row column
  else 0


/-- Dividing diagonal coordinates never increases the target magnitude bound. -/
theorem diagonalSolution_bound (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) (width : ℕ)
    (targetBound : ∀ row, (target row).natAbs < 2 ^ width) :
    ∀ column, (diagonalSolution diagonal rank within target column).natAbs < 2 ^ width := by
  intro column
  unfold diagonalSolution
  split
  · exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (targetBound _)
  · simp

private theorem diagonal_mulVec_active (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (offDiagonal : ∀ row column, row.val ≠ column.val → diagonal row column = 0)
    (values : Fin columns → ℤ) (row : Fin rows) (inColumns : row.val < columns) :
    diagonal.mulVec values row = diagonal row ⟨row.val, inColumns⟩ * values ⟨row.val, inColumns⟩ := by
  classical
  change (∑ column, diagonal row column * values column) = _
  apply Finset.sum_eq_single (s := Finset.univ)
    (f := fun column : Fin columns => diagonal row column * values column) ⟨row.val, inColumns⟩
  · intro column _ different
    have differentValues : row.val ≠ column.val := by
      intro same
      exact different (Fin.ext same.symm)
    rw [offDiagonal row column differentValues, zero_mul]
  · simp

/-- The explicit diagonal coordinates solve the system whenever the criterion holds. -/
theorem diagonalSolution_correct (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ)
    (feasible : diagonalFeasible diagonal rank smith.1 target) :
    diagonal.mulVec (diagonalSolution diagonal rank smith.1 target) = target := by
  funext row
  by_cases active : row.val < rank
  · have inColumns : row.val < columns := active.trans_le (smith.1.trans (Nat.min_le_right rows columns))
    rw [diagonal_mulVec_active diagonal smith.2.1 _ row inColumns]
    have divides : diagonal row ⟨row.val, inColumns⟩ ∣ target row := by
      simpa only [diagonalFeasible, active, ↓reduceDIte] using feasible row
    have sameRow : (⟨row.val, active.trans_le (smith.1.trans (Nat.min_le_left rows columns))⟩ : Fin rows) = row := rfl
    simp only [diagonalSolution, active, ↓reduceDIte, sameRow]
    exact Int.mul_ediv_cancel' divides
  · have zeroRow : ∀ column, diagonal row column = 0 := fun column => smith.2.2.1 row column (by omega)
    have zeroTarget : target row = 0 := by
      simpa only [diagonalFeasible, active, ↓reduceDIte] using feasible row
    simp [Matrix.mulVec, dotProduct, zeroRow, zeroTarget]

/-- Every integer solution satisfies the active divisibility and zero-row tests. -/
theorem diagonalFeasible_of_solution (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ)
    (values : Fin columns → ℤ) (solution : diagonal.mulVec values = target) :
    diagonalFeasible diagonal rank smith.1 target := by
  intro row
  by_cases active : row.val < rank
  · simp only [active, ↓reduceDIte]
    rw [← solution, diagonal_mulVec_active diagonal smith.2.1]
    exact dvd_mul_right _ _
  · simp only [active, ↓reduceDIte]
    rw [← solution]
    have zeroRow : ∀ column, diagonal row column = 0 := fun column => smith.2.2.1 row column (by omega)
    simp [Matrix.mulVec, dotProduct, zeroRow]

/-- Exact feasibility criterion, valid for rectangular, singular, and empty matrices. -/
theorem diagonalFeasible_iff (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ) :
    diagonalFeasible diagonal rank smith.1 target ↔ ∃ values, diagonal.mulVec values = target :=
  ⟨fun feasible => ⟨diagonalSolution diagonal rank smith.1 target,
    diagonalSolution_correct diagonal rank smith target feasible⟩,
    fun ⟨values, solution⟩ => diagonalFeasible_of_solution diagonal rank smith target values solution⟩


/-- Boolean feasibility test by scanning every mathematical row. -/
def diagonalFeasibilityTest (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) : Bool :=
  (List.finRange rows).all fun row => if active : row.val < rank then
    decide (diagonal row ⟨row.val, active.trans_le (within.trans (Nat.min_le_right rows columns))⟩ ∣ target row)
  else decide (target row = 0)

theorem diagonalFeasibilityTest_iff (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) :
    diagonalFeasibilityTest diagonal rank within target = true ↔
      diagonalFeasible diagonal rank within target := by
  simp only [diagonalFeasibilityTest, List.all_eq_true, List.mem_finRange, forall_const]
  apply forall_congr'
  intro row
  by_cases active : row.val < rank <;> simp [active]

/-- Explicit solution coordinates, or the mathematical no-solution alternative. -/
def diagonalSolve (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) : Option (Fin columns → ℤ) :=
  if diagonalFeasibilityTest diagonal rank within target then
    some (diagonalSolution diagonal rank within target)
  else none

theorem diagonalSolve_some_correct (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ) (values : Fin columns → ℤ)
    (result : diagonalSolve diagonal rank smith.1 target = some values) :
    diagonal.mulVec values = target := by
  unfold diagonalSolve at result
  split at result
  · rename_i accepted
    cases Option.some.inj result
    exact diagonalSolution_correct diagonal rank smith target
      ((diagonalFeasibilityTest_iff diagonal rank smith.1 target).mp accepted)
  · cases result

theorem diagonalSolve_none_iff (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (target : Fin rows → ℤ) :
    diagonalSolve diagonal rank smith.1 target = none ↔
      ¬ ∃ values, diagonal.mulVec values = target := by
  rw [← diagonalFeasible_iff diagonal rank smith, ← diagonalFeasibilityTest_iff]
  simp [diagonalSolve]

/-- Unimodular two-sided changes preserve integer solvability. -/
theorem feasible_iff_transformed (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (equation : left * matrix * right = diagonal)
    (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) (target : Fin rows → ℤ) :
    (∃ values, matrix.mulVec values = target) ↔
      ∃ coordinates, diagonal.mulVec coordinates = left.mulVec target := by
  have injective := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det left).mpr leftUnit)
  have surjective := Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det right).mpr rightUnit)
  constructor
  · rintro ⟨values, solution⟩
    obtain ⟨coordinates, coordinates_eq⟩ := surjective values
    refine ⟨coordinates, ?_⟩
    rw [← equation, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, coordinates_eq, solution]
  · rintro ⟨coordinates, solution⟩
    refine ⟨right.mulVec coordinates, injective ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, equation]
    exact solution

/-- Smith reduction decides feasibility by divisibility after applying the left matrix. -/
theorem smithFeasible_iff (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) (target : Fin rows → ℤ) :
    (∃ values, matrix.mulVec values = target) ↔
      diagonalFeasible diagonal rank smith.2.2.2.1 (left.mulVec target) := by
  rw [feasible_iff_transformed matrix diagonal left right smith.1 smith.2.1 smith.2.2.1,
    diagonalFeasible_iff diagonal rank smith.2.2.2]

/-- Recover the original solution by applying the right transformation to diagonal coordinates. -/
theorem smithSolution_correct (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) (target : Fin rows → ℤ)
    (feasible : diagonalFeasible diagonal rank smith.2.2.2.1 (left.mulVec target)) :
    matrix.mulVec (right.mulVec (diagonalSolution diagonal rank smith.2.2.2.1 (left.mulVec target))) = target := by
  apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det left).mpr smith.2.1)
  simp only [Matrix.mulVec_mulVec]
  simpa only [Matrix.mul_assoc] using (congrArg (fun transformed => transformed.mulVec
    (diagonalSolution diagonal rank smith.2.2.2.1 (left.mulVec target))) smith.1).trans
      (diagonalSolution_correct diagonal rank smith.2.2.2 _ feasible)


/-- Once the transformations have bounded entries, witness recovery has a
polynomial bit bound in those widths, the target width, and both dimensions. -/
theorem smithSolution_bound (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (within : rank ≤ min rows columns) (target : Fin rows → ℤ)
    (transformationWidth targetWidth : ℕ)
    (leftBound : ∀ row column, (left row column).natAbs < 2 ^ transformationWidth)
    (rightBound : ∀ row column, (right row column).natAbs < 2 ^ transformationWidth)
    (targetBound : ∀ row, (target row).natAbs < 2 ^ targetWidth) :
    ∀ column, (right.mulVec (diagonalSolution diagonal rank within (left.mulVec target)) column).natAbs <
      2 ^ (2 * transformationWidth + targetWidth + rows + columns + 2) := by
  have transformedBound := mulVec_bound transformationWidth targetWidth left target leftBound targetBound
  have coordinatesBound := diagonalSolution_bound diagonal rank within (left.mulVec target)
    (transformationWidth + targetWidth + rows + 1) (by simpa using transformedBound)
  intro column
  have result := mulVec_bound transformationWidth (transformationWidth + targetWidth + rows + 1)
    right (diagonalSolution diagonal rank within (left.mulVec target)) rightBound coordinatesBound column
  have widthEqual : transformationWidth + (transformationWidth + targetWidth + rows + 1) + columns + 1 =
      2 * transformationWidth + targetWidth + rows + columns + 2 := by omega
  simpa only [Fintype.card_fin, widthEqual] using result

end Polytime2.IntegerMatrix
