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

import Polytime2.Matrices.HermiteRankMath

/-! # Stabilizing the active rectangle

A column pass following compact row normalization reports the same rank.
Its positive leading block forces its row permutation to preserve the active
prefix. Consequently it keeps the old inactive rows zero while also clearing
all inactive columns. This is the rectangular reduction needed before the
square active-block alternating progress argument.
-/

namespace Polytime2.IntegerMatrix

/-- A compact column pass preserves the zero inactive rows of a compact row input. -/
theorem compactHermiteColumns_zero_rows {rows columns rank : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original) :
    ∀ row : Fin rows, rank ≤ row.val → (compactHermiteColumns original).2.1 row = 0 := by
  have sameRank : (compactHermiteColumns original).1 = rank := (compactHermiteColumns_rank original).trans normalized.rank_eq
  have columnShape := (compactHermiteColumns_correct original).2.2.2
  rw [sameRank] at columnShape
  obtain ⟨columnBound, rowBound, zeroColumns, lower, positive, reduced⟩ := columnShape
  obtain ⟨_, _, oldZero, _, _, _⟩ := normalized
  let state := hermiteRowsSweep original.transpose
  let columnPermutation := pivotPermutation state.2.2.1
  let rowPermutation := pivotPermutation state.2.2.2
  have equation := (hermiteRowsSweep_correct original.transpose).1
  have originZero (row : Fin rows) (after : rank ≤ (rowPermutation row).val) :
      (compactHermiteColumns original).2.1 row = 0 := by
    funext column
    change state.1.1 (columnPermutation column) (rowPermutation row) = 0
    rw [← equation]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, oldZero (rowPermutation row) after,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have before (index : Fin rank) : (rowPermutation (Fin.castLE rowBound index)).val < rank := by
    by_contra after
    have zero := congrFun (originZero (Fin.castLE rowBound index) (by omega)) (Fin.castLE columnBound index)
    have positiveEntry := positive index
    change 0 < (compactHermiteColumns original).2.1 (Fin.castLE rowBound index) (Fin.castLE columnBound index) at positiveEntry
    exact (ne_of_gt positiveEntry) zero
  let restricted : Fin rank → Fin rank := fun index => ⟨(rowPermutation (Fin.castLE rowBound index)).val, before index⟩
  have injective : Function.Injective restricted := by
    intro first second same
    have values := congrArg Fin.val same
    have images : rowPermutation (Fin.castLE rowBound first) = rowPermutation (Fin.castLE rowBound second) := Fin.ext values
    have positions := rowPermutation.injective images
    have positionsValues := congrArg Fin.val positions
    exact Fin.ext positionsValues
  have surjective := Finite.surjective_of_injective injective
  intro row after
  apply originZero row
  by_contra beforeRank
  have imageBefore : (rowPermutation row).val < rank := by omega
  obtain ⟨index, image⟩ := surjective ⟨(rowPermutation row).val, imageBefore⟩
  have imageValues := congrArg Fin.val image
  have positions := rowPermutation.injective (show rowPermutation (Fin.castLE rowBound index) = rowPermutation row from Fin.ext imageValues)
  have values := congrArg Fin.val positions
  change index.val = row.val at values
  have indexBefore := index.isLt
  omega

/-- Dually, a row pass preserves inactive zero columns of a compact column input. -/
theorem compactHermiteRows_zero_columns {rows columns rank : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (normalized : IsCompactRowHermite rank original.transpose) :
    ∀ column : Fin columns, rank ≤ column.val → (compactHermiteRows original).2.1.transpose column = 0 := by
  have zero := compactHermiteColumns_zero_rows original.transpose normalized
  simpa only [compactHermiteColumns, Matrix.transpose_transpose] using zero

/-- After a row pass and a column pass, both inactive strips are zero and rank is unchanged. -/
theorem compactHermite_initial_strips {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    let first := compactHermiteRows original
    let second := compactHermiteColumns first.2.1
    second.1 = first.1 ∧
      (∀ row : Fin rows, first.1 ≤ row.val → second.2.1 row = 0) ∧
      (∀ column : Fin columns, first.1 ≤ column.val → second.2.1.transpose column = 0) := by
  let first := compactHermiteRows original
  have shape := (compactHermiteRows_correct original).2.2.2
  have sameRank : (compactHermiteColumns first.2.1).1 = first.1 :=
    (compactHermiteColumns_rank first.2.1).trans shape.rank_eq
  refine ⟨sameRank, compactHermiteColumns_zero_rows first.2.1 shape, ?_⟩
  have columnsShape := (compactHermiteColumns_correct first.2.1).2.2.2
  rw [sameRank] at columnsShape
  obtain ⟨_, _, zeroColumns, _, _, _⟩ := columnsShape
  exact zeroColumns

/-- Perform the two initial passes and accumulate both actual transformations. -/
def compactHermiteInitial {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    ℕ × Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let first := compactHermiteRows original
  let second := compactHermiteColumns first.2.1
  (second.1, second.2.1, second.2.2.1 * first.2.2.1, first.2.2.2 * second.2.2.2)

/-- The initial passes leave a square active block, retaining both bases and all inactive zeros. -/
theorem compactHermiteInitial_correct {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    let result := compactHermiteInitial original
    result.2.2.1 * original * result.2.2.2 = result.2.1 ∧
      IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧
      IsCompactRowHermite result.1 result.2.1.transpose ∧
      (∀ row : Fin rows, result.1 ≤ row.val → result.2.1 row = 0) := by
  let first := compactHermiteRows original
  let second := compactHermiteColumns first.2.1
  have firstCorrect := compactHermiteRows_correct original
  have secondCorrect := compactHermiteColumns_correct first.2.1
  have strips := compactHermite_initial_strips original
  refine ⟨?_, ?_, ?_, secondCorrect.2.2.2, ?_⟩
  · change (second.2.2.1 * first.2.2.1) * original * (first.2.2.2 * second.2.2.2) = second.2.1
    calc
      _ = second.2.2.1 * (first.2.2.1 * original * first.2.2.2) * second.2.2.2 := by simp only [Matrix.mul_assoc]
      _ = second.2.2.1 * first.2.1 * second.2.2.2 := by rw [firstCorrect.1]
      _ = second.2.1 := secondCorrect.1
  · change IsUnit (second.2.2.1 * first.2.2.1).det
    rw [Matrix.det_mul]
    exact secondCorrect.2.1.mul firstCorrect.2.1
  · change IsUnit (first.2.2.2 * second.2.2.2).det
    rw [Matrix.det_mul]
    exact firstCorrect.2.2.1.mul secondCorrect.2.2.1
  · intro row after
    apply strips.2.1 row
    rw [← strips.1]
    exact after

theorem compactHermiteInitial_rank {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    (compactHermiteInitial original).1 = original.rank :=
  (compactHermite_initial_strips original).1.trans (compactHermiteRows_rank original)

/-- Entry width after the initial row and column passes, derived from input dimensions. -/
def hermiteInitialWidth {Scalar : Type} [Semiring Scalar] (rows columns width : Scalar) : Scalar :=
  let firstWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
  2 * (columns * (firstWidth + columns) + 1) + firstWidth + 2 * columns + 2

/-- Composing the fixed pair of passes retains polynomial original-input widths. -/
theorem compactHermiteInitial_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    let firstWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
    let leftWidth := 1 + rows * hermiteSweepBasisIncrement rows width
    let rightWidth := 1 + columns * hermiteSweepBasisIncrement columns firstWidth
    let result := compactHermiteInitial original
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ hermiteInitialWidth rows columns width) ∧
    (∀ row column, (result.2.2.1 row column).natAbs < 2 ^ (leftWidth + rows + 2)) ∧
    (∀ row column, (result.2.2.2 row column).natAbs < 2 ^ (rightWidth + columns + 2)) := by
  have first := compactHermiteRows_bound width original entryBound
  have second := compactHermiteColumns_bound _ (compactHermiteRows original).2.1 first.1
  refine ⟨second.1, ?_, ?_⟩
  · have bounded := mul_bound _ _ (compactHermiteColumns (compactHermiteRows original).2.1).2.2.1
      (compactHermiteRows original).2.2.1 second.2.1 first.2.1
    intro row column
    exact (bounded row column).trans_le (pow_le_pow_right₀ (by decide) (by simp only [Fintype.card_fin]; omega))
  · have bounded := mul_bound _ _ (compactHermiteRows original).2.2.2
      (compactHermiteColumns (compactHermiteRows original).2.1).2.2.2 first.2.2 second.2.2
    intro row column
    exact (bounded row column).trans_le (pow_le_pow_right₀ (by decide) (by simp only [Fintype.card_fin]; omega))

end Polytime2.IntegerMatrix
