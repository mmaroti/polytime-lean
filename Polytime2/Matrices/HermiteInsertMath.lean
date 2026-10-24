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

import Polytime2.Matrices.HermiteIncomingBounds
import Polytime2.Matrices.HermitePivotMath

/-! # Inserting one row into a normalized Hermite block

Clear the incoming row in the old pivot columns, then search its residual row.
If it vanishes, keep the old rank. Otherwise make the selected residual entry
positive and normalize the earlier rows against it. Return the actual matrix,
left basis, and optional new pivot coordinate. No invalid coordinate is exposed.
The outer traversal over successive input rows is separate.
-/

namespace Polytime2.IntegerMatrix

variable {Row : Type} [DecidableEq Row] [Fintype Row] {columns pivots : ℕ}

omit [DecidableEq Row] [Fintype Row] in
private theorem incomingTarget_excluded (selectedRows : Fin (pivots + 1) ↪ Row) :
    selectedRows (Fin.last pivots) ∉ Set.range (Fin.Embedding.init selectedRows) := by
  rintro ⟨index, same⟩
  have equal := selectedRows.injective same
  have values := congrArg Fin.val equal
  change index.val = pivots at values
  exact (ne_of_lt index.isLt) values

/-- Insert one incoming row, returning a new pivot exactly when the residual row is nonzero. -/
def hermiteInsertRow (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Fin columns)
    (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ) :
    (Matrix Row (Fin columns) ℤ × Matrix Row Row ℤ) × Option (Fin columns) :=
  let cleared := hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left
  match hermiteResidualPivot (selectedRows (Fin.last pivots)) cleared.1 with
  | none => (cleared, none)
  | some column => (hermiteExtendPivot (Fin.Embedding.init selectedRows) (selectedRows (Fin.last pivots)) column
      cleared.1 cleared.2, some column)

/-- Equal finite dimensions and pointwise equal coordinates and matrices give
heterogeneously equal insertion results, without choosing storage casts. -/
theorem hermiteInsertRow_congr {firstRows secondRows firstColumns secondColumns firstPivots secondPivots : ℕ}
    (rowsEqual : firstRows = secondRows) (columnsEqual : firstColumns = secondColumns)
    (pivotsEqual : firstPivots = secondPivots)
    (firstSelection : Fin (firstPivots + 1) ↪ Fin firstRows)
    (secondSelection : Fin (secondPivots + 1) ↪ Fin secondRows)
    (firstPivotColumns : Fin firstPivots → Fin firstColumns)
    (secondPivotColumns : Fin secondPivots → Fin secondColumns)
    (firstMatrix : Matrix (Fin firstRows) (Fin firstColumns) ℤ)
    (secondMatrix : Matrix (Fin secondRows) (Fin secondColumns) ℤ)
    (firstLeft : Matrix (Fin firstRows) (Fin firstRows) ℤ)
    (secondLeft : Matrix (Fin secondRows) (Fin secondRows) ℤ)
    (selectionValues : ∀ (first : Fin (firstPivots + 1)) (second : Fin (secondPivots + 1)), first.val = second.val →
      (firstSelection first).val = (secondSelection second).val)
    (columnValues : ∀ (first : Fin firstPivots) (second : Fin secondPivots), first.val = second.val →
      (firstPivotColumns first).val = (secondPivotColumns second).val)
    (matrixValues : ∀ (firstRow : Fin firstRows) (secondRow : Fin secondRows)
      (firstColumn : Fin firstColumns) (secondColumn : Fin secondColumns),
      firstRow.val = secondRow.val → firstColumn.val = secondColumn.val →
      firstMatrix firstRow firstColumn = secondMatrix secondRow secondColumn)
    (leftValues : ∀ (firstRow : Fin firstRows) (secondRow : Fin secondRows)
      (firstColumn : Fin firstRows) (secondColumn : Fin secondRows),
      firstRow.val = secondRow.val → firstColumn.val = secondColumn.val →
      firstLeft firstRow firstColumn = secondLeft secondRow secondColumn) :
    HEq (hermiteInsertRow firstSelection firstPivotColumns firstMatrix firstLeft)
      (hermiteInsertRow secondSelection secondPivotColumns secondMatrix secondLeft) := by
  subst secondRows
  subst secondColumns
  subst secondPivots
  have selectionEqual : firstSelection = secondSelection := by
    ext index
    exact selectionValues index index rfl
  have pivotEqual : firstPivotColumns = secondPivotColumns := by
    funext index
    exact Fin.ext (columnValues index index rfl)
  have matrixEqual : firstMatrix = secondMatrix := by
    ext row column
    exact matrixValues row row column column rfl rfl
  have leftEqual : firstLeft = secondLeft := by
    ext row column
    exact leftValues row row column column rfl rfl
  cases selectionEqual
  cases pivotEqual
  cases matrixEqual
  cases leftEqual
  rfl

/-- Reindex equal finite matrix dimensions and the optional column to obtain
ordinary equality from heterogeneous equality of insertion results. -/
theorem hermiteInsertResult_cast {firstRows secondRows firstColumns secondColumns : ℕ}
    (rowsEqual : firstRows = secondRows) (columnsEqual : firstColumns = secondColumns)
    (first : (Matrix (Fin firstRows) (Fin firstColumns) ℤ × Matrix (Fin firstRows) (Fin firstRows) ℤ) ×
      Option (Fin firstColumns))
    (second : (Matrix (Fin secondRows) (Fin secondColumns) ℤ × Matrix (Fin secondRows) (Fin secondRows) ℤ) ×
      Option (Fin secondColumns)) (same : HEq first second) :
    ((fun row column => first.1.1 (Fin.cast rowsEqual.symm row) (Fin.cast columnsEqual.symm column),
      fun row column => first.1.2 (Fin.cast rowsEqual.symm row) (Fin.cast rowsEqual.symm column)),
      first.2.map (Fin.cast columnsEqual)) = second := by
  subst secondRows
  subst secondColumns
  have equal := eq_of_heq same
  subst second
  simp only [Fin.cast_refl, id_eq, Option.map_id]
  rcases first with ⟨⟨matrix, left⟩, pivot⟩
  rfl

/-- The optional returned coordinate is exactly the shared residual search result. -/
theorem hermiteInsertRow_pivot (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Fin columns)
    (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ) :
    (hermiteInsertRow selectedRows pivotColumns matrix left).2 =
      hermiteResidualPivot (selectedRows (Fin.last pivots))
        (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).1 := by
  dsimp only [hermiteInsertRow]
  split <;> symm <;> assumption

/-- A dependent incoming row leaves a zero residual and keeps the cleared matrix pair. -/
theorem hermiteInsertRow_none (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Fin columns)
    (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ)
    (stopped : (hermiteInsertRow selectedRows pivotColumns matrix left).2 = none) :
    (hermiteInsertRow selectedRows pivotColumns matrix left).1 =
        hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left ∧
      (hermiteInsertRow selectedRows pivotColumns matrix left).1.1 (selectedRows (Fin.last pivots)) = 0 := by
  have search := (hermiteInsertRow_pivot selectedRows pivotColumns matrix left).symm.trans stopped
  have zero := (hermiteResidualPivot_none _ _).mp search
  have exactPair : (hermiteInsertRow selectedRows pivotColumns matrix left).1 =
      hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left := by
    simp only [hermiteInsertRow, search]
  exact ⟨exactPair, by rw [exactPair]; exact zero⟩

/-- Insertion retains the full accumulated presentation and unimodularity in both branches. -/
theorem hermiteInsertRow_preserves (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Fin columns) (matrix original : Matrix Row (Fin columns) ℤ)
    (left : Matrix Row Row ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteInsertRow selectedRows pivotColumns matrix left).1.2 * original * right =
        (hermiteInsertRow selectedRows pivotColumns matrix left).1.1 ∧
      IsUnit (hermiteInsertRow selectedRows pivotColumns matrix left).1.2.det := by
  have cleared := hermiteIncomingPrefix_preserves selectedRows pivotColumns pivots matrix original left right equation unit
  dsimp only [hermiteInsertRow]
  split
  · exact cleared
  · exact hermiteExtendPivot_preserves _ _ _ (incomingTarget_excluded selectedRows) _ original _ right cleared.1 cleared.2

/-- Insertion preserves every unselected matrix row and its actual basis row. -/
theorem hermiteInsertRow_rows_other (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Fin columns) (row : Row) (outside : row ∉ Set.range selectedRows)
    (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ) :
    (hermiteInsertRow selectedRows pivotColumns matrix left).1.1 row = matrix row ∧
      (hermiteInsertRow selectedRows pivotColumns matrix left).1.2 row = left row := by
  have notTarget : row ≠ selectedRows (Fin.last pivots) := fun same => outside ⟨Fin.last pivots, same.symm⟩
  have cleared := hermiteIncomingPrefix_rows_other selectedRows pivotColumns pivots row notTarget
    (fun index _ same => outside ⟨index.castSucc, same.symm⟩) matrix left
  have notActive : row ∉ Set.range (Fin.Embedding.init selectedRows) := by
    rintro ⟨index, same⟩
    exact outside ⟨index.castSucc, same⟩
  dsimp only [hermiteInsertRow]
  split
  · exact cleared
  · rename_i column found
    have grown := hermiteExtendPivot_rows_other (Fin.Embedding.init selectedRows) _ row column
      (incomingTarget_excluded selectedRows) notActive notTarget
      (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).1
      (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).2
    exact ⟨grown.1.trans cleared.1, grown.2.trans cleared.2⟩

/-- A basis column zero on selected rows is unchanged by the complete insertion. -/
theorem hermiteInsertRow_left_zero_column (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Fin columns) (other : Row)
    (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ)
    (zero : ∀ index, left (selectedRows index) other = 0) :
    ∀ row, (hermiteInsertRow selectedRows pivotColumns matrix left).1.2 row other = left row other := by
  have cleared := hermiteIncomingPrefix_left_zero_column selectedRows pivotColumns pivots other matrix left zero
  dsimp only [hermiteInsertRow]
  split
  · exact cleared
  · rename_i column found
    have grown := hermiteExtendPivot_left_zero_column (Fin.Embedding.init selectedRows)
      (selectedRows (Fin.last pivots)) column other (incomingTarget_excluded selectedRows)
      (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).1
      (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).2
      ((cleared _).trans (zero (Fin.last pivots)))
    intro row
    exact (grown row).trans (cleared row)

/-- A dependent insertion retains a normalized old pivot block. -/
theorem hermiteInsertRow_normalized_none (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Fin columns) (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (stopped : (hermiteInsertRow selectedRows pivotColumns matrix left).2 = none) :
    let result := (hermiteInsertRow selectedRows pivotColumns matrix left).1.1
    let rows : Fin pivots → Row := fun index => selectedRows index.castSucc
    (result.submatrix rows pivotColumns).IsUpperTriangular ∧
      (∀ index, 0 < result (rows index) (pivotColumns index)) ∧
      (∀ row column : Fin pivots, row < column →
        0 ≤ result (rows row) (pivotColumns column) ∧
          result (rows row) (pivotColumns column) < result (rows column) (pivotColumns column)) := by
  rw [(hermiteInsertRow_none selectedRows pivotColumns matrix left stopped).1]
  exact hermiteIncomingPrefix_normalized selectedRows pivotColumns matrix left positive upper

/-- An independent insertion returns a new pivot and a normalized extended block. -/
theorem hermiteInsertRow_normalized_some (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Fin columns) (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0) (column : Fin columns)
    (found : (hermiteInsertRow selectedRows pivotColumns matrix left).2 = some column) :
    column ∉ Set.range pivotColumns ∧
    let result := (hermiteInsertRow selectedRows pivotColumns matrix left).1.1
    let extendedColumns := Fin.snoc (α := fun _ => Fin columns) pivotColumns column
    (result.submatrix selectedRows extendedColumns).IsUpperTriangular ∧
      (∀ index, 0 < result (selectedRows index) (extendedColumns index)) ∧
      (∀ row other : Fin (pivots + 1), row < other →
        0 ≤ result (selectedRows row) (extendedColumns other) ∧
          result (selectedRows row) (extendedColumns other) < result (selectedRows other) (extendedColumns other)) := by
  let cleared := hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left
  have search := (hermiteInsertRow_pivot selectedRows pivotColumns matrix left).symm.trans found
  have sourceZero (index : Fin pivots) : cleared.1 (selectedRows (Fin.last pivots)) (pivotColumns index) = 0 :=
    (hermiteIncomingPrefix_entries selectedRows pivotColumns pivots (by rfl) matrix left positive upper index index.isLt).2.1
  refine ⟨hermiteResidualPivot_not_pivot _ _ pivotColumns sourceZero column search, ?_⟩
  have normalized := hermiteIncomingPrefix_normalized selectedRows pivotColumns matrix left positive upper
  have grown := hermiteExtendPivot_normalized (Fin.Embedding.init selectedRows) pivotColumns
    (selectedRows (Fin.last pivots)) column (incomingTarget_excluded selectedRows) cleared.1 cleared.2
    normalized.1 normalized.2.1 normalized.2.2 sourceZero (hermiteResidualPivot_nonzero _ _ _ search)
  have exactPair : (hermiteInsertRow selectedRows pivotColumns matrix left).1 =
      hermiteExtendPivot (Fin.Embedding.init selectedRows) (selectedRows (Fin.last pivots)) column cleared.1 cleared.2 := by
    simp only [hermiteInsertRow, search, cleared]
  have snocRows : Fin.snoc (α := fun _ => Row) (Fin.Embedding.init selectedRows)
      (selectedRows (Fin.last pivots)) = (selectedRows : Fin (pivots + 1) → Row) := by
    change Fin.snoc (Fin.init (selectedRows : Fin (pivots + 1) → Row))
      (selectedRows (Fin.last pivots)) = _
    exact Fin.snoc_init_self _
  rw [exactPair]
  simpa only [snocRows] using grown

/-- Insertion has polynomial matrix and basis widths in the original row-traversal input sizes. -/
theorem hermiteInsertRow_bound (width basisWidth : ℕ) (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots ↪ Fin columns) (matrix : Matrix Row (Fin columns) ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ basisWidth) :
    let pairWidth := (pivots + 1) * (width + (pivots + 1)) + 1
    let matrixWidth := width + pivots * (3 * pairWidth + 3)
    let leftWidth := basisWidth + pivots * (width + pivots * (3 * pairWidth + 3) + 2 * pairWidth + 3)
    (∀ row column, ((hermiteInsertRow selectedRows pivotColumns matrix left).1.1 row column).natAbs <
      2 ^ (2 * matrixWidth + 1)) ∧
    (∀ row column, ((hermiteInsertRow selectedRows pivotColumns matrix left).1.2 row column).natAbs <
      2 ^ (matrixWidth + leftWidth + 1)) := by
  have cleared := hermiteIncomingPrefix_bound width basisWidth pivots (by rfl) selectedRows pivotColumns
    matrix left positive upper entryBound basisBound
  dsimp only [hermiteInsertRow]
  split
  · exact ⟨fun row column => (cleared.1 row column).trans_le (pow_le_pow_right₀ (by decide) (by omega)),
      fun row column => (cleared.2 row column).trans_le (pow_le_pow_right₀ (by decide) (by omega))⟩
  · exact hermiteExtendPivot_bound _ _ _ _ _ (incomingTarget_excluded selectedRows) _ _ cleared.1 cleared.2

end Polytime2.IntegerMatrix
