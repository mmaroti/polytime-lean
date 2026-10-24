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

import Polytime2.Arrays.FindFalseMath
import Polytime2.Matrices.HermiteExtendMath
import Polytime2.Matrices.NegateMath

/-! # Sign normalization and extension by a nonzero residual pivot

A nonzero entry of a residual row can extend the old normalized pivot block.
Negate the entire residual row and its accumulated basis row when the selected
entry is negative, then normalize the earlier rows with the existing remainder
sweep. This preserves the presentation and unimodularity. The shared finite-array
search returns a nonzero coordinate or certifies that
the entire residual row is zero. A returned coordinate cannot repeat a pivot
column already cleared in that row.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type}

/-- Find a nonzero residual coordinate using the shared finite-array search. -/
def hermiteResidualPivot {columns : ℕ} (source : Row) (matrix : Matrix Row (Fin columns) ℤ) :
    Option (Fin columns) :=
  ArraySearch.firstFalse (fun column => decide (matrix source column = 0))

/-- No residual pivot means the entire incoming row is zero. -/
theorem hermiteResidualPivot_none {columns : ℕ} (source : Row) (matrix : Matrix Row (Fin columns) ℤ) :
    hermiteResidualPivot source matrix = none ↔ matrix source = 0 := by
  simp only [hermiteResidualPivot, ArraySearch.firstFalse_none, decide_eq_true_eq, funext_iff, Pi.zero_apply]

/-- A returned residual coordinate has a genuinely nonzero entry. -/
theorem hermiteResidualPivot_nonzero {columns : ℕ} (source : Row)
    (matrix : Matrix Row (Fin columns) ℤ) (column : Fin columns)
    (found : hermiteResidualPivot source matrix = some column) : matrix source column ≠ 0 := by
  have selected := ArraySearch.firstFalse_found (fun column => decide (matrix source column = 0)) column found
  simpa only [decide_eq_false_iff_not] using selected

/-- A residual pivot cannot repeat an old pivot column already cleared in the incoming row. -/
theorem hermiteResidualPivot_not_pivot {columns rank : ℕ} (source : Row)
    (matrix : Matrix Row (Fin columns) ℤ) (pivotColumns : Fin rank → Fin columns)
    (sourceZero : ∀ index, matrix source (pivotColumns index) = 0) (column : Fin columns)
    (found : hermiteResidualPivot source matrix = some column) : column ∉ Set.range pivotColumns := by
  rintro ⟨index, same⟩
  exact hermiteResidualPivot_nonzero source matrix column found (by rw [← same]; exact sourceZero index)

variable [DecidableEq Row] [Fintype Row]

/-- Make the selected entry nonnegative, applying the same sign change to the left basis. -/
def positivePivotWithLeft (source : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  if matrix source column < 0 then (rowNegate source matrix, rowNegate source left) else (matrix, left)

theorem positivePivotWithLeft_entry (source : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (positivePivotWithLeft source column matrix left).1 source column = |matrix source column| := by
  by_cases negative : matrix source column < 0
  · simp only [positivePivotWithLeft, ite_eq_left negative, rowNegate_apply, ite_true, abs_of_neg negative]
  · simp only [positivePivotWithLeft, ite_eq_right negative, abs_of_nonneg (le_of_not_gt negative)]

theorem positivePivotWithLeft_rows_other (source row : Row) (different : row ≠ source) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (positivePivotWithLeft source column matrix left).1 row = matrix row ∧
      (positivePivotWithLeft source column matrix left).2 row = left row := by
  unfold positivePivotWithLeft
  split_ifs <;> constructor <;> funext other <;> simp only [rowNegate_apply, ite_eq_right different]

theorem positivePivotWithLeft_zero_column (source : Row) (column other : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : matrix source other = 0) :
    ∀ row, (positivePivotWithLeft source column matrix left).1 row other = matrix row other := by
  intro row
  unfold positivePivotWithLeft
  split_ifs
  · exact rowNegate_zero_column source other matrix zero row
  · rfl

/-- Sign normalization also preserves a zero source entry in an entire basis column. -/
theorem positivePivotWithLeft_left_zero_column (source : Row) (column : Column) (other : Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : left source other = 0) :
    ∀ row, (positivePivotWithLeft source column matrix left).2 row other = left row other := by
  intro row
  unfold positivePivotWithLeft
  split_ifs
  · exact rowNegate_zero_column source other left zero row
  · rfl

theorem positivePivotWithLeft_preserves [Fintype Column] (source : Row) (column : Column)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (positivePivotWithLeft source column matrix left).2 * original * right =
        (positivePivotWithLeft source column matrix left).1 ∧
      IsUnit (positivePivotWithLeft source column matrix left).2.det := by
  unfold positivePivotWithLeft
  split_ifs
  · constructor
    · change (Matrix.rowScale source (-1) * left) * original * right = Matrix.rowScale source (-1) * matrix
      calc
        _ = Matrix.rowScale source (-1) * (left * original * right) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [equation]
    · change IsUnit (Matrix.rowScale source (-1) * left).det
      rw [Matrix.det_mul, rowNegate_unimodular]
      exact isUnit_neg_one.mul unit
  · exact ⟨equation, unit⟩

theorem positivePivotWithLeft_bound (matrixWidth basisWidth : ℕ) (source : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((positivePivotWithLeft source column matrix left).1 row other).natAbs < 2 ^ matrixWidth) ∧
    (∀ row other, ((positivePivotWithLeft source column matrix left).2 row other).natAbs < 2 ^ basisWidth) := by
  unfold positivePivotWithLeft
  split_ifs
  · exact ⟨rowNegate_bound _ _ _ matrixBound, rowNegate_bound _ _ _ basisBound⟩
  · exact ⟨matrixBound, basisBound⟩

/-- Extend by a supplied nonzero residual entry, deriving its positive sign internally. -/
def hermiteExtendPivot {rank : ℕ} (activeRows : Fin rank ↪ Row) (source : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  let signed := positivePivotWithLeft source column matrix left
  rowRemainderSweep source column ((List.finRange rank).map activeRows) signed.1 signed.2

/-- The caller supplies a nonzero entry; its sign is not a precondition. -/
theorem hermiteExtendPivot_normalized {rank : ℕ} (activeRows : Fin rank ↪ Row)
    (pivotColumns : Fin rank → Column) (source : Row) (column : Column)
    (excluded : source ∉ Set.range activeRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (upper : (matrix.submatrix activeRows pivotColumns).IsUpperTriangular)
    (positive : ∀ index, 0 < matrix (activeRows index) (pivotColumns index))
    (reduced : ∀ row other : Fin rank, row < other →
      0 ≤ matrix (activeRows row) (pivotColumns other) ∧
        matrix (activeRows row) (pivotColumns other) < matrix (activeRows other) (pivotColumns other))
    (sourceZero : ∀ index, matrix source (pivotColumns index) = 0)
    (nonzero : matrix source column ≠ 0) :
    let result := (hermiteExtendPivot activeRows source column matrix left).1
    let rows := Fin.snoc (α := fun _ => Row) activeRows source
    let columns := Fin.snoc (α := fun _ => Column) pivotColumns column
    (result.submatrix rows columns).IsUpperTriangular ∧
      (∀ index, 0 < result (rows index) (columns index)) ∧
      (∀ row other : Fin (rank + 1), row < other →
        0 ≤ result (rows row) (columns other) ∧
          result (rows row) (columns other) < result (rows other) (columns other)) := by
  let signed := positivePivotWithLeft source column matrix left
  have activeSame (index : Fin rank) : signed.1 (activeRows index) = matrix (activeRows index) :=
    (positivePivotWithLeft_rows_other source (activeRows index)
      (fun same => excluded ⟨index, same⟩) column matrix left).1
  have oldBlock : signed.1.submatrix activeRows pivotColumns = matrix.submatrix activeRows pivotColumns := by
    ext row other
    exact congrFun (activeSame row) (pivotColumns other)
  apply rowRemainderSweep_extend_normalized activeRows pivotColumns source column excluded signed.1 signed.2
  · rw [oldBlock]; exact upper
  · intro index; rw [activeSame]; exact positive index
  · intro row other below; rw [activeSame, activeSame]; exact reduced row other below
  · intro index
    exact (positivePivotWithLeft_zero_column source column (pivotColumns index) matrix left (sourceZero index) source).trans
      (sourceZero index)
  · rw [positivePivotWithLeft_entry]
    exact abs_pos.mpr nonzero

/-- Extending by an already positive pivot preserves all diagonal entries when earlier pivot columns vanish. -/
theorem hermiteExtendPivot_diagonal_of_positive {dimension rank : ℕ}
    (activeRows : Fin rank ↪ Fin dimension) (source : Fin dimension) (excluded : source ∉ Set.range activeRows)
    (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : 0 < matrix source source) (zero : ∀ index, matrix source (activeRows index) = 0) :
    ∀ index, (hermiteExtendPivot activeRows source source matrix left).1 index index = matrix index index := by
  let targets := (List.finRange rank).map activeRows
  have sourceExcluded : source ∉ targets := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact excluded ⟨index, same⟩
  have formula := (rowRemainderSweep_apply source source targets ((List.nodup_finRange rank).map activeRows.injective)
    sourceExcluded matrix left).1
  intro index
  change (rowRemainderSweep source source targets (positivePivotWithLeft source source matrix left).1
    (positivePivotWithLeft source source matrix left).2).1 index index = _
  simp only [positivePivotWithLeft, ite_eq_right (not_lt.mpr positive.le)]
  rw [formula]
  split_ifs with member
  · obtain ⟨old, _, same⟩ := List.mem_map.mp member
    have sourceZero : matrix source index = 0 := by rw [← same]; exact zero old
    rw [sourceZero, mul_zero, sub_zero]
  · rfl

/-- Rank growth leaves rows outside its active rows and incoming source untouched. -/
theorem hermiteExtendPivot_rows_other {rank : ℕ} (activeRows : Fin rank ↪ Row)
    (source row : Row) (column : Column) (sourceExcluded : source ∉ Set.range activeRows)
    (rowExcluded : row ∉ Set.range activeRows) (different : row ≠ source)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteExtendPivot activeRows source column matrix left).1 row = matrix row ∧
      (hermiteExtendPivot activeRows source column matrix left).2 row = left row := by
  let targets := (List.finRange rank).map activeRows
  have sourceNotMember : source ∉ targets := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact sourceExcluded ⟨index, same⟩
  have rowNotMember : row ∉ targets := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact rowExcluded ⟨index, same⟩
  have signed := positivePivotWithLeft_rows_other source row different column matrix left
  have formula := rowRemainderSweep_apply source column targets ((List.nodup_finRange rank).map activeRows.injective)
    sourceNotMember (positivePivotWithLeft source column matrix left).1 (positivePivotWithLeft source column matrix left).2
  constructor
  · funext other
    change (rowRemainderSweep source column targets _ _).1 row other = _
    rw [formula.1, ite_eq_right rowNotMember]
    exact congrFun signed.1 other
  · funext other
    change (rowRemainderSweep source column targets _ _).2 row other = _
    rw [formula.2, ite_eq_right rowNotMember]
    exact congrFun signed.2 other

/-- A zero source basis entry is preserved through sign-aware rank growth. -/
theorem hermiteExtendPivot_left_zero_column {rank : ℕ} (activeRows : Fin rank ↪ Row)
    (source : Row) (column : Column) (other : Row) (excluded : source ∉ Set.range activeRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : left source other = 0) (row : Row) :
    (hermiteExtendPivot activeRows source column matrix left).2 row other = left row other := by
  have sourceExcluded : source ∉ (List.finRange rank).map activeRows := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact excluded ⟨index, same⟩
  have signed := positivePivotWithLeft_left_zero_column source column other matrix left zero
  exact (rowRemainderSweep_left_zero_column source column other _
    ((List.nodup_finRange rank).map activeRows.injective) sourceExcluded _ _
    ((signed source).trans zero) row).trans (signed row)

/-- Sign normalization and the remainder sweep retain the full accumulated presentation. -/
theorem hermiteExtendPivot_preserves [Fintype Column] {rank : ℕ} (activeRows : Fin rank ↪ Row)
    (source : Row) (column : Column) (excluded : source ∉ Set.range activeRows)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteExtendPivot activeRows source column matrix left).2 * original * right =
        (hermiteExtendPivot activeRows source column matrix left).1 ∧
      IsUnit (hermiteExtendPivot activeRows source column matrix left).2.det := by
  have sourceExcluded : source ∉ (List.finRange rank).map activeRows := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact excluded ⟨index, same⟩
  have signed := positivePivotWithLeft_preserves source column matrix original left right equation unit
  exact rowRemainderSweep_preserves source column _ sourceExcluded
    (positivePivotWithLeft source column matrix left).1 original
    (positivePivotWithLeft source column matrix left).2 right signed.1 signed.2

/-- A rank-growth step derives output widths without a sign-dependent capacity. -/
theorem hermiteExtendPivot_bound {rank : ℕ} (matrixWidth basisWidth : ℕ) (activeRows : Fin rank ↪ Row)
    (source : Row) (column : Column) (excluded : source ∉ Set.range activeRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteExtendPivot activeRows source column matrix left).1 row other).natAbs <
      2 ^ (2 * matrixWidth + 1)) ∧
    (∀ row other, ((hermiteExtendPivot activeRows source column matrix left).2 row other).natAbs <
      2 ^ (matrixWidth + basisWidth + 1)) := by
  have sourceExcluded : source ∉ (List.finRange rank).map activeRows := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact excluded ⟨index, same⟩
  have signed := positivePivotWithLeft_bound matrixWidth basisWidth source column matrix left matrixBound basisBound
  exact rowRemainderSweep_bound matrixWidth basisWidth source column _
    ((List.nodup_finRange rank).map activeRows.injective) sourceExcluded _ _ signed.1 signed.2

end Polytime2.IntegerMatrix
