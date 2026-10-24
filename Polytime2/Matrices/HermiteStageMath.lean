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

import Polytime2.Matrices.EuclideanSweepMath
import Polytime2.Matrices.HermiteColumnBounds

/-! # An interleaved Hermite elimination stage

Given a positive pivot, a distinct incoming row, and distinct earlier rows
excluding both, clear the incoming entry by the progress-sensitive Hermite
step. Then reduce the earlier entries modulo the new pivot. Both operations
update the actual left basis. Prior columns where the two selected rows were
zero stay unchanged. If the selected column has width `w`, this stage adds
`3*w+3` bits to the independent matrix and basis widths. Global bounds for the
selected column across successive stages still require minor estimates.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- Cancel an incoming entry, then reduce earlier entries against the updated pivot. -/
def hermiteRowStage (source target : Row) (column : Column) (earlierRows : List Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  let eliminated := hermiteRowStep source target column matrix left
  rowRemainderSweep source column earlierRows eliminated.1 eliminated.2

omit [DecidableEq Column] in
/-- Reordering distinct earlier rows leaves both returned matrices unchanged. -/
theorem hermiteRowStage_perm (source target : Row) (column : Column) (earlierRows reordered : List Row)
    (permutation : earlierRows.Perm reordered) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    hermiteRowStage source target column earlierRows matrix left =
      hermiteRowStage source target column reordered matrix left :=
  rowRemainderSweep_perm source column earlierRows reordered permutation distinct sourceExcluded _ _

/-- Once the incoming entry is cleared, a singleton stage performs only remainder normalization. -/
theorem hermiteRowStage_singleton_fold_of_zero (source target : Row) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (targetExcluded : target ∉ earlierRows) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (zero : matrix target column = 0) :
    earlierRows.foldr (fun row state => hermiteRowStage source target column [row] state.1 state.2)
      (matrix, left) = rowRemainderSweep source column earlierRows matrix left := by
  induction earlierRows with
  | nil => rfl
  | cons row earlierRows induction =>
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have tailSource : source ∉ earlierRows := fun member => sourceExcluded (List.mem_cons_of_mem row member)
    have tailTarget : target ∉ earlierRows := fun member => targetExcluded (List.mem_cons_of_mem row member)
    rw [List.foldr_cons, induction tailDistinct tailSource tailTarget]
    have formula := (rowRemainderSweep_apply source column earlierRows tailDistinct tailSource matrix left).1
    have stillZero : (rowRemainderSweep source column earlierRows matrix left).1 target column = 0 := by
      rw [formula, ite_eq_right tailTarget]
      exact zero
    unfold hermiteRowStage
    rw [hermiteRowStep_zero_target source target column _ _ stillZero]
    rfl

/-- A general stage is an initial elimination followed by singleton stage updates. -/
theorem hermiteRowStage_fold_singletons (source target : Row) (different : source ≠ target) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (targetExcluded : target ∉ earlierRows) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    earlierRows.foldr (fun row state => hermiteRowStage source target column [row] state.1 state.2)
      (hermiteRowStep source target column matrix left) =
      hermiteRowStage source target column earlierRows matrix left := by
  exact hermiteRowStage_singleton_fold_of_zero source target column earlierRows distinct sourceExcluded
    targetExcluded _ _ (hermiteRowStep_entries source target different column matrix left positive).2

/-- The forward array-fold schedule agrees with the mathematical interleaved stage. -/
theorem hermiteRowStage_foldl_singletons (source target : Row) (different : source ≠ target) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (targetExcluded : target ∉ earlierRows) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    earlierRows.foldl (fun state row => hermiteRowStage source target column [row] state.1 state.2)
      (hermiteRowStep source target column matrix left) =
      hermiteRowStage source target column earlierRows matrix left := by
  rw [List.foldl_eq_foldr_reverse]
  have reverseDistinct : earlierRows.reverse.Nodup := by simpa using distinct
  have reverseSource : source ∉ earlierRows.reverse := by simpa using sourceExcluded
  have reverseTarget : target ∉ earlierRows.reverse := by simpa using targetExcluded
  rw [hermiteRowStage_fold_singletons source target different column earlierRows.reverse reverseDistinct
    reverseSource reverseTarget matrix left positive]
  exact rowRemainderSweep_perm source column earlierRows.reverse earlierRows (List.reverse_perm _)
    reverseDistinct reverseSource _ _

/-- Every forward stage prefix is the stage on that prefix of the earlier-row list. -/
theorem hermiteRowStage_prefix_succ (source target : Row) (different : source ≠ target) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (targetExcluded : target ∉ earlierRows) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) (count : ℕ) (within : count < earlierRows.length) :
    hermiteRowStage source target column (earlierRows.take (count + 1)) matrix left =
      hermiteRowStage source target column [earlierRows[count]]
        (hermiteRowStage source target column (earlierRows.take count) matrix left).1
        (hermiteRowStage source target column (earlierRows.take count) matrix left).2 := by
  have prefixEquation (length : ℕ) := hermiteRowStage_foldl_singletons source target different column (earlierRows.take length)
    distinct.take (fun member => sourceExcluded (List.mem_of_mem_take member))
    (fun member => targetExcluded (List.mem_of_mem_take member)) matrix left positive
  rw [← prefixEquation (count + 1), List.take_succ_eq_append_getElem within, List.foldl_append, List.foldl_cons, List.foldl_nil,
    prefixEquation count]

/-- Clearing one entry cannot increase the width of the selected column. -/
theorem hermiteRowStep_column_bound (width : ℕ) (source target : Row) (different : source ≠ target)
    (column : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ width) :
    ∀ row, ((hermiteRowStep source target column matrix left).1 row column).natAbs < 2 ^ width := by
  have pivot := hermiteColumnSweep_pivot_le source column [target] (by simp [different]) matrix left positive
  have entries := hermiteRowStep_entries source target different column matrix left positive
  intro row
  by_cases atSource : row = source
  · subst row
    simpa only [hermiteColumnSweep, List.foldr_cons, List.foldr_nil] using pivot.trans_lt (columnBound source)
  · by_cases atTarget : row = target
    · subst row
      rw [entries.2]
      positivity
    · rw [hermiteRowStep_other source target row atSource atTarget]
      exact columnBound row

/-- The stage retains the gcd pivot, cancels the incoming entry, and leaves canonical remainders above it. -/
theorem hermiteRowStage_entries (source target : Row) (different : source ≠ target) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (targetExcluded : target ∉ earlierRows) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    (hermiteRowStage source target column earlierRows matrix left).1 source column =
      Int.gcd (matrix source column) (matrix target column) ∧
    (hermiteRowStage source target column earlierRows matrix left).1 target column = 0 ∧
    ∀ row ∈ earlierRows, 0 ≤ (hermiteRowStage source target column earlierRows matrix left).1 row column ∧
      (hermiteRowStage source target column earlierRows matrix left).1 row column <
        (Int.gcd (matrix source column) (matrix target column) : ℤ) := by
  let eliminated := hermiteRowStep source target column matrix left
  have entries := hermiteRowStep_entries source target different column matrix left positive
  have nextPositive : 0 < eliminated.1 source column := by
    rw [entries.1]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (matrix target column) (ne_of_gt positive)
  have formula := rowRemainderSweep_apply source column earlierRows distinct sourceExcluded eliminated.1 eliminated.2
  have sourceEq := formula.1 source column
  have targetEq := formula.1 target column
  simp only [ite_eq_right sourceExcluded] at sourceEq
  simp only [ite_eq_right targetExcluded] at targetEq
  refine ⟨sourceEq.trans entries.1, targetEq.trans entries.2, ?_⟩
  intro row member
  have range := rowRemainderSweep_range source column earlierRows distinct sourceExcluded eliminated.1 eliminated.2 nextPositive row member
  simpa only [eliminated, hermiteRowStage, entries.1] using range

/-- Rows outside the incoming pair and normalization list retain both matrix and basis rows. -/
theorem hermiteRowStage_rows_other (source target row : Row)
    (notSource : row ≠ source) (notTarget : row ≠ target) (column : Column)
    (earlierRows : List Row) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (rowExcluded : row ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteRowStage source target column earlierRows matrix left).1 row = matrix row ∧
      (hermiteRowStage source target column earlierRows matrix left).2 row = left row := by
  have unchanged := hermiteRowStep_rows_other source target row notSource notTarget column matrix left
  have formula := rowRemainderSweep_apply source column earlierRows distinct sourceExcluded
    (hermiteRowStep source target column matrix left).1 (hermiteRowStep source target column matrix left).2
  constructor
  · funext other
    change (rowRemainderSweep source column earlierRows
      (hermiteRowStep source target column matrix left).1
      (hermiteRowStep source target column matrix left).2).1 row other = _
    rw [formula.1 row other, if_neg rowExcluded]
    exact congrFun unchanged.1 other
  · funext other
    change (rowRemainderSweep source column earlierRows
      (hermiteRowStep source target column matrix left).1
      (hermiteRowStep source target column matrix left).2).2 row other = _
    rw [formula.2 row other, if_neg rowExcluded]
    exact congrFun unchanged.2 other

/-- Old zero columns in the selected rows stay unchanged through both operations. -/
theorem hermiteRowStage_zero_column (source target : Row) (column other : Column) (earlierRows : List Row)
    (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceZero : matrix source other = 0) (targetZero : matrix target other = 0) (row : Row) :
    (hermiteRowStage source target column earlierRows matrix left).1 row other = matrix row other := by
  have unchanged := hermiteRowStep_zero_column source target column other matrix left sourceZero targetZero
  have nextZero := (unchanged source).trans sourceZero
  exact (rowRemainderSweep_zero_column source column other earlierRows distinct sourceExcluded
    (hermiteRowStep source target column matrix left).1 (hermiteRowStep source target column matrix left).2 nextZero row).trans
      (unchanged row)

/-- Interleaved elimination preserves a basis column zero in the selected pair. -/
theorem hermiteRowStage_left_zero_column (source target : Row) (column : Column) (other : Row)
    (earlierRows : List Row) (distinct : earlierRows.Nodup) (excluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceZero : left source other = 0) (targetZero : left target other = 0) (row : Row) :
    (hermiteRowStage source target column earlierRows matrix left).2 row other = left row other := by
  have unchanged := hermiteRowStep_left_zero_column source target column other matrix left sourceZero targetZero
  exact (rowRemainderSweep_left_zero_column source column other earlierRows distinct excluded _ _
    ((unchanged source).trans sourceZero) row).trans (unchanged row)

/-- The combined stage preserves the full original-to-current equation and basis unimodularity. -/
theorem hermiteRowStage_preserves [Fintype Row] [Fintype Column]
    (source target : Row) (different : source ≠ target) (column : Column) (earlierRows : List Row)
    (sourceExcluded : source ∉ earlierRows) (matrix original : Matrix Row Column ℤ)
    (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteRowStage source target column earlierRows matrix left).2 * original * right =
      (hermiteRowStage source target column earlierRows matrix left).1 ∧
      IsUnit (hermiteRowStage source target column earlierRows matrix left).2.det := by
  have eliminated := hermiteRowStep_preserves source target different column matrix original left right equation unit
  exact rowRemainderSweep_preserves source column earlierRows sourceExcluded
    (hermiteRowStep source target column matrix left).1 original
    (hermiteRowStep source target column matrix left).2 right eliminated.1 eliminated.2

/-- Separate pair widths keep a small updated source available for normalization. -/
theorem hermiteRowStage_bound_of_pair (columnWidth pairColumnWidth pairWidth matrixWidth basisWidth : ℕ)
    (source target : Row) (different : source ≠ target) (column : Column) (earlierRows : List Row)
    (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (pivotBound : (matrix source column).natAbs < 2 ^ pairColumnWidth)
    (targetBound : (matrix target column).natAbs < 2 ^ pairColumnWidth)
    (sourceBound : ∀ other, (matrix source other).natAbs < 2 ^ pairWidth)
    (incomingBound : ∀ other, (matrix target other).natAbs < 2 ^ pairWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).1 row other).natAbs <
      2 ^ (max matrixWidth (columnWidth + pairWidth) + (2 * pairColumnWidth + 3))) ∧
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).2 row other).natAbs <
      2 ^ (basisWidth + (columnWidth + 2 * pairColumnWidth + 3))) := by
  have eliminated := hermiteRowStep_bound pairColumnWidth matrixWidth basisWidth source target column matrix left
    pivotBound targetBound matrixBound basisBound
  have smallSource := hermiteRowStep_source_bound pairColumnWidth pairWidth source target different column matrix left
    pivotBound targetBound sourceBound incomingBound
  have normalized := rowRemainderSweep_bound_of_source_column columnWidth
    (matrixWidth + (2 * pairColumnWidth + 2)) (pairWidth + (2 * pairColumnWidth + 2))
    (basisWidth + (2 * pairColumnWidth + 2)) source column earlierRows distinct sourceExcluded
    (hermiteRowStep source target column matrix left).1 (hermiteRowStep source target column matrix left).2
    (hermiteRowStep_column_bound columnWidth source target different column matrix left positive columnBound)
    eliminated.1 smallSource eliminated.2
  exact ⟨fun row other => (normalized.1 row other).trans_le (pow_le_pow_right₀ (by decide) (by omega)),
    fun row other => (normalized.2 row other).trans_le (pow_le_pow_right₀ (by decide) (by omega))⟩

/-- Interleaving normalization has an additive width bound independent of earlier-row count. -/
theorem hermiteRowStage_bound (columnWidth matrixWidth basisWidth : ℕ)
    (source target : Row) (different : source ≠ target) (column : Column) (earlierRows : List Row)
    (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + (3 * columnWidth + 3))) ∧
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).2 row other).natAbs <
      2 ^ (basisWidth + (3 * columnWidth + 3))) := by
  simpa only [max_eq_right (Nat.le_add_left matrixWidth columnWidth), show
      columnWidth + 2 * columnWidth + 3 = 3 * columnWidth + 3 by omega,
    show columnWidth + matrixWidth + (2 * columnWidth + 3) = matrixWidth + (3 * columnWidth + 3) by omega] using
    hermiteRowStage_bound_of_pair columnWidth columnWidth matrixWidth matrixWidth basisWidth
      source target different column earlierRows distinct sourceExcluded matrix left positive columnBound
      (columnBound source) (columnBound target) (matrixBound source) (matrixBound target) matrixBound basisBound

/-- Small selected rows give additive matrix growth even when earlier rows are larger. -/
theorem hermiteRowStage_bound_of_small_pair (pairColumnWidth pairWidth matrixWidth basisWidth : ℕ)
    (source target : Row) (different : source ≠ target) (column : Column) (earlierRows : List Row)
    (distinct : earlierRows.Nodup) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (pivotBound : (matrix source column).natAbs < 2 ^ pairColumnWidth)
    (targetBound : (matrix target column).natAbs < 2 ^ pairColumnWidth)
    (sourceBound : ∀ other, (matrix source other).natAbs < 2 ^ pairWidth)
    (incomingBound : ∀ other, (matrix target other).natAbs < 2 ^ pairWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + pairWidth + (2 * pairColumnWidth + 3))) ∧
    (∀ row other, ((hermiteRowStage source target column earlierRows matrix left).2 row other).natAbs <
      2 ^ (basisWidth + (matrixWidth + 2 * pairColumnWidth + 3))) := by
  simpa only [max_eq_right (Nat.le_add_right matrixWidth pairWidth)] using
    hermiteRowStage_bound_of_pair matrixWidth pairColumnWidth pairWidth matrixWidth basisWidth
      source target different column earlierRows distinct sourceExcluded matrix left positive
      (fun row => matrixBound row column) pivotBound targetBound sourceBound incomingBound matrixBound basisBound

/-- A next forward-prefix update is admissible and fits the same original-width workspace. -/
theorem hermiteRowStage_prefix_fits (width : ℕ) (source target : Row) (different : source ≠ target)
    (column : Column) (earlierRows : List Row) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ width)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ width)
    (count : ℕ) (within : count < earlierRows.length) :
    let state := hermiteRowStage source target column (earlierRows.take count) matrix left
    let token := earlierRows[count]
    (source ≠ target ∧ source ≠ token ∧ token ≠ target ∧ 0 < state.1 source column) ∧
    (∀ row other, ((hermiteRowStage source target column [token] state.1 state.2).1 row other).natAbs <
      2 ^ (4 * width + 3)) ∧
    (∀ row other, ((hermiteRowStage source target column [token] state.1 state.2).2 row other).natAbs <
      2 ^ (4 * width + 3)) := by
  have member : earlierRows[count] ∈ earlierRows := List.getElem_mem within
  have entries := hermiteRowStage_entries source target different column (earlierRows.take count) distinct.take
    (fun old => sourceExcluded (List.mem_of_mem_take old))
    (fun old => targetExcluded (List.mem_of_mem_take old)) matrix left positive
  refine ⟨⟨different, ?_, ?_, ?_⟩, ?_⟩
  · intro same
    exact sourceExcluded (same.symm ▸ member)
  · intro same
    exact targetExcluded (same ▸ member)
  · rw [entries.1]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (matrix target column) (ne_of_gt positive)
  · have recurrence := hermiteRowStage_prefix_succ source target different column earlierRows distinct
      sourceExcluded targetExcluded matrix left positive count within
    rw [← recurrence]
    have bounds := hermiteRowStage_bound width width width source target different column
      (earlierRows.take (count + 1)) distinct.take (fun old => sourceExcluded (List.mem_of_mem_take old))
      matrix left positive (fun row => matrixBound row column) matrixBound basisBound
    simpa only [show width + (3 * width + 3) = 4 * width + 3 by omega] using bounds

end Polytime2.IntegerMatrix
