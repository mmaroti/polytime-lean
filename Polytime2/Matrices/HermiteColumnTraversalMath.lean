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

import Polytime2.Matrices.HermiteColumnBounds
import Mathlib.Data.List.FinRange

/-! # Canonical prefixes of a Hermite column traversal

Visit rows in increasing order, skipping the source. After a prefix, the
mathematical state is the existing column sweep with the visited targets in
reverse order. Its recurrence matches a left array fold, while the existing
column-sweep theorems supply zero entries and polynomial prefix widths.
-/

namespace Polytime2.IntegerMatrix

variable {rows : ℕ} {Column : Type} [DecidableEq Column]

/-- Internal reverse schedule for rows already visited by an increasing traversal. -/
def hermiteColumnTargets (source : Fin rows) (count : ℕ) : List (Fin rows) :=
  (((List.finRange rows).take count).filter (fun row => decide (row ≠ source))).reverse

theorem hermiteColumnTargets_mem (source : Fin rows) (count : ℕ) (row : Fin rows) :
    row ∈ hermiteColumnTargets source count ↔ row.val < count ∧ row ≠ source := by
  simp only [hermiteColumnTargets, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
  rw [List.mem_take_iff_idxOf_lt (by simp), List.idxOf_finRange]

theorem hermiteColumnTargets_excluded (source : Fin rows) (count : ℕ) :
    source ∉ hermiteColumnTargets source count := by simp [hermiteColumnTargets_mem]

theorem hermiteColumnTargets_distinct (source : Fin rows) (count : ℕ) :
    (hermiteColumnTargets source count).Nodup := by
  have initial : ((List.finRange rows).take count).Nodup := (List.nodup_finRange rows).take
  exact List.nodup_reverse.mpr (initial.filter _)

theorem hermiteColumnTargets_length (source : Fin rows) (count : ℕ) :
    (hermiteColumnTargets source count).length ≤ count := by
  simp only [hermiteColumnTargets, List.length_reverse]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

theorem hermiteColumnTargets_succ (source index : Fin rows) :
    hermiteColumnTargets source (index.val + 1) =
      if index = source then hermiteColumnTargets source index.val
      else index :: hermiteColumnTargets source index.val := by
  have step := List.take_succ_eq_append_getElem (l := List.finRange rows) (i := index.val) (by simp)
  unfold hermiteColumnTargets
  rw [step]
  by_cases same : index = source <;> simp [List.filter_append, same]

/-- Before reaching the source, the reverse schedule is exactly the reversed visited prefix. -/
theorem hermiteColumnTargets_before_source (source : Fin rows) (count : ℕ) (before : count ≤ source.val) :
    hermiteColumnTargets source count = ((List.finRange rows).take count).reverse := by
  unfold hermiteColumnTargets
  congr 1
  apply List.filter_eq_self.mpr
  intro row member
  have within : row.val < count := by
    rw [List.mem_take_iff_idxOf_lt (by simp), List.idxOf_finRange] at member
    exact member
  have different : row ≠ source := by intro same; subst row; omega
  simpa only [decide_eq_true_eq] using different

/-- The mathematical accumulator of the canonical row traversal. -/
def hermiteColumnPrefix (source : Fin rows) (column : Column) (count : ℕ)
    (matrix : Matrix (Fin rows) Column ℤ) (left : Matrix (Fin rows) (Fin rows) ℤ) :=
  hermiteColumnSweep source column (hermiteColumnTargets source count) matrix left

omit [DecidableEq Column] in
theorem hermiteColumnPrefix_zero (source : Fin rows) (column : Column)
    (matrix : Matrix (Fin rows) Column ℤ) (left : Matrix (Fin rows) (Fin rows) ℤ) :
    hermiteColumnPrefix source column 0 matrix left = (matrix, left) := rfl

omit [DecidableEq Column] in
/-- The pure prefix recurrence is exactly a left-fold update with a source skip. -/
theorem hermiteColumnPrefix_succ (source index : Fin rows) (column : Column)
    (matrix : Matrix (Fin rows) Column ℤ) (left : Matrix (Fin rows) (Fin rows) ℤ) :
    hermiteColumnPrefix source column (index.val + 1) matrix left =
      if index = source then hermiteColumnPrefix source column index.val matrix left
      else hermiteRowStep source index column
        (hermiteColumnPrefix source column index.val matrix left).1
        (hermiteColumnPrefix source column index.val matrix left).2 := by
  simp only [hermiteColumnPrefix, hermiteColumnTargets_succ]
  split_ifs <;> rfl

/-- Visited nonsource rows have zero entries; the pivot stays positive. -/
theorem hermiteColumnPrefix_entries (source : Fin rows) (column : Column) (count : ℕ)
    (matrix : Matrix (Fin rows) Column ℤ) (left : Matrix (Fin rows) (Fin rows) ℤ)
    (positive : 0 < matrix source column) :
    0 < (hermiteColumnPrefix source column count matrix left).1 source column ∧
      ∀ row : Fin rows, row.val < count → row ≠ source →
        (hermiteColumnPrefix source column count matrix left).1 row column = 0 := by
  have entries := hermiteColumnSweep_entries source column (hermiteColumnTargets source count)
    (hermiteColumnTargets_excluded source count) matrix left positive
  exact ⟨entries.1, fun row before different => entries.2 row
    ((hermiteColumnTargets_mem source count row).mpr ⟨before, different⟩)⟩

/-- Prefix widths use the number of visited positions, including the skipped source. -/
theorem hermiteColumnPrefix_bound (columnWidth matrixWidth basisWidth : ℕ)
    (source : Fin rows) (column : Column) (count : ℕ)
    (matrix : Matrix (Fin rows) Column ℤ) (left : Matrix (Fin rows) (Fin rows) ℤ) (positive : 0 < matrix source column)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteColumnPrefix source column count matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + count * (2 * columnWidth + 2))) ∧
    (∀ row other, ((hermiteColumnPrefix source column count matrix left).2 row other).natAbs <
      2 ^ (basisWidth + count * (2 * columnWidth + 2))) := by
  obtain ⟨first, second⟩ := hermiteColumnSweep_bound columnWidth matrixWidth basisWidth source column
    (hermiteColumnTargets source count) (hermiteColumnTargets_distinct source count)
    (hermiteColumnTargets_excluded source count) matrix left positive columnBound matrixBound basisBound
  have budget := Nat.mul_le_mul_right (2 * columnWidth + 2) (hermiteColumnTargets_length source count)
  exact ⟨fun row other => (first row other).trans_le
      (pow_le_pow_right₀ (by decide) (Nat.add_le_add_left budget matrixWidth)),
    fun row other => (second row other).trans_le
      (pow_le_pow_right₀ (by decide) (Nat.add_le_add_left budget basisWidth))⟩

/-- The row traversal reuses the column traversal and transposes the right basis. -/
def hermiteRowPrefix {Row : Type} [DecidableEq Row] {columns : ℕ} (source : Fin columns) (row : Row) (count : ℕ)
    (matrix : Matrix Row (Fin columns) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ) :
    Matrix Row (Fin columns) ℤ × Matrix (Fin columns) (Fin columns) ℤ :=
  let result := hermiteColumnPrefix source row count matrix.transpose right.transpose
  (result.1.transpose, result.2.transpose)

end Polytime2.IntegerMatrix
