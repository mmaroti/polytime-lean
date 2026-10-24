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

import Polytime2.Matrices.EuclideanMath

/-! # A fixed-pivot Euclidean sweep

Given a positive pivot and a list of distinct target rows excluding its source,
reduce each target entry modulo the pivot and apply the same operations to the
left basis. The closed formula uses only original rows. Consequently one sweep
has a single derived width bound, independent of the number of target rows.
This does not bound successive sweeps with changing pivots.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row]

/-- Reduce each listed target against one fixed source, retaining the left basis. -/
def rowRemainderSweep (source : Row) (column : Column) (targets : List Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    Matrix Row Column ℤ × Matrix Row Row ℤ :=
  targets.foldr (fun target state => rowRemainderWithLeft source target column state.1 state.2) (matrix, left)

/-- No target depends on another target: every coefficient uses the original matrix. -/
theorem rowRemainderSweep_apply (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (∀ row other, (rowRemainderSweep source column targets matrix left).1 row other =
      if row ∈ targets then matrix row other - (matrix row column / matrix source column) * matrix source other
      else matrix row other) ∧
    (∀ row other, (rowRemainderSweep source column targets matrix left).2 row other =
      if row ∈ targets then left row other - (matrix row column / matrix source column) * left source other
      else left row other) := by
  induction targets with
  | nil => simp [rowRemainderSweep]
  | cons target targets induction =>
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have targetExcluded := (List.nodup_cons.mp distinct).1
    have sourceExcluded : source ∉ targets := by
      exact fun member => excluded (List.mem_cons_of_mem target member)
    obtain ⟨matrixFormula, leftFormula⟩ := induction tailDistinct sourceExcluded
    have matrixTarget := fun other => matrixFormula target other
    have matrixSource := fun other => matrixFormula source other
    have leftTarget := fun other => leftFormula target other
    have leftSource := fun other => leftFormula source other
    simp only [ite_eq_right targetExcluded] at matrixTarget leftTarget
    simp only [ite_eq_right sourceExcluded] at matrixSource leftSource
    constructor
    · intro row other
      change rowRemainder source target column
        (rowRemainderSweep source column targets matrix left).1 row other = _
      by_cases same : row = target
      · subst row
        simp only [rowRemainder, rowAdd, Matrix.updateRow_self, matrixTarget, matrixSource,
          List.mem_cons, true_or, ite_true, sub_eq_add_neg, neg_mul]
      · simp only [rowRemainder, rowAdd, Matrix.updateRow_ne same]
        simpa only [List.mem_cons, same, false_or] using matrixFormula row other
    · intro row other
      change rowAdd target source
        (-((rowRemainderSweep source column targets matrix left).1 target column /
          (rowRemainderSweep source column targets matrix left).1 source column))
        (rowRemainderSweep source column targets matrix left).2 row other = _
      by_cases same : row = target
      · subst row
        simp only [rowAdd, Matrix.updateRow_self, matrixTarget, matrixSource, leftTarget, leftSource,
          List.mem_cons, true_or, ite_true, sub_eq_add_neg, neg_mul]
      · simp only [rowAdd, Matrix.updateRow_ne same]
        simpa only [List.mem_cons, same, false_or] using leftFormula row other

/-- Every selected entry becomes its original remainder. -/
theorem rowRemainderSweep_entry (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (row : Row) (selected : row ∈ targets) :
    (rowRemainderSweep source column targets matrix left).1 row column =
      matrix row column % matrix source column := by
  classical
  rw [(rowRemainderSweep_apply source column targets distinct excluded matrix left).1 row column,
    ite_eq_left selected]
  simpa only [rowRemainder, rowAdd, Matrix.updateRow_self, sub_eq_add_neg, neg_mul] using
    rowRemainder_entry source row column matrix

/-- Earlier zero columns of the source remain unchanged throughout the sweep. -/
theorem rowRemainderSweep_zero_column (source : Row) (column other : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : matrix source other = 0) (row : Row) :
    (rowRemainderSweep source column targets matrix left).1 row other = matrix row other := by
  rw [(rowRemainderSweep_apply source column targets distinct excluded matrix left).1 row other]
  simp [zero]

/-- A zero source basis entry keeps that entire basis column fixed. -/
theorem rowRemainderSweep_left_zero_column (source : Row) (column : Column) (other : Row)
    (targets : List Row) (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : left source other = 0) (row : Row) :
    (rowRemainderSweep source column targets matrix left).2 row other = left row other := by
  rw [(rowRemainderSweep_apply source column targets distinct excluded matrix left).2]
  simp only [zero, mul_zero, sub_zero, ite_self]

/-- The selected column is reduced modulo the unchanged positive pivot. -/
theorem rowRemainderSweep_range (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) (row : Row) (selected : row ∈ targets) :
    0 ≤ (rowRemainderSweep source column targets matrix left).1 row column ∧
      (rowRemainderSweep source column targets matrix left).1 row column < matrix source column := by
  rw [rowRemainderSweep_entry source column targets distinct excluded matrix left row selected]
  exact ⟨Int.emod_nonneg _ (ne_of_gt positive), Int.emod_lt_of_pos _ positive⟩

/-- The complete sweep preserves the accumulated presentation and unimodularity. -/
theorem rowRemainderSweep_preserves [Fintype Row] [Fintype Column]
    (source : Row) (column : Column) (targets : List Row) (excluded : source ∉ targets)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (rowRemainderSweep source column targets matrix left).2 * original * right =
      (rowRemainderSweep source column targets matrix left).1 ∧
      IsUnit (rowRemainderSweep source column targets matrix left).2.det := by
  classical
  induction targets with
  | nil => exact ⟨equation, unit⟩
  | cons target targets induction =>
    have different : source ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    obtain ⟨tailEquation, tailUnit⟩ := induction tailExcluded
    exact ⟨rowRemainderWithLeft_equation source target column _ original _ right tailEquation,
      rowRemainderWithLeft_unimodular source target different column _ _ tailUnit⟩

/-- Separate source and target widths control normalization without widening all rows alike. -/
theorem rowRemainderSweep_bound_of_source_column (columnWidth matrixWidth sourceWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (sourceBound : ∀ other, (matrix source other).natAbs < 2 ^ sourceWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((rowRemainderSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (max matrixWidth (columnWidth + sourceWidth) + 1)) ∧
    (∀ row other, ((rowRemainderSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (columnWidth + basisWidth + 1)) := by
  have quotientBound (row : Row) : (-(matrix row column / matrix source column)).natAbs < 2 ^ columnWidth := by
    rw [Int.natAbs_neg]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (columnBound row)
  obtain ⟨matrixFormula, basisFormula⟩ := rowRemainderSweep_apply source column targets distinct excluded matrix left
  constructor
  · intro row other
    rw [matrixFormula]
    split_ifs
    · simpa only [sub_eq_add_neg, neg_mul] using IntegerArithmetic.multiplyAdd_bound_of_three_widths matrixWidth columnWidth sourceWidth
        _ _ _ (matrixBound row other) (quotientBound row) (sourceBound other)
    · exact (matrixBound row other).trans_le (pow_le_pow_right₀ (by decide) (by omega))
  · intro row other
    rw [basisFormula]
    split_ifs
    · simpa only [sub_eq_add_neg, neg_mul] using IntegerArithmetic.multiplyAdd_bound_of_widths columnWidth basisWidth
        _ _ _ (basisBound row other) (quotientBound row) (basisBound source other)
    · exact (basisBound row other).trans_le (pow_le_pow_right₀ (by decide) (by omega))

/-- Quotient widths depend only on the selected column, independently of other entries. -/
theorem rowRemainderSweep_bound_of_column (columnWidth matrixWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((rowRemainderSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (columnWidth + matrixWidth + 1)) ∧
    (∀ row other, ((rowRemainderSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (columnWidth + basisWidth + 1)) := by
  simpa only [max_eq_right (Nat.le_add_left matrixWidth columnWidth)] using
    rowRemainderSweep_bound_of_source_column columnWidth matrixWidth matrixWidth basisWidth
      source column targets distinct excluded matrix left columnBound matrixBound
      (matrixBound source) basisBound

/-- A small source row makes width growth additive in its width, even for large quotients. -/
theorem rowRemainderSweep_bound_of_source (matrixWidth sourceWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (sourceBound : ∀ other, (matrix source other).natAbs < 2 ^ sourceWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((rowRemainderSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + sourceWidth + 1)) ∧
    (∀ row other, ((rowRemainderSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (matrixWidth + basisWidth + 1)) := by
  simpa only [max_eq_right (Nat.le_add_right matrixWidth sourceWidth)] using
    rowRemainderSweep_bound_of_source_column matrixWidth matrixWidth sourceWidth basisWidth
      source column targets distinct excluded matrix left (fun row => matrixBound row column)
      matrixBound sourceBound basisBound

/-- The common-column-width specialization reuses the heterogeneous sweep bound. -/
theorem rowRemainderSweep_bound (matrixWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row)
    (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((rowRemainderSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (2 * matrixWidth + 1)) ∧
    (∀ row other, ((rowRemainderSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (matrixWidth + basisWidth + 1)) := by
  simpa only [two_mul] using rowRemainderSweep_bound_of_column matrixWidth matrixWidth basisWidth
    source column targets distinct excluded matrix left (fun row => matrixBound row column) matrixBound basisBound

/-- Distinct nonsource targets can be permuted without changing either returned matrix. -/
theorem rowRemainderSweep_perm (source : Row) (column : Column) (targets reordered : List Row)
    (permutation : targets.Perm reordered) (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    rowRemainderSweep source column targets matrix left = rowRemainderSweep source column reordered matrix left := by
  have reorderedDistinct := permutation.nodup_iff.mp distinct
  have reorderedExcluded : source ∉ reordered := fun member => excluded (permutation.mem_iff.mpr member)
  have first := rowRemainderSweep_apply source column targets distinct excluded matrix left
  have second := rowRemainderSweep_apply source column reordered reorderedDistinct reorderedExcluded matrix left
  apply Prod.ext
  · ext row other
    simp only [first.1 row other, second.1 row other, permutation.mem_iff]
  · ext row other
    simp only [first.2 row other, second.2 row other, permutation.mem_iff]

/-- A fresh final target can be reduced after the preceding sweep. -/
theorem rowRemainderSweep_append_singleton (source target : Row) (column : Column) (targets : List Row)
    (distinct : (targets ++ [target]).Nodup) (excluded : source ∉ targets ++ [target])
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    rowRemainderSweep source column (targets ++ [target]) matrix left =
      rowRemainderWithLeft source target column (rowRemainderSweep source column targets matrix left).1
        (rowRemainderSweep source column targets matrix left).2 := by
  have permutation : (targets ++ [target]).Perm (target :: targets) := by
    simp
  exact rowRemainderSweep_perm source column _ _ permutation distinct excluded matrix left

/-- Increasing array prefixes agree with the order-independent mathematical sweep. -/
theorem rowRemainderSweep_prefix_succ {length : ℕ} (source : Row) (column : Column)
    (targets : Fin length → Row) (distinct : (List.ofFn targets).Nodup) (excluded : source ∉ List.ofFn targets)
    (index : Fin length) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    rowRemainderSweep source column ((List.ofFn targets).take (index.val + 1)) matrix left =
      rowRemainderWithLeft source (targets index) column
        (rowRemainderSweep source column ((List.ofFn targets).take index.val) matrix left).1
        (rowRemainderSweep source column ((List.ofFn targets).take index.val) matrix left).2 := by
  have next := List.take_succ_eq_append_getElem (l := List.ofFn targets) (i := index.val) (by simp)
  simp only [List.getElem_ofFn] at next
  have prefixDistinct : ((List.ofFn targets).take (index.val + 1)).Nodup := distinct.take
  have prefixExcluded : source ∉ (List.ofFn targets).take (index.val + 1) :=
    fun member => excluded (List.mem_of_mem_take member)
  rw [next] at prefixDistinct prefixExcluded ⊢
  exact rowRemainderSweep_append_singleton source (targets index) column _ prefixDistinct prefixExcluded matrix left

end Polytime2.IntegerMatrix
