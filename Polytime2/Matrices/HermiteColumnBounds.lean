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

import Polytime2.Matrices.HermiteStepMath

/-! # Polynomial widths for a changing-pivot column sweep

A sweep starts with a positive pivot and distinct target rows excluding its
source. The chosen column has magnitude width `w`, while all matrix and basis
entries have independent widths. Each step adds at most `2*w+2` bits: the pivot
never increases, and an unprocessed target row still has its original entries.
Thus every suffix sweep has polynomial matrix and basis widths. This is a bound
for one column; it does not establish global bounds across Hermite columns.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- A row outside the entire sweep is unchanged. -/
theorem hermiteColumnSweep_other (source row : Row) (notSource : row ≠ source) (column other : Column)
    (targets : List Row) (excluded : row ∉ targets) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteColumnSweep source column targets matrix left).1 row other = matrix row other := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
    have notTarget : row ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have notTail : row ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    change (hermiteRowStep source target column
      (hermiteColumnSweep source column targets matrix left).1
      (hermiteColumnSweep source column targets matrix left).2).1 row other = _
    rw [hermiteRowStep_other source target row notSource notTarget]
    exact induction notTail

/-- A positive sweep pivot never exceeds its initial value. -/
theorem hermiteColumnSweep_pivot_le (source : Row) (column : Column) (targets : List Row)
    (excluded : source ∉ targets) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    ((hermiteColumnSweep source column targets matrix left).1 source column).natAbs ≤
      (matrix source column).natAbs := by
  have resultPositive := (hermiteColumnSweep_entries source column targets excluded matrix left positive).1
  have product := hermiteColumnPivotChanges_product source column targets excluded matrix left positive
  have powerPositive : (0 : ℤ) < 2 ^ hermiteColumnPivotChanges source column targets matrix left := by positivity
  have resultLe : (hermiteColumnSweep source column targets matrix left).1 source column ≤ matrix source column := by
    nlinarith
  have castLe :
      (((hermiteColumnSweep source column targets matrix left).1 source column).natAbs : ℤ) ≤
      ((matrix source column).natAbs : ℤ) := by
    simpa only [Int.natAbs_of_nonneg (le_of_lt positive), Int.natAbs_of_nonneg (le_of_lt resultPositive)] using resultLe
  exact_mod_cast castLe

omit [DecidableEq Column] in
/-- Small pivot-column entries bound coefficients independently of other entries. -/
theorem hermiteRowStep_bound (columnWidth matrixWidth basisWidth : ℕ)
    (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (pivotBound : (matrix source column).natAbs < 2 ^ columnWidth)
    (targetBound : (matrix target column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteRowStep source target column matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + (2 * columnWidth + 2))) ∧
    (∀ row other, ((hermiteRowStep source target column matrix left).2 row other).natAbs <
      2 ^ (basisWidth + (2 * columnWidth + 2))) := by
  have quotientBound : (-(matrix target column / matrix source column)).natAbs < 2 ^ columnWidth := by
    rw [Int.natAbs_neg]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt targetBound
  have coefficients := bezoutMatrix_bound columnWidth _ _ pivotBound targetBound
  unfold hermiteRowStep
  split_ifs
  · constructor
    · intro row other
      exact (rowAdd_bound_of_widths columnWidth matrixWidth target source _ matrix quotientBound matrixBound row other).trans_le
        (pow_le_pow_right₀ (by decide) (by omega))
    · intro row other
      exact (rowAdd_bound_of_widths columnWidth basisWidth target source _ left quotientBound basisBound row other).trans_le
        (pow_le_pow_right₀ (by decide) (by omega))
  · constructor
    · intro row other
      exact (rowPair_bound_of_widths (2 * columnWidth + 1) matrixWidth source target _ matrix coefficients matrixBound row other).trans_le
        (pow_le_pow_right₀ (by decide) (by omega))
    · intro row other
      exact (rowPair_bound_of_widths (2 * columnWidth + 1) basisWidth source target _ left coefficients basisBound row other).trans_le
        (pow_le_pow_right₀ (by decide) (by omega))

/-- The updated source width depends only on the selected pair, not on other rows. -/
theorem hermiteRowStep_source_bound (columnWidth pairWidth : ℕ)
    (source target : Row) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (pivotBound : (matrix source column).natAbs < 2 ^ columnWidth)
    (targetBound : (matrix target column).natAbs < 2 ^ columnWidth)
    (sourceBound : ∀ other, (matrix source other).natAbs < 2 ^ pairWidth)
    (incomingBound : ∀ other, (matrix target other).natAbs < 2 ^ pairWidth) :
    ∀ other, ((hermiteRowStep source target column matrix left).1 source other).natAbs <
      2 ^ (pairWidth + (2 * columnWidth + 2)) := by
  intro other
  by_cases divides : matrix source column ∣ matrix target column
  · rw [hermiteRowStep_source_of_dvd source target different column matrix left divides]
    exact (sourceBound other).trans_le (pow_le_pow_right₀ (by decide) (by omega))
  · have coefficients := bezoutMatrix_bound columnWidth _ _ pivotBound targetBound
    have bound := IntegerArithmetic.twoProducts_bound_of_widths (2 * columnWidth + 1) pairWidth
      _ _ _ _ (coefficients 0 0) (sourceBound other) (coefficients 0 1) (incomingBound other)
    have result : ((hermiteRowStep source target column matrix left).1 source other).natAbs <
        2 ^ ((2 * columnWidth + 1) + pairWidth + 1) := by
      simpa only [hermiteRowStep, ite_eq_right divides, bezoutRowsWithLeft, rowPair,
        Matrix.updateRow_ne different, Matrix.updateRow_self] using bound
    exact result.trans_le (pow_le_pow_right₀ (by decide) (by omega))

/-- Every suffix sweep fits polynomial widths derived from the original column. -/
theorem hermiteColumnSweep_bound (columnWidth matrixWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row) (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteColumnSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + targets.length * (2 * columnWidth + 2))) ∧
    (∀ row other, ((hermiteColumnSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (basisWidth + targets.length * (2 * columnWidth + 2))) := by
  induction targets with
  | nil => simpa only [hermiteColumnSweep, List.foldr_nil, List.length_nil, zero_mul, add_zero] using And.intro matrixBound basisBound
  | cons target targets induction =>
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have targetExcluded := (List.nodup_cons.mp distinct).1
    have different : source ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    obtain ⟨tailMatrixBound, tailBasisBound⟩ := induction tailDistinct tailExcluded
    have pivotBound := (hermiteColumnSweep_pivot_le source column targets tailExcluded matrix left positive).trans_lt
      (columnBound source)
    have targetBound : ((hermiteColumnSweep source column targets matrix left).1 target column).natAbs < 2 ^ columnWidth := by
      rw [hermiteColumnSweep_other source target different.symm column column targets targetExcluded matrix left]
      exact columnBound target
    have stepBound := hermiteRowStep_bound columnWidth
      (matrixWidth + targets.length * (2 * columnWidth + 2))
      (basisWidth + targets.length * (2 * columnWidth + 2)) source target column
      (hermiteColumnSweep source column targets matrix left).1
      (hermiteColumnSweep source column targets matrix left).2 pivotBound targetBound tailMatrixBound tailBasisBound
    simpa only [hermiteColumnSweep, List.foldr_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using stepBound

/-- A dimension-based workspace covers every distinct-target column sweep. -/
theorem hermiteColumnSweep_bound_of_card [Fintype Row] (columnWidth matrixWidth basisWidth : ℕ)
    (source : Row) (column : Column) (targets : List Row) (distinct : targets.Nodup) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (columnBound : ∀ row, (matrix row column).natAbs < 2 ^ columnWidth)
    (matrixBound : ∀ row other, (matrix row other).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row other, (left row other).natAbs < 2 ^ basisWidth) :
    (∀ row other, ((hermiteColumnSweep source column targets matrix left).1 row other).natAbs <
      2 ^ (matrixWidth + Fintype.card Row * (2 * columnWidth + 2))) ∧
    (∀ row other, ((hermiteColumnSweep source column targets matrix left).2 row other).natAbs <
      2 ^ (basisWidth + Fintype.card Row * (2 * columnWidth + 2))) := by
  obtain ⟨matrixResult, basisResult⟩ := hermiteColumnSweep_bound columnWidth matrixWidth basisWidth
    source column targets distinct excluded matrix left positive columnBound matrixBound basisBound
  have budget := Nat.mul_le_mul_right (2 * columnWidth + 2) distinct.length_le_card
  exact ⟨fun row other => (matrixResult row other).trans_le
      (pow_le_pow_right₀ (by decide) (Nat.add_le_add_left budget matrixWidth)),
    fun row other => (basisResult row other).trans_le
      (pow_le_pow_right₀ (by decide) (Nat.add_le_add_left budget basisWidth))⟩

end Polytime2.IntegerMatrix
