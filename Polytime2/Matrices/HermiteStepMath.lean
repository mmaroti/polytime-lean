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

import Polytime2.Arithmetic.GcdProgressMath
import Polytime2.Matrices.EuclideanMath
import Polytime2.Matrices.BezoutTrackingMath

/-! # A progress-sensitive Hermite row step

For distinct source and target rows and a positive source pivot, clear the target
entry and update the left basis. A divisible entry uses quotient cancellation,
leaving the entire source row fixed. Otherwise use normalized Bézout elimination;
the new positive pivot is the gcd and is at most half the previous pivot.
Neither invertibility nor full rank of the rectangular input is assumed.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- Keep divisible pivots fixed and use Bézout only for genuine gcd changes. -/
def hermiteRowStep (source target : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  if matrix source column ∣ matrix target column then rowRemainderWithLeft source target column matrix left
  else bezoutRowsWithLeft source target column matrix left

/-- The selected target vanishes and the pivot is the gcd in either branch. -/
theorem hermiteRowStep_entries (source target : Row) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column) :
    (hermiteRowStep source target column matrix left).1 source column = Int.gcd (matrix source column) (matrix target column) ∧
      (hermiteRowStep source target column matrix left).1 target column = 0 := by
  unfold hermiteRowStep
  split_ifs with divides
  · exact ⟨(rowRemainder_source source target different column matrix column).trans
        (Int.gcd_eq_left (le_of_lt positive) divides).symm,
      rowRemainder_divisible source target column matrix divides⟩
  · exact bezoutRowsWithLeft_eliminates source target different column matrix left

/-- A nondivisible target forces a genuine factor-two positive-pivot decrease. -/
theorem hermiteRowStep_progress (source target : Row) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (positive : 0 < matrix source column)
    (notDivides : ¬matrix source column ∣ matrix target column) :
    0 < (hermiteRowStep source target column matrix left).1 source column ∧
      2 * (hermiteRowStep source target column matrix left).1 source column ≤ matrix source column := by
  rw [(hermiteRowStep_entries source target different column matrix left positive).1]
  exact ⟨by exact_mod_cast Int.gcd_pos_of_ne_zero_left (matrix target column) (ne_of_gt positive),
    ExtendedGcd.int_gcd_halves_of_not_dvd _ _ positive notDivides⟩

/-- Divisible elimination preserves every entry of the source row. -/
theorem hermiteRowStep_source_of_dvd (source target : Row) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (divides : matrix source column ∣ matrix target column) (other : Column) :
    (hermiteRowStep source target column matrix left).1 source other = matrix source other := by
  simp only [hermiteRowStep, ite_eq_left divides, rowRemainderWithLeft]
  exact rowRemainder_source source target different column matrix other

/-- Both alternatives preserve the actual basis equation and unimodularity. -/
theorem hermiteRowStep_preserves [Fintype Row] [Fintype Column]
    (source target : Row) (different : source ≠ target) (column : Column)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteRowStep source target column matrix left).2 * original * right =
      (hermiteRowStep source target column matrix left).1 ∧
      IsUnit (hermiteRowStep source target column matrix left).2.det := by
  unfold hermiteRowStep
  split_ifs
  · exact ⟨rowRemainderWithLeft_equation source target column matrix original left right equation,
      rowRemainderWithLeft_unimodular source target different column matrix left unit⟩
  · exact ⟨bezoutRowsWithLeft_equation source target column original matrix left right equation,
      bezoutRowsWithLeft_unimodular source target different column matrix left unit⟩

/-- A zero selected target needs no operation on either matrix. -/
theorem hermiteRowStep_zero_target (source target : Row) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (zero : matrix target column = 0) :
    hermiteRowStep source target column matrix left = (matrix, left) := by
  simp [hermiteRowStep, zero, rowRemainderWithLeft, rowRemainder, rowAdd]

/-- Rows outside the selected pair are unchanged in both accumulated matrices. -/
theorem hermiteRowStep_rows_other (source target row : Row) (notSource : row ≠ source) (notTarget : row ≠ target)
    (column : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteRowStep source target column matrix left).1 row = matrix row ∧
      (hermiteRowStep source target column matrix left).2 row = left row := by
  unfold hermiteRowStep
  split_ifs <;> constructor <;> funext other <;>
    simp [rowRemainderWithLeft, rowRemainder, rowAdd, bezoutRowsWithLeft,
      rowPair, Matrix.updateRow_ne notSource, Matrix.updateRow_ne notTarget]

/-- A row outside the selected pair is untouched. -/
theorem hermiteRowStep_other (source target row : Row) (notSource : row ≠ source) (notTarget : row ≠ target)
    (column other : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteRowStep source target column matrix left).1 row other = matrix row other :=
  congrFun (hermiteRowStep_rows_other source target row notSource notTarget column matrix left).1 other

/-- Earlier zero entries in both selected rows leave their whole column unchanged. -/
theorem hermiteRowStep_zero_column (source target : Row) (column other : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceZero : matrix source other = 0) (targetZero : matrix target other = 0) (row : Row) :
    (hermiteRowStep source target column matrix left).1 row other = matrix row other := by
  unfold hermiteRowStep
  split_ifs
  · exact rowRemainder_zero_column source target column other matrix sourceZero row
  · exact rowPair_zero_column source target _ matrix other sourceZero targetZero row

/-- Zero entries in the selected basis rows keep the whole basis column fixed. -/
theorem hermiteRowStep_left_zero_column (source target : Row) (column : Column) (other : Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceZero : left source other = 0) (targetZero : left target other = 0) (row : Row) :
    (hermiteRowStep source target column matrix left).2 row other = left row other := by
  unfold hermiteRowStep
  split_ifs
  · exact rowAdd_zero_column target source _ left other sourceZero row
  · exact rowPair_zero_column source target _ left other sourceZero targetZero row

/-- Clear all listed entries of a column, keeping the accumulated left basis. -/
def hermiteColumnSweep (source : Row) (column : Column) (targets : List Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  targets.foldr (fun target state => hermiteRowStep source target column state.1 state.2) (matrix, left)

/-- A complete column sweep has a positive pivot and zero entries at every target. -/
theorem hermiteColumnSweep_entries (source : Row) (column : Column) (targets : List Row)
    (excluded : source ∉ targets) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    0 < (hermiteColumnSweep source column targets matrix left).1 source column ∧
      ∀ row ∈ targets, (hermiteColumnSweep source column targets matrix left).1 row column = 0 := by
  induction targets with
  | nil => exact ⟨positive, by simp⟩
  | cons target targets induction =>
    have different : source ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    obtain ⟨tailPositive, tailZeros⟩ := induction tailExcluded
    have entries := hermiteRowStep_entries source target different column
      (hermiteColumnSweep source column targets matrix left).1
      (hermiteColumnSweep source column targets matrix left).2 tailPositive
    constructor
    · change 0 < (hermiteRowStep source target column
        (hermiteColumnSweep source column targets matrix left).1
        (hermiteColumnSweep source column targets matrix left).2).1 source column
      rw [entries.1]
      exact_mod_cast Int.gcd_pos_of_ne_zero_left _ (ne_of_gt tailPositive)
    · intro row selected
      change (hermiteRowStep source target column
        (hermiteColumnSweep source column targets matrix left).1
        (hermiteColumnSweep source column targets matrix left).2).1 row column = 0
      by_cases same : row = target
      · subst row
        exact entries.2
      · have inTail : row ∈ targets := (List.mem_cons.mp selected).resolve_left same
        have notSource : row ≠ source := fun equality => tailExcluded (equality ▸ inTail)
        rw [hermiteRowStep_other source target row notSource same]
        exact tailZeros row inTail

/-- The column sweep retains the transformation equation for arbitrary rectangular inputs. -/
theorem hermiteColumnSweep_preserves [Fintype Row] [Fintype Column]
    (source : Row) (column : Column) (targets : List Row) (excluded : source ∉ targets)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteColumnSweep source column targets matrix left).2 * original * right =
      (hermiteColumnSweep source column targets matrix left).1 ∧
      IsUnit (hermiteColumnSweep source column targets matrix left).2.det := by
  induction targets with
  | nil => exact ⟨equation, unit⟩
  | cons target targets induction =>
    have different : source ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    obtain ⟨tailEquation, tailUnit⟩ := induction tailExcluded
    exact hermiteRowStep_preserves source target different column _ original _ right tailEquation tailUnit

/-- Count only steps which change the pivot; quotient cancellations do not count. -/
def hermiteColumnPivotChanges (source : Row) (column : Column) (targets : List Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : ℕ :=
  match targets with
  | [] => 0
  | target :: targets =>
    let state := hermiteColumnSweep source column targets matrix left
    hermiteColumnPivotChanges source column targets matrix left +
      if state.1 source column ∣ state.1 target column then 0 else 1

/-- Actual pivot changes in the column sweep telescope multiplicatively. -/
theorem hermiteColumnPivotChanges_product (source : Row) (column : Column) (targets : List Row)
    (excluded : source ∉ targets) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) :
    (2 : ℤ) ^ hermiteColumnPivotChanges source column targets matrix left *
      (hermiteColumnSweep source column targets matrix left).1 source column ≤ matrix source column := by
  induction targets with
  | nil => simp [hermiteColumnPivotChanges, hermiteColumnSweep]
  | cons target targets induction =>
    have different : source ≠ target := fun same => excluded (List.mem_cons.mpr (Or.inl same))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    have prefixBound := induction tailExcluded
    have tailPositive := (hermiteColumnSweep_entries source column targets tailExcluded matrix left positive).1
    change (2 : ℤ) ^ (_ + if _ then 0 else 1) *
      (hermiteRowStep source target column
        (hermiteColumnSweep source column targets matrix left).1
        (hermiteColumnSweep source column targets matrix left).2).1 source column ≤ _
    split_ifs with divides
    · simp only [add_zero]
      rw [hermiteRowStep_source_of_dvd source target different _ _ _ divides]
      exact prefixBound
    · have decreased := (hermiteRowStep_progress source target different column
        (hermiteColumnSweep source column targets matrix left).1
        (hermiteColumnSweep source column targets matrix left).2 tailPositive divides).2
      have scaled := mul_le_mul_of_nonneg_left decreased
        (by positivity : (0 : ℤ) ≤ 2 ^ hermiteColumnPivotChanges source column targets matrix left)
      calc
        _ = (2 : ℤ) ^ hermiteColumnPivotChanges source column targets matrix left *
            (2 * (hermiteRowStep source target column
              (hermiteColumnSweep source column targets matrix left).1
              (hermiteColumnSweep source column targets matrix left).2).1 source column) := by ring
        _ ≤ (2 : ℤ) ^ hermiteColumnPivotChanges source column targets matrix left *
            (hermiteColumnSweep source column targets matrix left).1 source column := scaled
        _ ≤ matrix source column := prefixBound

/-- The actual number of genuine gcd updates is bounded by the initial pivot width. -/
theorem hermiteColumnPivotChanges_lt_width (width : ℕ) (source : Row) (column : Column) (targets : List Row)
    (excluded : source ∉ targets) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : 0 < matrix source column) (bound : (matrix source column).natAbs < 2 ^ width) :
    hermiteColumnPivotChanges source column targets matrix left < width := by
  have sweepPositive := (hermiteColumnSweep_entries source column targets excluded matrix left positive).1
  have powered : (2 : ℤ) ^ hermiteColumnPivotChanges source column targets matrix left < 2 ^ width := calc
    _ ≤ (2 : ℤ) ^ hermiteColumnPivotChanges source column targets matrix left *
        (hermiteColumnSweep source column targets matrix left).1 source column := by
      nlinarith [pow_pos (by decide : (0 : ℤ) < 2)
        (hermiteColumnPivotChanges source column targets matrix left)]
    _ ≤ matrix source column := hermiteColumnPivotChanges_product source column targets excluded matrix left positive
    _ < 2 ^ width := by
      have castBound : ((matrix source column).natAbs : ℤ) < 2 ^ width := by exact_mod_cast bound
      simpa only [Int.natAbs_of_nonneg (le_of_lt positive)] using castBound
  exact (pow_lt_pow_iff_right₀ (by decide : (1 : ℤ) < 2)).mp powered

end Polytime2.IntegerMatrix
