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

import Polytime2.Matrices.HermiteStageMath
import Polytime2.Matrices.DiagonalProgressMath

/-! # Diagonal-factor transfer in an interleaved Hermite stage

On a square active block, use an earlier source against a later incoming row.
The source has zero in the incoming diagonal column, and both selected rows
vanish in the diagonal columns normalized above the pivot. The stage preserves
the selected diagonal product and every other diagonal entry. A nondivisible
pivot update therefore decreases the shared weighted-diagonal bit measure.
This is a local stage result; the full-pass invariant and pass budget remain
separate obligations.
-/

namespace Polytime2.IntegerMatrix

variable {length : ℕ}

/-- With no source entry in the later diagonal column, elimination transfers only the pivot quotient. -/
theorem hermiteRowStep_target_diagonal (source target : Fin length)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : 0 < matrix source source) (futureZero : matrix source target = 0) :
    (hermiteRowStep source target source matrix left).1 target target =
      if matrix source source ∣ matrix target source then matrix target target
      else (matrix source source / (Int.gcd (matrix source source) (matrix target source) : ℤ)) * matrix target target := by
  have nonzero : Int.gcd (matrix source source) (matrix target source) ≠ 0 :=
    ne_of_gt (Int.gcd_pos_of_ne_zero_left _ (ne_of_gt positive))
  unfold hermiteRowStep
  split_ifs
  · simp [rowRemainderWithLeft, rowRemainder, rowAdd, futureZero]
  · simp [bezoutRowsWithLeft, rowPair, bezoutMatrix, nonzero, futureZero]

/-- A local elimination preserves the product of the earlier and incoming diagonal entries. -/
theorem hermiteRowStep_diagonal_product (source target : Fin length) (different : source ≠ target)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : 0 < matrix source source) (futureZero : matrix source target = 0) :
    (hermiteRowStep source target source matrix left).1 source source *
        (hermiteRowStep source target source matrix left).1 target target = matrix source source * matrix target target := by
  rw [(hermiteRowStep_entries source target different source matrix left positive).1,
    hermiteRowStep_target_diagonal source target matrix left positive futureZero]
  split_ifs with divides
  · rw [Int.gcd_eq_left (le_of_lt positive) divides]
  · calc
      _ = (matrix source source / (Int.gcd (matrix source source) (matrix target source) : ℤ) *
          (Int.gcd (matrix source source) (matrix target source) : ℤ)) * matrix target target := by ring
      _ = _ := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]

/-- Remainder normalization excludes both selected rows, so it retains their diagonal product. -/
theorem hermiteRowStage_diagonal_product (source target : Fin length) (different : source ≠ target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : 0 < matrix source source) (futureZero : matrix source target = 0) :
    (hermiteRowStage source target source earlierRows matrix left).1 source source *
        (hermiteRowStage source target source earlierRows matrix left).1 target target = matrix source source * matrix target target := by
  have formula := (rowRemainderSweep_apply source source earlierRows distinct sourceExcluded
    (hermiteRowStep source target source matrix left).1 (hermiteRowStep source target source matrix left).2).1
  change (rowRemainderSweep source source earlierRows _ _).1 source source *
    (rowRemainderSweep source source earlierRows _ _).1 target target = _
  rw [formula, formula, ite_eq_right sourceExcluded, ite_eq_right targetExcluded]
  exact hermiteRowStep_diagonal_product source target different matrix left positive futureZero

/-- Earlier zero columns prevent remainder normalization from changing any other diagonal entry. -/
theorem hermiteRowStage_diagonal_other (source target index : Fin length)
    (notSource : index ≠ source) (notTarget : index ≠ target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup) (excluded : source ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (earlierZero : ∀ row ∈ earlierRows, matrix source row = 0 ∧ matrix target row = 0) :
    (hermiteRowStage source target source earlierRows matrix left).1 index index = matrix index index := by
  by_cases earlier : index ∈ earlierRows
  · exact hermiteRowStage_zero_column source target source index earlierRows distinct excluded matrix left
      (earlierZero index earlier).1 (earlierZero index earlier).2 index
  · have formula := (rowRemainderSweep_apply source source earlierRows distinct excluded
      (hermiteRowStep source target source matrix left).1 (hermiteRowStep source target source matrix left).2).1 index index
    change (rowRemainderSweep source source earlierRows _ _).1 index index = _
    rw [formula, ite_eq_right earlier]
    exact hermiteRowStep_other source target index notSource notTarget source index matrix left

/-- A divisible cancellation leaves the full diagonal unchanged under the same zero conditions. -/
theorem hermiteRowStage_diagonal_of_dvd (source target : Fin length) (different : source ≠ target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : 0 < matrix source source) (futureZero : matrix source target = 0)
    (earlierZero : ∀ row ∈ earlierRows, matrix source row = 0 ∧ matrix target row = 0)
    (divides : matrix source source ∣ matrix target source) :
    ∀ index, (hermiteRowStage source target source earlierRows matrix left).1 index index = matrix index index := by
  intro index
  by_cases atSource : index = source
  · subst index
    rw [(hermiteRowStage_entries source target different source earlierRows distinct sourceExcluded targetExcluded
      matrix left positive).1, Int.gcd_eq_left (le_of_lt positive) divides]
  · by_cases atTarget : index = target
    · subst index
      have formula := (rowRemainderSweep_apply source source earlierRows distinct sourceExcluded
        (hermiteRowStep source target source matrix left).1 (hermiteRowStep source target source matrix left).2).1 target target
      change (rowRemainderSweep source source earlierRows _ _).1 target target = _
      rw [formula, ite_eq_right targetExcluded, hermiteRowStep_target_diagonal source target matrix left positive futureZero,
        ite_eq_left divides]
    · exact hermiteRowStage_diagonal_other source target index atSource atTarget earlierRows distinct sourceExcluded matrix left earlierZero

/-- The selected product and untouched other diagonals preserve positivity at every stage. -/
theorem hermiteRowStage_diagonal_positive (source target : Fin length) (different : source ≠ target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : ∀ index, 0 < matrix index index) (futureZero : matrix source target = 0)
    (earlierZero : ∀ row ∈ earlierRows, matrix source row = 0 ∧ matrix target row = 0) :
    ∀ index, 0 < (hermiteRowStage source target source earlierRows matrix left).1 index index := by
  let result := (hermiteRowStage source target source earlierRows matrix left).1
  have entries := hermiteRowStage_entries source target different source earlierRows distinct sourceExcluded targetExcluded
    matrix left (positive source)
  have sourceEntry : result source source = (Int.gcd (matrix source source) (matrix target source) : ℤ) := entries.1
  have product : result source source * result target target = matrix source source * matrix target target :=
    hermiteRowStage_diagonal_product source target different earlierRows distinct sourceExcluded targetExcluded
      matrix left (positive source) futureZero
  have sourcePositive : 0 < result source source := by
    rw [sourceEntry]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left _ (ne_of_gt (positive source))
  have targetPositive : 0 < result target target := by
    have originalProduct := mul_pos (positive source) (positive target)
    nlinarith
  intro index
  by_cases atSource : index = source
  · subst index; exact sourcePositive
  · by_cases atTarget : index = target
    · subst index; exact targetPositive
    · rw [hermiteRowStage_diagonal_other source target index atSource atTarget earlierRows distinct sourceExcluded matrix left earlierZero]
      exact positive index

/-- A genuine gcd update at any earlier/later pair decreases the shared diagonal bit measure. -/
theorem hermiteRowStage_potential_decreases (source target : Fin length) (ordered : source < target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : ∀ index, 0 < matrix index index) (futureZero : matrix source target = 0)
    (earlierZero : ∀ row ∈ earlierRows, matrix source row = 0 ∧ matrix target row = 0)
    (notDivides : ¬matrix source source ∣ matrix target source) :
    (diagonalPotential (fun index => ((hermiteRowStage source target source earlierRows matrix left).1 index index).natAbs)).size <
      (diagonalPotential (fun index => (matrix index index).natAbs)).size := by
  let result := (hermiteRowStage source target source earlierRows matrix left).1
  have different : source ≠ target := ne_of_lt ordered
  have entries := hermiteRowStage_entries source target different source earlierRows distinct sourceExcluded targetExcluded
    matrix left (positive source)
  have product := hermiteRowStage_diagonal_product source target different earlierRows distinct sourceExcluded targetExcluded
    matrix left (positive source) futureZero
  have sourceEntry : result source source = (Int.gcd (matrix source source) (matrix target source) : ℤ) := entries.1
  change result source source * result target target = matrix source source * matrix target target at product
  have unchanged (index : Fin length) (notSource : index ≠ source) (notTarget : index ≠ target) :
      result index index = matrix index index :=
    hermiteRowStage_diagonal_other source target index notSource notTarget earlierRows distinct sourceExcluded matrix left earlierZero
  have positiveNew := hermiteRowStage_diagonal_positive source target different earlierRows distinct sourceExcluded targetExcluded
    matrix left positive futureZero earlierZero
  have currentPositive : ∀ index, 0 < (result index index).natAbs :=
    fun index => Int.natAbs_pos.mpr (ne_of_gt (positiveNew index))
  apply diagonalPotential_size_decreases_of_pair (fun index => (matrix index index).natAbs)
    (fun index => (result index index).natAbs) currentPositive source target ordered
  · intro index notSource notTarget
    rw [unchanged index notSource notTarget]
  · simpa only [Int.natAbs_mul] using congrArg Int.natAbs product
  · rw [sourceEntry, Int.natAbs_natCast, Int.gcd_eq_natAbs]
    exact ExtendedGcd.gcd_halves_of_not_dvd _ _ (Int.natAbs_pos.mpr (ne_of_gt (positive source)))
      (by simpa only [Int.natAbs_dvd_natAbs] using notDivides)

/-- Every admissible stage is nonincreasing in the shared weighted-diagonal bit measure. -/
theorem hermiteRowStage_potential_mono (source target : Fin length) (ordered : source < target)
    (earlierRows : List (Fin length)) (distinct : earlierRows.Nodup)
    (sourceExcluded : source ∉ earlierRows) (targetExcluded : target ∉ earlierRows)
    (matrix left : Matrix (Fin length) (Fin length) ℤ)
    (positive : ∀ index, 0 < matrix index index) (futureZero : matrix source target = 0)
    (earlierZero : ∀ row ∈ earlierRows, matrix source row = 0 ∧ matrix target row = 0) :
    (diagonalPotential (fun index => ((hermiteRowStage source target source earlierRows matrix left).1 index index).natAbs)).size ≤
      (diagonalPotential (fun index => (matrix index index).natAbs)).size := by
  by_cases divides : matrix source source ∣ matrix target source
  · have diagonal := hermiteRowStage_diagonal_of_dvd source target (ne_of_lt ordered) earlierRows distinct sourceExcluded targetExcluded
      matrix left (positive source) futureZero earlierZero divides
    have same : (fun index => ((hermiteRowStage source target source earlierRows matrix left).1 index index).natAbs) =
        (fun index => (matrix index index).natAbs) := funext (fun index => congrArg Int.natAbs (diagonal index))
    rw [same]
  · exact (hermiteRowStage_potential_decreases source target ordered earlierRows distinct sourceExcluded targetExcluded
      matrix left positive futureZero earlierZero divides).le

end Polytime2.IntegerMatrix
