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

import Polytime2.Matrices.HermiteDiagonalMath
import Polytime2.Matrices.HermiteSweepMath

/-! # Triangular-input invariants for Hermite progress

Processed rows use only processed original input rows. For a lower triangular
input, their entries in future columns must therefore vanish. This supplies
the source-future zero condition of the weighted diagonal stage theorem.
-/

namespace Polytime2.IntegerMatrix

/-- Divisible elimination from an earlier row preserves lower triangularity. -/
theorem hermiteRowStep_lower_of_dvd {dimension : ℕ} (source target : Fin dimension)
    (ordered : source < target) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (divides : matrix source source ∣ matrix target source) :
    (hermiteRowStep source target source matrix left).1.IsLowerTriangular := by
  rw [hermiteRowStep, ite_eq_left divides]
  intro row column before
  change row.val < column.val at before
  change rowRemainder source target source matrix row column = 0
  by_cases same : row = target
  · subst row
    have sourceZero := lower (show source.val < column.val from lt_trans ordered before)
    rw [rowRemainder_zero_column source target source column matrix sourceZero]
    exact lower before
  · simp only [rowRemainder, rowAdd, Matrix.updateRow_ne same]
    exact lower before

/-- Earlier-row normalization is idle after divisible elimination of lower triangular input. -/
theorem hermiteRowStage_lower_of_dvd {dimension : ℕ} (source target : Fin dimension)
    (ordered : source < target) (earlierRows : List (Fin dimension)) (distinct : earlierRows.Nodup)
    (excluded : source ∉ earlierRows) (earlier : ∀ row ∈ earlierRows, row < source)
    (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (divides : matrix source source ∣ matrix target source) :
    (hermiteRowStage source target source earlierRows matrix left).1.IsLowerTriangular := by
  have eliminated := hermiteRowStep_lower_of_dvd source target ordered matrix left lower divides
  have formula := (rowRemainderSweep_apply source source earlierRows distinct excluded
    (hermiteRowStep source target source matrix left).1
    (hermiteRowStep source target source matrix left).2).1
  intro row column before
  change (rowRemainderSweep source source earlierRows
    (hermiteRowStep source target source matrix left).1
    (hermiteRowStep source target source matrix left).2).1 row column = 0
  rw [formula]
  split_ifs with member
  · rw [eliminated (earlier row member), Int.zero_ediv, zero_mul, sub_zero]
    exact eliminated before
  · exact eliminated before

/-- With a positive diagonal pivot and lower triangular input, rank extension is idle. -/
theorem hermiteExtendPivot_eq_of_positive_lower {dimension rank : ℕ}
    (activeRows : Fin rank ↪ Fin dimension) (source : Fin dimension)
    (earlier : ∀ index, activeRows index < source)
    (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : 0 < matrix source source) :
    hermiteExtendPivot activeRows source source matrix left = (matrix, left) := by
  have excluded : source ∉ (List.finRange rank).map activeRows := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact (ne_of_lt (earlier index)) same
  have formula := rowRemainderSweep_apply source source ((List.finRange rank).map activeRows)
    ((List.nodup_finRange rank).map activeRows.injective) excluded matrix left
  have zero : ∀ row ∈ (List.finRange rank).map activeRows, matrix row source = 0 := by
    intro row member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    rw [← same]
    exact lower (earlier index)
  simp only [hermiteExtendPivot, positivePivotWithLeft, ite_eq_right (not_lt.mpr positive.le)]
  apply Prod.ext
  · ext row column
    rw [formula.1]
    split_ifs with member
    · rw [zero row member, Int.zero_ediv, zero_mul, sub_zero]
    · rfl
  · ext row column
    rw [formula.2]
    split_ifs with member
    · rw [zero row member, Int.zero_ediv, zero_mul, sub_zero]
    · rfl

/-- A supported left transformation of lower triangular input cannot introduce future-column entries. -/
theorem lower_mul_upper_right_zero {dimension : ℕ} (processed : ℕ)
    (original current left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (equation : left * original = current) (lower : original.IsLowerTriangular)
    (support : ∀ row : Fin dimension, row.val < processed →
      ∀ column : Fin dimension, processed ≤ column.val → left row column = 0) :
    ∀ row column : Fin dimension, row.val < processed → processed ≤ column.val → current row column = 0 := by
  intro row column before after
  rw [← equation]
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro index _
  by_cases old : index.val < processed
  · rw [lower (show index.val < column.val from Nat.lt_of_lt_of_le old after), mul_zero]
  · rw [support row before index (by omega), zero_mul]

/-- Every outer prefix inherits future-column zeros from the original lower triangular input. -/
theorem HermiteRowPrefix.upper_right_zero {dimension processed : ℕ}
    {original : Matrix (Fin dimension) (Fin dimension) ℤ} {state : HermiteRowState dimension dimension}
    (invariant : HermiteRowPrefix original processed state) (lower : original.IsLowerTriangular) :
    ∀ row column : Fin dimension, row.val < processed → processed ≤ column.val → state.1.1 row column = 0 := by
  obtain ⟨equation, _, _, _, _, _, _, support, _⟩ := invariant
  exact lower_mul_upper_right_zero processed original state.1.1 state.1.2 equation lower support

/-- Including the next input row, the incoming rectangle has no entries in later columns. -/
theorem HermiteRowPrefix.incoming_rectangle_zero {dimension processed : ℕ}
    {original : Matrix (Fin dimension) (Fin dimension) ℤ} {state : HermiteRowState dimension dimension}
    (invariant : HermiteRowPrefix original processed state) (lower : original.IsLowerTriangular)
    (within : processed + 1 ≤ dimension) :
    ∀ row : Fin (processed + 1), ∀ column : Fin dimension, processed + 1 ≤ column.val →
      state.1.1 (Fin.castLE within row) column = 0 := by
  intro row column after
  by_cases before : row.val < processed
  · exact invariant.upper_right_zero lower _ column before (by omega)
  · rw [invariant.future_row (Fin.castLE within row) (by simpa using Nat.le_of_not_gt before)]
    exact lower (show (Fin.castLE within row).val < column.val from
      Nat.lt_of_lt_of_le row.isLt after)

/-- At a canonical incoming stage, unvisited source rows and cleared earlier entries supply the zero conditions. -/
theorem hermiteIncomingPrefix_canonical_conditions {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (index : Fin pivots) :
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let state := hermiteIncomingPrefix selected columns index.val matrix left
    state.1 (selected index.castSucc) (selected (Fin.last pivots)) = 0 ∧
      ∀ row ∈ (hermiteColumnTargets index.castSucc index.val).map selected,
        state.1 (selected index.castSucc) row = 0 ∧ state.1 (selected (Fin.last pivots)) row = 0 := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  let state := hermiteIncomingPrefix selected columns index.val matrix left
  have sourceSame := (hermiteIncomingPrefix_future_row selected columns index.val index (by rfl) matrix left).1
  have coordinates (old : Fin pivots) : selected old.castSucc = columns old := Fin.ext rfl
  have pivotPositive : ∀ old, 0 < matrix (selected old.castSucc) (columns old) := by
    intro old
    rw [← coordinates old]
    exact positive _
  have pivotUpper : ∀ row column : Fin pivots, column < row → matrix (selected row.castSucc) (columns column) = 0 := by
    intro row column below
    rw [coordinates row]
    exact upper row column below
  refine ⟨?_, ?_⟩
  · change state.1 (selected index.castSucc) (selected (Fin.last pivots)) = 0
    rw [sourceSame, coordinates index]
    exact futureZero index
  · intro row member
    obtain ⟨earlier, earlierMember, rowEq⟩ := List.mem_map.mp member
    subst row
    have before := (hermiteColumnTargets_mem _ _ _).mp earlierMember
    let old : Fin pivots := ⟨earlier.val, lt_trans before.1 index.isLt⟩
    have earlierEq : earlier = old.castSucc := Fin.ext rfl
    rw [earlierEq, coordinates old]
    constructor
    · rw [sourceSame, coordinates index]
      exact upper index old before.1
    · exact (hermiteIncomingPrefix_entries selected columns index.val (by omega) matrix left pivotPositive pivotUpper
        old before.1).2.1

/-- A canonical inner transition preserves positivity and transfers strict gcd progress. -/
theorem hermiteIncomingPrefix_canonical_transition {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (index : Fin pivots)
    (currentPositive : ∀ row, 0 < (hermiteIncomingPrefix (Fin.castLEEmb within)
      (Fin.castLE (by omega : pivots ≤ dimension)) index.val matrix left).1 row row) :
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let before := hermiteIncomingPrefix selected columns index.val matrix left
    let after := hermiteIncomingPrefix selected columns (index.val + 1) matrix left
    (∀ row, 0 < after.1 row row) ∧
      (diagonalPotential (fun row => (after.1 row row).natAbs)).size ≤
        (diagonalPotential (fun row => (before.1 row row).natAbs)).size ∧
      (¬ before.1 (selected index.castSucc) (columns index) ∣
        before.1 (selected (Fin.last pivots)) (columns index) →
        (diagonalPotential (fun row => (after.1 row row).natAbs)).size <
          (diagonalPotential (fun row => (before.1 row row).natAbs)).size) := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  let state := hermiteIncomingPrefix selected columns index.val matrix left
  have conditions := hermiteIncomingPrefix_canonical_conditions within matrix left positive upper futureZero index
  have ordered : selected index.castSucc < selected (Fin.last pivots) := by
    change index.val < pivots
    exact index.isLt
  have sourceExcluded : selected index.castSucc ∉ (hermiteColumnTargets index.castSucc index.val).map selected := by
    simpa only [List.mem_map, selected.injective.eq_iff, exists_eq_right] using
    hermiteColumnTargets_excluded index.castSucc index.val
  have targetExcluded : selected (Fin.last pivots) ∉ (hermiteColumnTargets index.castSucc index.val).map selected := by
    intro member
    obtain ⟨earlier, earlierMember, same⟩ := List.mem_map.mp member
    have equal := selected.injective same
    subst earlier
    have before := (hermiteColumnTargets_mem _ _ _).mp earlierMember
    simp only [Fin.val_last] at before
    have bounded := index.isLt
    omega
  have distinct := (hermiteColumnTargets_distinct index.castSucc index.val).map selected.injective
  have nextPositive := hermiteRowStage_diagonal_positive _ _ (ne_of_lt ordered) _ distinct sourceExcluded targetExcluded
    state.1 state.2 currentPositive conditions.1 conditions.2
  have nextMeasure := hermiteRowStage_potential_mono _ _ ordered _ distinct sourceExcluded targetExcluded
    state.1 state.2 currentPositive conditions.1 conditions.2
  have coordinate : columns index = selected index.castSucc := Fin.ext rfl
  change (∀ row, 0 < (hermiteIncomingPrefix selected columns (index.val + 1) matrix left).1 row row) ∧ _
  rw [hermiteIncomingPrefix_succ, coordinate]
  refine ⟨nextPositive, nextMeasure, ?_⟩
  intro notDivides
  exact hermiteRowStage_potential_decreases _ _ ordered _ distinct sourceExcluded targetExcluded
    state.1 state.2 currentPositive conditions.1 conditions.2 notDivides

/-- Every inner prefix preserves positive diagonals and is nonincreasing in the shared bit measure. -/
theorem hermiteIncomingPrefix_canonical_progress {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (count : ℕ) (countBound : count ≤ pivots) :
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let state := hermiteIncomingPrefix selected columns count matrix left
    (∀ index, 0 < state.1 index index) ∧
      (diagonalPotential (fun index => (state.1 index index).natAbs)).size ≤
        (diagonalPotential (fun index => (matrix index index).natAbs)).size := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  change (∀ index, 0 < (hermiteIncomingPrefix selected columns count matrix left).1 index index) ∧
    (diagonalPotential (fun index => ((hermiteIncomingPrefix selected columns count matrix left).1 index index).natAbs)).size ≤
      (diagonalPotential (fun index => (matrix index index).natAbs)).size
  induction count with
  | zero =>
    simpa only [hermiteIncomingPrefix, List.take_zero, List.foldl_nil] using
      And.intro positive (le_refl (diagonalPotential (fun index => (matrix index index).natAbs)).size)
  | succ count induction =>
    let index : Fin pivots := ⟨count, by omega⟩
    let state := hermiteIncomingPrefix selected columns count matrix left
    have previous := induction (by omega)
    have transition := hermiteIncomingPrefix_canonical_transition within matrix left positive upper futureZero index previous.1
    exact ⟨transition.1, transition.2.1.trans previous.2⟩

/-- One genuine gcd update forces strict progress through every later incoming prefix. -/
theorem hermiteIncomingPrefix_canonical_strict {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (index : Fin pivots) (count : ℕ) (countBound : count ≤ pivots) (visited : index.val < count)
    (notDivides :
      ¬ (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
        index.val matrix left).1 (Fin.castLE within index.castSucc) (Fin.castLE (by omega) index) ∣
        (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
        index.val matrix left).1 (Fin.castLE within (Fin.last pivots)) (Fin.castLE (by omega) index)) :
    (diagonalPotential (fun row => ((hermiteIncomingPrefix (Fin.castLEEmb within)
      (Fin.castLE (by omega : pivots ≤ dimension)) count matrix left).1 row row).natAbs)).size <
        (diagonalPotential (fun row => (matrix row row).natAbs)).size := by
  induction count with
  | zero => omega
  | succ count induction =>
    let next : Fin pivots := ⟨count, by omega⟩
    have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero count (by omega)
    have transition := hermiteIncomingPrefix_canonical_transition within matrix left positive upper futureZero next progress.1
    by_cases last : index.val = count
    · have same : index = next := Fin.ext last
      have strict := transition.2.2 (by simpa only [← same, Fin.coe_castLEEmb] using notDivides)
      exact strict.trans_le progress.2
    · exact transition.2.1.trans_lt (induction (by omega) (by omega) notDivides)

/-- Without strict progress, every canonical inner stage preserves lower triangularity. -/
theorem hermiteIncomingPrefix_lower_of_potential_le {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (lower : matrix.IsLowerTriangular) (count : ℕ) (countBound : count ≤ pivots)
    (noDecrease : (diagonalPotential (fun row => (matrix row row).natAbs)).size ≤
      (diagonalPotential (fun row => ((hermiteIncomingPrefix (Fin.castLEEmb within)
        (Fin.castLE (by omega : pivots ≤ dimension)) count matrix left).1 row row).natAbs)).size) :
    (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
      count matrix left).1.IsLowerTriangular := by
  induction count with
  | zero => exact lower
  | succ count induction =>
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let index : Fin pivots := ⟨count, by omega⟩
    let state := hermiteIncomingPrefix selected columns count matrix left
    have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero count (by omega)
    have transition := hermiteIncomingPrefix_canonical_transition within matrix left positive upper futureZero index progress.1
    have previous := induction (by omega) (noDecrease.trans transition.2.1)
    have divides : state.1 (selected index.castSucc) (columns index) ∣
        state.1 (selected (Fin.last pivots)) (columns index) := by
      by_contra notDivides
      have strict := hermiteIncomingPrefix_canonical_strict within matrix left positive upper futureZero
        index (count + 1) countBound (Nat.lt_succ_self count) notDivides
      exact (not_lt_of_ge noDecrease) strict
    have ordered : selected index.castSucc < selected (Fin.last pivots) := index.isLt
    have earlier : ∀ row ∈ (hermiteColumnTargets index.castSucc index.val).map selected,
        row < selected index.castSucc := by
      intro row member
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
      subst row
      change old.val < index.val
      exact ((hermiteColumnTargets_mem _ _ _).mp oldMember).1
    have excluded : selected index.castSucc ∉ (hermiteColumnTargets index.castSucc index.val).map selected := by
      intro member
      exact (lt_irrefl _) (earlier _ member)
    have distinct := (hermiteColumnTargets_distinct index.castSucc index.val).map selected.injective
    have coordinate : columns index = selected index.castSucc := Fin.ext rfl
    rw [coordinate] at divides
    have next := hermiteRowStage_lower_of_dvd _ _ ordered _ distinct excluded earlier state.1 state.2 previous divides
    change (hermiteIncomingPrefix selected columns (count + 1) matrix left).1.IsLowerTriangular
    rw [show count + 1 = index.val + 1 from rfl, hermiteIncomingPrefix_succ, coordinate]
    exact next

/-- The only nonzero residual coordinate after canonical elimination is the incoming diagonal. -/
theorem hermiteIncomingPrefix_canonical_pivot {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (beyond : ∀ row : Fin (pivots + 1), ∀ column : Fin dimension, pivots + 1 ≤ column.val →
      matrix (Fin.castLE within row) column = 0) :
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let state := hermiteIncomingPrefix selected columns pivots matrix left
    hermiteResidualPivot (selected (Fin.last pivots)) state.1 = some (selected (Fin.last pivots)) := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  let state := hermiteIncomingPrefix selected columns pivots matrix left
  let target := selected (Fin.last pivots)
  have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero pivots (by rfl)
  have pivotPositive : ∀ old, 0 < matrix (selected old.castSucc) (columns old) := by
    intro old
    change 0 < matrix (columns old) (columns old)
    exact positive _
  have pivotUpper : ∀ row column : Fin pivots, column < row → matrix (selected row.castSucc) (columns column) = 0 := by
    intro row column below
    change matrix (columns row) (columns column) = 0
    exact upper row column below
  have zeroOther (column : Fin dimension) (different : column ≠ target) : state.1 target column = 0 := by
    by_cases before : column.val < pivots
    · let old : Fin pivots := ⟨column.val, before⟩
      have coordinate : columns old = column := Fin.ext rfl
      have cleared := (hermiteIncomingPrefix_entries selected columns pivots (by rfl) matrix left pivotPositive pivotUpper old old.isLt).2.1
      simpa only [coordinate] using cleared
    · have after : pivots + 1 ≤ column.val := by
        have notEqual : column.val ≠ pivots := fun equal => different (Fin.ext equal)
        omega
      have unchanged := hermiteIncomingPrefix_zero_column selected columns pivots column matrix left
        (fun index => beyond index column after) target
      exact unchanged.trans (beyond (Fin.last pivots) column after)
  change hermiteResidualPivot target state.1 = some target
  cases found : hermiteResidualPivot target state.1 with
  | none =>
    have zero := congrFun ((hermiteResidualPivot_none target state.1).mp found) target
    change state.1 target target = 0 at zero
    have diagonalPositive : 0 < state.1 target target := progress.1 target
    exact False.elim ((ne_of_gt diagonalPositive) zero)
  | some column =>
    have nonzero := hermiteResidualPivot_nonzero target state.1 column found
    have equal : column = target := by
      by_contra different
      exact nonzero (zeroOther column different)
    exact congrArg some equal

/-- Positive residual extension leaves the incoming prefix diagonal unchanged. -/
theorem hermiteInsertRow_canonical_diagonal {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (beyond : ∀ row : Fin (pivots + 1), ∀ column : Fin dimension, pivots + 1 ≤ column.val →
      matrix (Fin.castLE within row) column = 0) :
    ∀ index, (hermiteInsertRow (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
      matrix left).1.1 index index =
      (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
        pivots matrix left).1 index index := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  let state := hermiteIncomingPrefix selected columns pivots matrix left
  let target := selected (Fin.last pivots)
  have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero pivots (by rfl)
  have found : hermiteResidualPivot (selected (Fin.last pivots))
      (hermiteIncomingPrefix selected columns pivots matrix left).1 = some (selected (Fin.last pivots)) :=
    hermiteIncomingPrefix_canonical_pivot within matrix left positive upper futureZero beyond
  have excluded : target ∉ Set.range (Fin.Embedding.init selected) := by
    rintro ⟨index, same⟩
    have values := congrArg Fin.val same
    change index.val = pivots at values
    exact (ne_of_lt index.isLt) values
  have pivotPositive : ∀ old, 0 < matrix (selected old.castSucc) (columns old) := by
    intro old
    change 0 < matrix (columns old) (columns old)
    exact positive _
  have pivotUpper : ∀ row column : Fin pivots, column < row → matrix (selected row.castSucc) (columns column) = 0 := by
    intro row column below
    change matrix (columns row) (columns column) = 0
    exact upper row column below
  have sourceZero : ∀ old, state.1 target ((Fin.Embedding.init selected) old) = 0 := by
    intro old
    have cleared := (hermiteIncomingPrefix_entries selected columns pivots (by rfl) matrix left pivotPositive pivotUpper old old.isLt).2.1
    exact cleared
  have extension := hermiteExtendPivot_diagonal_of_positive (Fin.Embedding.init selected) target excluded state.1 state.2
    (progress.1 target) sourceZero
  have pair : (hermiteInsertRow selected columns matrix left).1 =
      hermiteExtendPivot (Fin.Embedding.init selected) target target state.1 state.2 := by
    simp only [hermiteInsertRow, found, state, target]
  have diagonal (index) : (hermiteInsertRow selected columns matrix left).1.1 index index = state.1 index index := by
    rw [pair]
    exact extension index
  exact diagonal

/-- Canonical insertion appends the incoming diagonal pivot and is nonincreasing in the bit measure. -/
theorem hermiteInsertRow_canonical_progress {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (beyond : ∀ row : Fin (pivots + 1), ∀ column : Fin dimension, pivots + 1 ≤ column.val →
      matrix (Fin.castLE within row) column = 0) :
    let selected := Fin.castLEEmb within
    let columns := Fin.castLE (by omega : pivots ≤ dimension)
    let inserted := hermiteInsertRow selected columns matrix left
    inserted.2 = some (selected (Fin.last pivots)) ∧
      (∀ index, 0 < inserted.1.1 index index) ∧
      (diagonalPotential (fun index => (inserted.1.1 index index).natAbs)).size ≤
        (diagonalPotential (fun index => (matrix index index).natAbs)).size := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero pivots (by rfl)
  have found := hermiteIncomingPrefix_canonical_pivot within matrix left positive upper futureZero beyond
  have diagonal := hermiteInsertRow_canonical_diagonal within matrix left positive upper futureZero beyond
  refine ⟨(hermiteInsertRow_pivot selected columns matrix left).trans found, ?_, ?_⟩
  · intro index
    rw [diagonal]
    exact progress.1 index
  · simpa only [diagonal] using progress.2

/-- Strict inner progress survives residual selection and positive pivot extension. -/
theorem hermiteInsertRow_canonical_strict {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (beyond : ∀ row : Fin (pivots + 1), ∀ column : Fin dimension, pivots + 1 ≤ column.val →
      matrix (Fin.castLE within row) column = 0) (index : Fin pivots)
    (notDivides :
      ¬ (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
        index.val matrix left).1 (Fin.castLE within index.castSucc) (Fin.castLE (by omega) index) ∣
        (hermiteIncomingPrefix (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
        index.val matrix left).1 (Fin.castLE within (Fin.last pivots)) (Fin.castLE (by omega) index)) :
    (diagonalPotential (fun row => ((hermiteInsertRow (Fin.castLEEmb within)
      (Fin.castLE (by omega : pivots ≤ dimension)) matrix left).1.1 row row).natAbs)).size <
        (diagonalPotential (fun row => (matrix row row).natAbs)).size := by
  have diagonal := hermiteInsertRow_canonical_diagonal within matrix left positive upper futureZero beyond
  simpa only [diagonal] using
    hermiteIncomingPrefix_canonical_strict within matrix left positive upper futureZero index pivots
      (by rfl) index.isLt notDivides

/-- Insertion without strict progress preserves lower triangularity, including pivot extension. -/
theorem hermiteInsertRow_lower_of_potential_le {dimension pivots : ℕ}
    (within : pivots + 1 ≤ dimension) (matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (positive : ∀ index, 0 < matrix index index)
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (Fin.castLE (by omega : pivots ≤ dimension) row) (Fin.castLE (by omega : pivots ≤ dimension) column) = 0)
    (futureZero : ∀ index : Fin pivots,
      matrix (Fin.castLE (by omega : pivots ≤ dimension) index) (Fin.castLE within (Fin.last pivots)) = 0)
    (beyond : ∀ row : Fin (pivots + 1), ∀ column : Fin dimension, pivots + 1 ≤ column.val →
      matrix (Fin.castLE within row) column = 0)
    (lower : matrix.IsLowerTriangular)
    (noDecrease : (diagonalPotential (fun row => (matrix row row).natAbs)).size ≤
      (diagonalPotential (fun row => ((hermiteInsertRow (Fin.castLEEmb within)
        (Fin.castLE (by omega : pivots ≤ dimension)) matrix left).1.1 row row).natAbs)).size) :
    (hermiteInsertRow (Fin.castLEEmb within) (Fin.castLE (by omega : pivots ≤ dimension))
      matrix left).1.1.IsLowerTriangular := by
  let selected := Fin.castLEEmb within
  let columns := Fin.castLE (by omega : pivots ≤ dimension)
  let state := hermiteIncomingPrefix selected columns pivots matrix left
  have diagonal := hermiteInsertRow_canonical_diagonal within matrix left positive upper futureZero beyond
  have prefixLower := hermiteIncomingPrefix_lower_of_potential_le within matrix left positive upper futureZero
    lower pivots (by rfl) (by simpa only [diagonal] using noDecrease)
  have progress := hermiteIncomingPrefix_canonical_progress within matrix left positive upper futureZero pivots (by rfl)
  have found : hermiteResidualPivot (selected (Fin.last pivots))
      (hermiteIncomingPrefix selected columns pivots matrix left).1 = some (selected (Fin.last pivots)) :=
    hermiteIncomingPrefix_canonical_pivot within matrix left positive upper futureZero beyond
  have extension := hermiteExtendPivot_eq_of_positive_lower (Fin.Embedding.init selected)
    (selected (Fin.last pivots)) (fun index => index.isLt) state.1 state.2 prefixLower
    (progress.1 (selected (Fin.last pivots)))
  dsimp only [state] at extension
  change (hermiteInsertRow selected columns matrix left).1.1.IsLowerTriangular
  simpa only [hermiteInsertRow, found, extension] using prefixLower

/-- A successful insertion appends the selected row and column to the actual metadata. -/
theorem hermiteRowAdvance_indices_some {rows columns : ℕ}
    (original : Matrix (Fin rows) (Fin columns) ℤ) (processed : Fin rows)
    (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state})
    (excluded : processed ∉ Set.range state.val.2.2.1) (column : Fin columns)
    (columnExcluded : column ∉ Set.range state.val.2.2.2)
    (found : (hermiteInsertRow (Fin.Embedding.snoc state.val.2.2.1 excluded)
      state.val.2.2.2 state.val.1.1 state.val.1.2).2 = some column) :
    (hermiteRowAdvance original processed state).val.2 =
      ⟨state.val.2.1 + 1, Fin.Embedding.snoc state.val.2.2.1 excluded,
        Fin.Embedding.snoc state.val.2.2.2 columnExcluded⟩ := by
  rcases state with ⟨⟨⟨matrix, left⟩, rank, activeRows, pivotColumns⟩, invariant⟩
  dsimp only at found
  simp only [hermiteRowAdvance]
  split
  · rename_i absent
    have impossible := absent.symm.trans found
    contradiction
  · rename_i next present
    have equal : next = column := Option.some.inj (present.symm.trans found)
    subst next
    rfl

/-- On lower triangular input, a canonical outer prefix advances to the next canonical prefix. -/
theorem hermiteRowAdvance_canonical {dimension processed : ℕ}
    (within : processed + 1 ≤ dimension)
    (original matrix left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : original.IsLowerTriangular)
    (invariant : HermiteRowPrefix original processed
      ((matrix, left), ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩))
    (positive : ∀ index, 0 < matrix index index) :
    let state := (⟨((matrix, left), ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩), invariant⟩ :
      {state : HermiteRowState dimension dimension // HermiteRowPrefix original processed state})
    let next := hermiteRowAdvance original ⟨processed, by omega⟩ state
    next.val.2 = ⟨processed + 1, Fin.castLEEmb within, Fin.castLEEmb within⟩ ∧
      (∀ index, 0 < next.val.1.1 index index) ∧
      (diagonalPotential (fun index => (next.val.1.1 index index).natAbs)).size ≤
        (diagonalPotential (fun index => (matrix index index).natAbs)).size := by
  let embedding : Fin processed ↪ Fin dimension := Fin.castLEEmb (by omega)
  let source : Fin dimension := ⟨processed, by omega⟩
  have excluded : source ∉ Set.range embedding := by
    rintro ⟨index, same⟩
    have values := congrArg Fin.val same
    change index.val = processed at values
    exact (ne_of_lt index.isLt) values
  have extended : Fin.Embedding.snoc embedding excluded = Fin.castLEEmb within := by
    ext index
    cases index using Fin.lastCases <;> simp [source, embedding, Fin.Embedding.snoc_last, Fin.Embedding.snoc_castSucc]
  have upper : ∀ row column : Fin processed, column < row →
      matrix (embedding row) (embedding column) = 0 := by
    intro row column before
    exact invariant.2.2.2.2.1 before
  have progress := hermiteInsertRow_canonical_progress within matrix left positive upper
    (fun index => invariant.upper_right_zero lower _ _ index.isLt (by rfl))
    (invariant.incoming_rectangle_zero lower within)
  let state := (⟨((matrix, left), ⟨processed, embedding, embedding⟩), invariant⟩ :
    {state : HermiteRowState dimension dimension // HermiteRowPrefix original processed state})
  have found : (hermiteInsertRow (Fin.Embedding.snoc embedding excluded) embedding matrix left).2 = some source := by
    rw [extended]
    exact progress.1
  have indices := hermiteRowAdvance_indices_some original source state excluded source excluded found
  have pair := hermiteRowAdvance_pair original source state excluded
  change (hermiteRowAdvance original source state).val.2 = _ ∧ _
  refine ⟨?_, ?_⟩
  · simpa only [state, extended] using indices
  · rw [pair, extended]
    exact progress.2

/-- Every outer prefix on positive lower triangular input has canonical pivots and bounded progress. -/
theorem hermiteRowsPrefix_canonical {dimension : ℕ}
    (original : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : original.IsLowerTriangular) (positive : ∀ index, 0 < original index index)
    (processed : ℕ) (within : processed ≤ dimension) :
    let state := hermiteRowsPrefix original processed within
    state.val.2 = ⟨processed, Fin.castLEEmb within, Fin.castLEEmb within⟩ ∧
      (∀ index, 0 < state.val.1.1 index index) ∧
      (diagonalPotential (fun index => (state.val.1.1 index index).natAbs)).size ≤
        (diagonalPotential (fun index => (original index index).natAbs)).size := by
  induction processed with
  | zero =>
    refine ⟨?_, positive, le_refl _⟩
    dsimp only [hermiteRowsPrefix, hermiteRowInitial]
    congr 2 <;> ext index <;> exact index.elim0
  | succ processed induction =>
    let previous := hermiteRowsPrefix original processed (by omega : processed ≤ dimension)
    have earlier := induction (by omega)
    have invariant : HermiteRowPrefix original processed
        (previous.val.1, ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩) := by
      rw [← earlier.1]
      exact previous.property
    have representation : previous =
        ⟨(previous.val.1, ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩), invariant⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl earlier.1
    have advanced := hermiteRowAdvance_canonical within original previous.val.1.1 previous.val.1.2
      lower invariant earlier.2.1
    have nextEq : hermiteRowsPrefix original (processed + 1) within =
        hermiteRowAdvance original ⟨processed, by omega⟩
          ⟨(previous.val.1, ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩), invariant⟩ := by
      change hermiteRowAdvance original ⟨processed, by omega⟩ previous = _
      exact congrArg (hermiteRowAdvance original ⟨processed, by omega⟩) representation
    change (hermiteRowsPrefix original (processed + 1) within).val.2 = _ ∧ _
    rw [nextEq]
    exact ⟨advanced.1, advanced.2.1, advanced.2.2.trans earlier.2.2⟩

/-- An outer prefix without strict progress remains lower triangular. -/
theorem hermiteRowsPrefix_lower_of_potential_le {dimension : ℕ}
    (original : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : original.IsLowerTriangular) (positive : ∀ index, 0 < original index index)
    (processed : ℕ) (within : processed ≤ dimension)
    (noDecrease : (diagonalPotential (fun row => (original row row).natAbs)).size ≤
      (diagonalPotential (fun row => ((hermiteRowsPrefix original processed within).val.1.1 row row).natAbs)).size) :
    (hermiteRowsPrefix original processed within).val.1.1.IsLowerTriangular := by
  induction processed with
  | zero => exact lower
  | succ processed induction =>
    let previous := hermiteRowsPrefix original processed (by omega : processed ≤ dimension)
    have canonical := hermiteRowsPrefix_canonical original lower positive processed (by omega)
    have invariant : HermiteRowPrefix original processed
        (previous.val.1, ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩) := by
      rw [← canonical.1]
      exact previous.property
    let state := (⟨(previous.val.1, ⟨processed, Fin.castLEEmb (by omega), Fin.castLEEmb (by omega)⟩), invariant⟩ :
      {state : HermiteRowState dimension dimension // HermiteRowPrefix original processed state})
    have representation : previous = state := by
      apply Subtype.ext
      exact Prod.ext rfl canonical.1
    have nextEq : hermiteRowsPrefix original (processed + 1) within =
        hermiteRowAdvance original ⟨processed, by omega⟩ state := by
      exact congrArg (hermiteRowAdvance original ⟨processed, by omega⟩) representation
    have advance := hermiteRowAdvance_canonical within original previous.val.1.1 previous.val.1.2
      lower invariant canonical.2.1
    rw [nextEq] at noDecrease
    have previousLower := induction (by omega) (noDecrease.trans advance.2.2)
    let embedding : Fin processed ↪ Fin dimension := Fin.castLEEmb (by omega)
    let source : Fin dimension := ⟨processed, by omega⟩
    have excluded : source ∉ Set.range embedding := by
      rintro ⟨index, same⟩
      have values := congrArg Fin.val same
      change index.val = processed at values
      exact (ne_of_lt index.isLt) values
    have extended : Fin.Embedding.snoc embedding excluded = Fin.castLEEmb within := by
      ext index
      cases index using Fin.lastCases <;> simp [source, embedding, Fin.Embedding.snoc_last, Fin.Embedding.snoc_castSucc]
    have pair := hermiteRowAdvance_pair original source state excluded
    change (hermiteRowAdvance original source state).val.1 =
      (hermiteInsertRow (Fin.Embedding.snoc embedding excluded) embedding previous.val.1.1 previous.val.1.2).1 at pair
    rw [extended] at pair
    change (diagonalPotential (fun row => (original row row).natAbs)).size ≤
      (diagonalPotential (fun row => ((hermiteRowAdvance original source state).val.1.1 row row).natAbs)).size at noDecrease
    rw [pair] at noDecrease
    have nextLower := hermiteInsertRow_lower_of_potential_le within previous.val.1.1 previous.val.1.2
      canonical.2.1 (fun row column before => invariant.2.2.2.2.1 before)
      (fun index => invariant.upper_right_zero lower _ _ index.isLt (by rfl))
      (invariant.incoming_rectangle_zero lower within) previousLower
      (canonical.2.2.trans noDecrease)
    rw [nextEq]
    change (hermiteRowAdvance original source state).val.1.1.IsLowerTriangular
    rw [pair]
    exact nextLower

/-- Positive lower triangular input yields an upper triangular output with positive diagonal. -/
theorem hermiteRowsSweep_upper_positive {dimension : ℕ}
    (original : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : original.IsLowerTriangular) (positive : ∀ index, 0 < original index index) :
    (hermiteRowsSweep original).1.1.IsUpperTriangular ∧
      (∀ index, 0 < (hermiteRowsSweep original).1.1 index index) := by
  have canonical := hermiteRowsPrefix_canonical original lower positive dimension (by rfl)
  have upper := (hermiteRowsSweep_correct original).2.2.2.2.1
  have indices := canonical.1
  change (hermiteRowsSweep original).2 = _ at indices
  rw [indices] at upper
  exact ⟨upper, canonical.2.1⟩

/-- A complete row pass on positive lower triangular input is diagonal unless its bit measure decreases. -/
theorem hermiteRowsSweep_diagonal_or_progress {dimension : ℕ}
    (original : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : original.IsLowerTriangular) (positive : ∀ index, 0 < original index index) :
    (∀ row column, row ≠ column → (hermiteRowsSweep original).1.1 row column = 0) ∨
      (diagonalPotential (fun row => ((hermiteRowsSweep original).1.1 row row).natAbs)).size <
        (diagonalPotential (fun row => (original row row).natAbs)).size := by
  by_cases decreases :
      (diagonalPotential (fun row => ((hermiteRowsSweep original).1.1 row row).natAbs)).size <
        (diagonalPotential (fun row => (original row row).natAbs)).size
  · exact Or.inr decreases
  · left
    have lowerNew := hermiteRowsPrefix_lower_of_potential_le original lower positive dimension (by rfl)
      (Nat.le_of_not_gt decreases)
    have upper := (hermiteRowsSweep_upper_positive original lower positive).1
    intro row column different
    rcases lt_or_gt_of_ne different with before | after
    · exact lowerNew before
    · exact upper after

end Polytime2.IntegerMatrix
