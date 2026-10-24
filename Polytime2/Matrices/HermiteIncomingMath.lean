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

import Polytime2.Matrices.MinorInvarianceMath
import Polytime2.Matrices.HermiteColumnTraversalMath

/-! # Incoming-row prefixes with a fixed original minor

Process the selected pivot rows in increasing order against the last selected
row. Each stage normalizes earlier pivot rows. Every prefix retains the
absolute determinant on the selected rows and columns, so the determinant
bound always uses the input matrix before the prefix, independent of the
number of stages. Positive initial echelon pivots give positive visited pivots,
zero incoming entries, and canonical remainders above each visited pivot.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column] {pivots : ℕ}

/-- Mathematical increasing-pivot traversal for one incoming row. -/
def hermiteIncomingPrefix (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) : Matrix Row Column ℤ × Matrix Row Row ℤ :=
  ((List.finRange pivots).take count).foldl (fun state index =>
    hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
      ((hermiteColumnTargets index.castSucc index.val).map selectedRows) state.1 state.2) (matrix, left)

omit [DecidableEq Column] in
/-- Increasing-pivot prefixes append exactly one interleaved elimination stage. -/
theorem hermiteIncomingPrefix_succ (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (index : Fin pivots)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    hermiteIncomingPrefix selectedRows pivotColumns (index.val + 1) matrix left =
      hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
        ((hermiteColumnTargets index.castSucc index.val).map selectedRows)
        (hermiteIncomingPrefix selectedRows pivotColumns index.val matrix left).1
        (hermiteIncomingPrefix selectedRows pivotColumns index.val matrix left).2 := by
  have step := List.take_succ_eq_append_getElem (l := List.finRange pivots) (i := index.val) (by simp)
  have atIndex : (List.finRange pivots)[index.val]'(by simp) = index := by
    apply Fin.ext
    simp
  simp only [hermiteIncomingPrefix, step, atIndex, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The runtime forward prefix of the selected-row array realizes the same incoming step. -/
theorem hermiteIncomingPrefix_succ_forward (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (index : Fin pivots)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    hermiteIncomingPrefix selectedRows pivotColumns (index.val + 1) matrix left =
      hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
        ((List.ofFn selectedRows).take index.val)
        (hermiteIncomingPrefix selectedRows pivotColumns index.val matrix left).1
        (hermiteIncomingPrefix selectedRows pivotColumns index.val matrix left).2 := by
  rw [hermiteIncomingPrefix_succ]
  apply hermiteRowStage_perm
  · rw [hermiteColumnTargets_before_source index.castSucc index.val (by rfl),
      List.map_reverse, List.ofFn_eq_map, ← List.map_take]
    exact List.reverse_perm _
  · exact (hermiteColumnTargets_distinct index.castSucc index.val).map selectedRows.injective
  · simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
      hermiteColumnTargets_excluded index.castSucc index.val

/-- Every prefix retains the actual accumulated presentation and unimodularity. -/
theorem hermiteIncomingPrefix_preserves [Fintype Row] [Fintype Column]
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Column) (count : ℕ)
    (matrix original : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = matrix) (unit : IsUnit left.det) :
    (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 * original * right =
        (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 ∧
      IsUnit (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2.det := by
  unfold hermiteIncomingPrefix
  generalize ((List.finRange pivots).take count) = indices
  induction indices generalizing matrix left with
  | nil => exact ⟨equation, unit⟩
  | cons index indices induction =>
    have different : selectedRows index.castSucc ≠ selectedRows (Fin.last pivots) := by
      intro same
      have values := congrArg Fin.val (selectedRows.injective same)
      simp only [Fin.val_castSucc, Fin.val_last] at values
      exact (ne_of_lt index.isLt) values
    have excluded : selectedRows index.castSucc ∉
        (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
      simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
        hermiteColumnTargets_excluded index.castSucc index.val
    have preserved := hermiteRowStage_preserves _ _ different (pivotColumns index) _ excluded
      matrix original left right equation unit
    exact induction _ _ preserved.1 preserved.2

/-- A column zero on all selected rows is unchanged by every incoming prefix. -/
theorem hermiteIncomingPrefix_zero_column (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ) (other : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (zero : ∀ index, matrix (selectedRows index) other = 0) :
    ∀ row, (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 row other = matrix row other := by
  unfold hermiteIncomingPrefix
  refine List.foldlRecOn (motive := fun state : Matrix Row Column ℤ × Matrix Row Row ℤ =>
    ∀ row, state.1 row other = matrix row other) _ _ (fun row => rfl) ?_
  intro state preserved index _member
  have excluded : selectedRows index.castSucc ∉
      (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
    simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
      hermiteColumnTargets_excluded index.castSucc index.val
  have unchanged := hermiteRowStage_zero_column (selectedRows index.castSucc) (selectedRows (Fin.last pivots))
    (pivotColumns index) other _ ((hermiteColumnTargets_distinct index.castSucc index.val).map selectedRows.injective)
    excluded state.1 state.2 ((preserved _).trans (zero index.castSucc)) ((preserved _).trans (zero (Fin.last pivots)))
  intro row
  exact (unchanged row).trans (preserved row)

/-- A basis column supported outside the selected rows is unchanged by every prefix. -/
theorem hermiteIncomingPrefix_left_zero_column (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ) (other : Row)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (zero : ∀ index, left (selectedRows index) other = 0) :
    ∀ row, (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 row other = left row other := by
  unfold hermiteIncomingPrefix
  generalize ((List.finRange pivots).take count) = indices
  induction indices generalizing matrix left with
  | nil => intro row; rfl
  | cons index indices induction =>
    have excluded : selectedRows index.castSucc ∉
        (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
      simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
        hermiteColumnTargets_excluded index.castSucc index.val
    have unchanged := hermiteRowStage_left_zero_column (selectedRows index.castSucc)
      (selectedRows (Fin.last pivots)) (pivotColumns index) other _
      ((hermiteColumnTargets_distinct index.castSucc index.val).map selectedRows.injective)
      excluded matrix left (zero index.castSucc) (zero (Fin.last pivots))
    let next := hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
      ((hermiteColumnTargets index.castSucc index.val).map selectedRows) matrix left
    have tail := induction next.1 next.2 (fun nextIndex => (unchanged (selectedRows nextIndex)).trans (zero nextIndex))
    intro row
    exact (tail row).trans (unchanged row)

/-- A prefix leaves unvisited pivot rows and their accumulated basis rows untouched. -/
theorem hermiteIncomingPrefix_rows_other (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ) (row : Row)
    (notTarget : row ≠ selectedRows (Fin.last pivots))
    (notVisited : ∀ index : Fin pivots, index.val < count → row ≠ selectedRows index.castSucc)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 row = matrix row ∧
      (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 row = left row := by
  have foldPreserves (indices : List (Fin pivots))
      (visited : ∀ index ∈ indices, index.val < count) :
      ∀ (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ),
      (indices.foldl (fun state index =>
        hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
          ((hermiteColumnTargets index.castSucc index.val).map selectedRows) state.1 state.2)
        (matrix, left)).1 row = matrix row ∧
      (indices.foldl (fun state index =>
        hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
          ((hermiteColumnTargets index.castSucc index.val).map selectedRows) state.1 state.2)
        (matrix, left)).2 row = left row := by
    induction indices with
    | nil => intros; exact ⟨rfl, rfl⟩
    | cons index indices induction =>
      intro matrix left
      have before := visited index (by simp)
      have sourceExcluded : selectedRows index.castSucc ∉
          (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
        simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
          hermiteColumnTargets_excluded index.castSucc index.val
      have rowExcluded : row ∉ (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
        intro member
        obtain ⟨earlier, member, same⟩ := List.mem_map.mp member
        have earlierBefore := (hermiteColumnTargets_mem _ _ _).mp member
        have earlierLt : earlier.val < pivots := lt_trans earlierBefore.1 index.isLt
        exact notVisited ⟨earlier.val, earlierLt⟩ (lt_trans earlierBefore.1 before) (by simpa using same.symm)
      have step := hermiteRowStage_rows_other _ _ row (notVisited index before) notTarget (pivotColumns index) _
        ((hermiteColumnTargets_distinct index.castSucc index.val).map selectedRows.injective)
        sourceExcluded rowExcluded matrix left
      have tail := induction (fun next member => visited next (List.mem_cons_of_mem index member))
        (hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
          ((hermiteColumnTargets index.castSucc index.val).map selectedRows) matrix left).1
        (hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
          ((hermiteColumnTargets index.castSucc index.val).map selectedRows) matrix left).2
      exact ⟨tail.1.trans step.1, tail.2.trans step.2⟩
  apply foldPreserves
  intro index member
  have taken := (List.mem_take_iff_idxOf_lt (by simp)).mp member
  simpa only [List.idxOf_finRange] using taken

/-- A future pivot still has exactly its original matrix and basis rows. -/
theorem hermiteIncomingPrefix_future_row (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ) (index : Fin pivots)
    (future : count ≤ index.val) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 (selectedRows index.castSucc) =
        matrix (selectedRows index.castSucc) ∧
      (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 (selectedRows index.castSucc) =
        left (selectedRows index.castSucc) := by
  apply hermiteIncomingPrefix_rows_other
  · intro same
    have values := congrArg Fin.val (selectedRows.injective same)
    simp only [Fin.val_castSucc, Fin.val_last] at values
    exact (ne_of_lt index.isLt) values
  · intro earlier before same
    have values := congrArg Fin.val (selectedRows.injective same)
    simp only [Fin.val_castSucc] at values
    omega

/-- Positive echelon pivots retain positivity, incoming zeros, and canonical remainders. -/
theorem hermiteIncomingPrefix_entries (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (count : ℕ) (within : count ≤ pivots)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0) :
    ∀ index : Fin pivots, index.val < count →
      0 < (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
        (selectedRows index.castSucc) (pivotColumns index) ∧
      (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
        (selectedRows (Fin.last pivots)) (pivotColumns index) = 0 ∧
      (∀ earlier : Fin pivots, earlier < index →
        0 ≤ (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
          (selectedRows earlier.castSucc) (pivotColumns index) ∧
        (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
          (selectedRows earlier.castSucc) (pivotColumns index) <
        (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
          (selectedRows index.castSucc) (pivotColumns index)) ∧
      ∀ later : Fin pivots, index < later →
        (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
          (selectedRows later.castSucc) (pivotColumns index) = 0 := by
  induction count with
  | zero => intro index before; omega
  | succ count induction =>
    let pivot : Fin pivots := ⟨count, by omega⟩
    let state := hermiteIncomingPrefix selectedRows pivotColumns count matrix left
    have unchanged := hermiteIncomingPrefix_future_row selectedRows pivotColumns count pivot (by rfl) matrix left
    have sourcePositive : 0 < state.1 (selectedRows pivot.castSucc) (pivotColumns pivot) := by
      rw [show state.1 (selectedRows pivot.castSucc) = matrix (selectedRows pivot.castSucc) from unchanged.1]
      exact positive pivot
    have different : selectedRows pivot.castSucc ≠ selectedRows (Fin.last pivots) := by
      intro same
      have values := congrArg Fin.val (selectedRows.injective same)
      simp only [Fin.val_castSucc, Fin.val_last] at values
      exact (ne_of_lt pivot.isLt) values
    have distinct := (hermiteColumnTargets_distinct pivot.castSucc pivot.val).map selectedRows.injective
    have sourceExcluded : selectedRows pivot.castSucc ∉
        (hermiteColumnTargets pivot.castSucc pivot.val).map selectedRows := by
      simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
        hermiteColumnTargets_excluded pivot.castSucc pivot.val
    have targetExcluded : selectedRows (Fin.last pivots) ∉
        (hermiteColumnTargets pivot.castSucc pivot.val).map selectedRows := by
      intro member
      obtain ⟨earlier, member, same⟩ := List.mem_map.mp member
      have equal := selectedRows.injective same
      subst earlier
      have before := (hermiteColumnTargets_mem _ _ _).mp member
      simp only [Fin.val_last] at before
      have pivotLt := pivot.isLt
      omega
    have entries := hermiteRowStage_entries _ _ different (pivotColumns pivot) _ distinct sourceExcluded
      targetExcluded state.1 state.2 sourcePositive
    intro index before
    rw [show count + 1 = pivot.val + 1 from rfl, hermiteIncomingPrefix_succ]
    by_cases same : index = pivot
    · subst index
      refine ⟨?_, entries.2.1, ?_, ?_⟩
      · rw [entries.1]
        exact_mod_cast Int.gcd_pos_of_ne_zero_left _ (ne_of_gt sourcePositive)
      · intro earlier before
        rw [entries.1]
        apply entries.2.2
        apply List.mem_map.mpr
        refine ⟨earlier.castSucc, ?_, rfl⟩
        apply (hermiteColumnTargets_mem _ _ _).mpr
        refine ⟨before, ?_⟩
        intro same
        have equal := congrArg Fin.val same
        exact (ne_of_lt before) (Fin.ext equal)
      · intro later after
        have future := hermiteIncomingPrefix_future_row selectedRows pivotColumns (pivot.val + 1) later
          (by exact Nat.succ_le_of_lt after) matrix left
        have zero := (congrFun future.1 (pivotColumns pivot)).trans (upper later pivot after)
        simpa only [hermiteIncomingPrefix_succ] using zero
    · have earlier : index.val < count := by
        have notEqual : index.val ≠ count := fun equal => same (Fin.ext equal)
        omega
      have previous := induction (by omega) index earlier
      have sourceZero : state.1 (selectedRows pivot.castSucc) (pivotColumns index) = 0 := by
        rw [unchanged.1]
        exact upper pivot index earlier
      have preserved := hermiteRowStage_zero_column _ _ (pivotColumns pivot) (pivotColumns index) _
        distinct sourceExcluded state.1 state.2 sourceZero previous.2.1
      refine ⟨by rw [preserved]; exact previous.1, (preserved _).trans previous.2.1, ?_, ?_⟩
      · intro earlier before
        rw [preserved, preserved]
        exact previous.2.2.1 earlier before
      · intro later after
        exact (preserved _).trans (previous.2.2.2 later after)

/-- A completed incoming traversal normalizes the entire old pivot block. -/
theorem hermiteIncomingPrefix_normalized (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0) :
    let result := (hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).1
    let rows : Fin pivots → Row := fun index => selectedRows index.castSucc
    (result.submatrix rows pivotColumns).IsUpperTriangular ∧
      (∀ index, 0 < result (rows index) (pivotColumns index)) ∧
      (∀ row column : Fin pivots, row < column →
        0 ≤ result (rows row) (pivotColumns column) ∧
          result (rows row) (pivotColumns column) < result (rows column) (pivotColumns column)) := by
  have entries (index : Fin pivots) := hermiteIncomingPrefix_entries selectedRows pivotColumns pivots (by rfl)
    matrix left positive upper index index.isLt
  refine ⟨?_, fun index => (entries index).1, ?_⟩
  · intro row column below
    exact (entries column).2.2.2 row below
  · intro row column before
    exact (entries column).2.2.1 row before

/-- A prefix retains any minor containing the incoming row and the visited pivot rows. -/
theorem hermiteIncomingPrefix_supported_minor_natAbs {rank : ℕ}
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Column) (count : ℕ)
    (minorRows : Fin rank ↪ Row) (minorColumns : Fin rank ↪ Column)
    (targetMember : selectedRows (Fin.last pivots) ∈ Set.range minorRows)
    (visitedMember : ∀ index : Fin pivots, index.val < count →
      selectedRows index.castSucc ∈ Set.range minorRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1.submatrix minorRows minorColumns).det.natAbs =
      (matrix.submatrix minorRows minorColumns).det.natAbs := by
  have invariant (indices : List (Fin pivots)) (before : ∀ index ∈ indices, index.val < count) :
      ∀ (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ),
      ((indices.foldl (fun state index =>
        hermiteRowStage (selectedRows index.castSucc) (selectedRows (Fin.last pivots)) (pivotColumns index)
          ((hermiteColumnTargets index.castSucc index.val).map selectedRows) state.1 state.2)
        (matrix, left)).1.submatrix minorRows minorColumns).det.natAbs =
      (matrix.submatrix minorRows minorColumns).det.natAbs := by
    induction indices with
    | nil => intros; rfl
    | cons index indices induction =>
      intro matrix left
      have different : selectedRows index.castSucc ≠ selectedRows (Fin.last pivots) := by
        intro same
        have values := congrArg Fin.val (selectedRows.injective same)
        simp only [Fin.val_castSucc, Fin.val_last] at values
        exact (ne_of_lt index.isLt) values
      have excluded : selectedRows index.castSucc ∉
          (hermiteColumnTargets index.castSucc index.val).map selectedRows := by
        simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
          hermiteColumnTargets_excluded index.castSucc index.val
      have supported : ∀ row ∈ (hermiteColumnTargets index.castSucc index.val).map selectedRows,
          row ∈ Set.range minorRows := by
        intro row member
        obtain ⟨earlier, earlierMember, rowEq⟩ := List.mem_map.mp member
        subst row
        have earlierBefore := (hermiteColumnTargets_mem _ _ _).mp earlierMember
        let earlierIndex : Fin pivots := ⟨earlier.val, lt_trans earlierBefore.1 index.isLt⟩
        have equal : earlier = earlierIndex.castSucc := Fin.ext rfl
        rw [equal]
        exact visitedMember earlierIndex (lt_trans earlierBefore.1 (before index (by simp)))
      have preserved := hermiteRowStage_supported_minor_natAbs minorRows minorColumns _ _ different
        (visitedMember index (before index (by simp))) targetMember (pivotColumns index) _ excluded supported matrix left
      exact (induction (fun next member => before next (List.mem_cons_of_mem index member)) _ _).trans preserved
  apply invariant
  intro index member
  simpa only [List.idxOf_finRange] using (List.mem_take_iff_idxOf_lt (by simp)).mp member

/-- The same input minor controls every prefix, without repeated width substitution. -/
theorem hermiteIncomingPrefix_minor_natAbs (selectedRows : Fin (pivots + 1) ↪ Row)
    (selectedColumns : Fin (pivots + 1) ↪ Column) (pivotColumns : Fin pivots → Column) (count : ℕ)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1.submatrix selectedRows selectedColumns).det.natAbs =
      (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  exact hermiteIncomingPrefix_supported_minor_natAbs selectedRows pivotColumns count selectedRows selectedColumns
    ⟨Fin.last pivots, rfl⟩ (fun index _ => ⟨index.castSucc, rfl⟩) matrix left

/-- Every incoming-row prefix has a determinant bound in the original entry width. -/
theorem hermiteIncomingPrefix_minor_bound (width : ℕ) (selectedRows : Fin (pivots + 1) ↪ Row)
    (selectedColumns : Fin (pivots + 1) ↪ Column) (pivotColumns : Fin pivots → Column) (count : ℕ)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1.submatrix selectedRows selectedColumns).det.natAbs <
      2 ^ ((pivots + 1) * (width + (pivots + 1)) + 1) := by
  rw [hermiteIncomingPrefix_minor_natAbs]
  exact determinant_bound width (pivots + 1) _ (fun row column => entryBound (selectedRows row) (selectedColumns column))

/-- A truncated minor bounds a future incoming entry at any intermediate prefix. -/
theorem hermiteIncomingPrefix_truncated_bound (width count : ℕ) (within : count ≤ pivots)
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots → Column)
    (minorRows : Fin (count + 1) ↪ Row) (minorColumns : Fin (count + 1) ↪ Column)
    (rows : ∀ index : Fin count, minorRows index.castSucc =
      selectedRows (Fin.castLE within index).castSucc)
    (target : minorRows (Fin.last count) = selectedRows (Fin.last pivots))
    (columns : ∀ index : Fin count, minorColumns index.castSucc = pivotColumns (Fin.castLE within index))
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
      (selectedRows (Fin.last pivots)) (minorColumns (Fin.last count))).natAbs <
      2 ^ ((count + 1) * (width + (count + 1)) + 1) := by
  let result := (hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
  have entries (index : Fin count) := hermiteIncomingPrefix_entries selectedRows pivotColumns count within
    matrix left positive upper (Fin.castLE within index) index.isLt
  have triangular : (result.submatrix minorRows minorColumns).IsUpperTriangular := by
    intro row column below
    have columnLt : column.val < count := lt_of_lt_of_le below (Nat.le_of_lt_succ row.isLt)
    let index : Fin count := ⟨column.val, columnLt⟩
    have columnEq : column = index.castSucc := Fin.ext rfl
    change result (minorRows row) (minorColumns column) = 0
    rw [columnEq, columns]
    by_cases rowLt : row.val < count
    · let later : Fin count := ⟨row.val, rowLt⟩
      have rowEq : row = later.castSucc := Fin.ext rfl
      rw [rowEq, rows]
      exact (entries index).2.2.2 (Fin.castLE within later) below
    · have rowEq : row = Fin.last count := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [rowEq, target]
      exact (entries index).2.1
  have diagonal := upperTriangular_diagonal_natAbs_le _ triangular (Fin.last count) (by
    intro other different
    have otherLt : other.val < count := by
      have notEqual : other.val ≠ count := fun equal => different (Fin.ext equal)
      omega
    let index : Fin count := ⟨other.val, otherLt⟩
    have otherEq : other = index.castSucc := Fin.ext rfl
    change result (minorRows other) (minorColumns other) ≠ 0
    rw [otherEq, rows, columns]
    exact ne_of_gt (entries index).1)
  have invariant := hermiteIncomingPrefix_supported_minor_natAbs selectedRows pivotColumns count minorRows minorColumns
    ⟨Fin.last count, target⟩ (by
      intro index before
      let small : Fin count := ⟨index.val, before⟩
      refine ⟨small.castSucc, ?_⟩
      exact (rows small).trans (congrArg selectedRows (congrArg Fin.castSucc (Fin.ext rfl)))) matrix left
  have determinantBound : (result.submatrix minorRows minorColumns).det.natAbs <
      2 ^ ((count + 1) * (width + (count + 1)) + 1) := by
    rw [invariant]
    exact determinant_bound width (count + 1) _ (fun row column => entryBound (minorRows row) (minorColumns column))
  simpa only [Matrix.submatrix_apply, target] using diagonal.trans_lt determinantBound

/-- The completed incoming entry has an original-width minor bound, with no extra shape witness. -/
theorem hermiteIncomingPrefix_incoming_bound (width : ℕ)
    (selectedRows : Fin (pivots + 1) ↪ Row) (selectedColumns : Fin (pivots + 1) ↪ Column)
    (pivotColumns : Fin pivots → Column)
    (columns : ∀ index, selectedColumns index.castSucc = pivotColumns index)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ((hermiteIncomingPrefix selectedRows pivotColumns pivots matrix left).1
      (selectedRows (Fin.last pivots)) (selectedColumns (Fin.last pivots))).natAbs <
      2 ^ ((pivots + 1) * (width + (pivots + 1)) + 1) := by
  simpa only [Fin.castLE_refl] using hermiteIncomingPrefix_truncated_bound width pivots (by rfl)
    selectedRows pivotColumns selectedRows selectedColumns (fun _ => rfl) rfl columns matrix left
    positive upper entryBound


end Polytime2.IntegerMatrix
