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

import Mathlib.Data.Int.NatAbs
import Mathlib.LinearAlgebra.Matrix.Block
import Polytime2.Matrices.HermiteStageMath
import Polytime2.Matrices.MinorBoundsMath

/-! # Minor invariance under supported Hermite stages

Select equally many rows and columns. Row additions and determinant-one two-row
operations inside the selected rows commute with taking that minor and retain
its absolute determinant. The same holds for an interleaved Hermite stage when
its source, incoming row, and earlier rows lie in the selection. This invariant
connects an incoming entry to a fixed original minor even when rows outside the
selection still have nonzero entries in the selected columns.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] {rank : ℕ}

/-- Row addition inside a selected row set commutes with taking a submatrix. -/
theorem rowAdd_submatrix (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (target source : Fin rank) (coefficient : ℤ) (matrix : Matrix Row Column ℤ) :
    (rowAdd (selectedRows target) (selectedRows source) coefficient matrix).submatrix selectedRows selectedColumns =
      rowAdd target source coefficient (matrix.submatrix selectedRows selectedColumns) := by
  ext row column
  by_cases same : row = target
  · subst row
    simp [rowAdd, Matrix.submatrix_apply]
  · have mappedDifferent : selectedRows row ≠ selectedRows target := fun equal => same (selectedRows.injective equal)
    simp [rowAdd, Matrix.submatrix_apply, Matrix.updateRow_ne same, Matrix.updateRow_ne mappedDifferent]

/-- Simultaneous two-row operations also commute with taking a selected minor. -/
theorem rowPair_submatrix (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (first second : Fin rank) (coefficients : Matrix (Fin 2) (Fin 2) ℤ) (matrix : Matrix Row Column ℤ) :
    (rowPair (selectedRows first) (selectedRows second) coefficients matrix).submatrix selectedRows selectedColumns =
      rowPair first second coefficients (matrix.submatrix selectedRows selectedColumns) := by
  ext row column
  by_cases atSecond : row = second
  · subst row
    simp [rowPair, Matrix.submatrix_apply]
  · have mappedNotSecond : selectedRows row ≠ selectedRows second := fun equal => atSecond (selectedRows.injective equal)
    by_cases atFirst : row = first
    · subst row
      simp [rowPair, Matrix.submatrix_apply, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne mappedNotSecond]
    · have mappedNotFirst : selectedRows row ≠ selectedRows first := fun equal => atFirst (selectedRows.injective equal)
      simp [rowPair, Matrix.submatrix_apply, Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst,
        Matrix.updateRow_ne mappedNotSecond, Matrix.updateRow_ne mappedNotFirst]

/-- A row addition inside a minor preserves its determinant magnitude. -/
theorem rowAdd_minor_natAbs (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (target source : Fin rank) (different : target ≠ source) (coefficient : ℤ) (matrix : Matrix Row Column ℤ) :
    ((rowAdd (selectedRows target) (selectedRows source) coefficient matrix).submatrix selectedRows selectedColumns).det.natAbs =
      (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  rw [rowAdd_submatrix, rowAdd_eq_mul, Matrix.det_mul, rowAdd_unimodular target source different, one_mul]

/-- A determinant-one pair action inside a minor preserves its determinant magnitude. -/
theorem rowPair_minor_natAbs (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (first second : Fin rank) (different : first ≠ second) (coefficients : Matrix (Fin 2) (Fin 2) ℤ)
    (determinant : coefficients.det = 1) (matrix : Matrix Row Column ℤ) :
    ((rowPair (selectedRows first) (selectedRows second) coefficients matrix).submatrix selectedRows selectedColumns).det.natAbs =
      (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  rw [rowPair_submatrix, rowPair_eq_mul, Matrix.det_mul, Int.natAbs_mul]
  rw [Int.isUnit_iff_natAbs_eq.mp (rowPair_unimodular first second different coefficients determinant), one_mul]

variable [DecidableEq Column]

/-- Either branch of the progress-sensitive step preserves the selected minor. -/
theorem hermiteRowStep_minor_natAbs (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (source target : Fin rank) (different : source ≠ target) (column : Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((hermiteRowStep (selectedRows source) (selectedRows target) column matrix left).1.submatrix
      selectedRows selectedColumns).det.natAbs = (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  unfold hermiteRowStep
  split_ifs
  · exact rowAdd_minor_natAbs selectedRows selectedColumns target source different.symm _ matrix
  · exact rowPair_minor_natAbs selectedRows selectedColumns source target different _ (bezoutMatrix_det _ _) matrix

/-- All remainder normalizations inside the minor preserve its determinant magnitude. -/
theorem rowRemainderSweep_minor_natAbs (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (source : Fin rank) (column : Column) (targets : List (Fin rank)) (excluded : source ∉ targets)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((rowRemainderSweep (selectedRows source) column (targets.map selectedRows) matrix left).1.submatrix
      selectedRows selectedColumns).det.natAbs = (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  induction targets with
  | nil => rfl
  | cons target targets induction =>
    have different : target ≠ source := fun same => excluded (List.mem_cons.mpr (Or.inl same.symm))
    have tailExcluded : source ∉ targets := fun member => excluded (List.mem_cons_of_mem target member)
    let previous := rowRemainderSweep (selectedRows source) column (targets.map selectedRows) matrix left
    have step := rowAdd_minor_natAbs selectedRows selectedColumns target source different
      (-(previous.1 (selectedRows target) column / previous.1 (selectedRows source) column)) previous.1
    exact step.trans (induction tailExcluded)

/-- A full interleaved stage supported on the selected rows retains the original minor magnitude. -/
theorem hermiteRowStage_minor_natAbs (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (source target : Fin rank) (different : source ≠ target) (column : Column)
    (earlierRows : List (Fin rank)) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((hermiteRowStage (selectedRows source) (selectedRows target) column (earlierRows.map selectedRows) matrix left).1.submatrix
      selectedRows selectedColumns).det.natAbs = (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  have eliminated := hermiteRowStep_minor_natAbs selectedRows selectedColumns source target different column matrix left
  exact (rowRemainderSweep_minor_natAbs selectedRows selectedColumns source column earlierRows sourceExcluded
    (hermiteRowStep (selectedRows source) (selectedRows target) column matrix left).1
    (hermiteRowStep (selectedRows source) (selectedRows target) column matrix left).2).trans eliminated

/-- A stage preserves any minor containing its affected rows, regardless of ambient row numbering. -/
theorem hermiteRowStage_supported_minor_natAbs (selectedRows : Fin rank ↪ Row)
    (selectedColumns : Fin rank ↪ Column) (source target : Row) (different : source ≠ target)
    (sourceMember : source ∈ Set.range selectedRows) (targetMember : target ∈ Set.range selectedRows)
    (column : Column) (earlierRows : List Row) (sourceExcluded : source ∉ earlierRows)
    (supported : ∀ row ∈ earlierRows, row ∈ Set.range selectedRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) :
    ((hermiteRowStage source target column earlierRows matrix left).1.submatrix
      selectedRows selectedColumns).det.natAbs = (matrix.submatrix selectedRows selectedColumns).det.natAbs := by
  classical
  obtain ⟨sourceIndex, sourceEq⟩ := sourceMember
  obtain ⟨targetIndex, targetEq⟩ := targetMember
  let : Nonempty (Fin rank) := ⟨sourceIndex⟩
  let lift := Function.invFun selectedRows
  have mapped : (earlierRows.map lift).map selectedRows = earlierRows := by
    rw [List.map_map]
    calc
      earlierRows.map (selectedRows ∘ lift) = earlierRows.map id := by
        apply List.map_congr_left
        intro row member
        exact Function.invFun_eq (supported row member)
      _ = earlierRows := List.map_id _
  have excluded : sourceIndex ∉ earlierRows.map lift := by
    intro member
    apply sourceExcluded
    rw [← mapped, ← sourceEq]
    exact List.mem_map_of_mem member
  have distinct : sourceIndex ≠ targetIndex := fun same => different (by rw [← sourceEq, ← targetEq, same])
  simpa only [sourceEq, targetEq, mapped] using hermiteRowStage_minor_natAbs selectedRows selectedColumns
    sourceIndex targetIndex distinct column (earlierRows.map lift) excluded matrix left

/-- The retained original minor gives a fixed width for a supported stage minor. -/
theorem hermiteRowStage_minor_bound (width : ℕ)
    (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (source target : Fin rank) (different : source ≠ target) (column : Column)
    (earlierRows : List (Fin rank)) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ((hermiteRowStage (selectedRows source) (selectedRows target) column (earlierRows.map selectedRows) matrix left).1.submatrix
      selectedRows selectedColumns).det.natAbs < 2 ^ (rank * (width + rank) + 1) := by
  rw [hermiteRowStage_minor_natAbs selectedRows selectedColumns source target different column earlierRows sourceExcluded matrix left]
  exact determinant_bound width rank _ (fun row column => entryBound (selectedRows row) (selectedColumns column))

/-- A triangular minor bounds any diagonal entry when the other diagonal entries are nonzero. -/
theorem upperTriangular_diagonal_natAbs_le (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (upper : matrix.IsUpperTriangular) (index : Fin rank)
    (others : ∀ other, other ≠ index → matrix other other ≠ 0) :
    (matrix index index).natAbs ≤ matrix.det.natAbs := by
  by_cases zero : matrix index index = 0
  · simp [zero]
  · have nonzero (other : Fin rank) : matrix other other ≠ 0 := by
      by_cases same : other = index
      · simpa only [same] using zero
      · exact others other same
    calc
      (matrix index index).natAbs ≤ ∏ other, (matrix other other).natAbs :=
        Finset.single_le_prod (fun other _ => Nat.succ_le_of_lt (Int.natAbs_pos.mpr (nonzero other))) (Finset.mem_univ index)
      _ = (∏ other, matrix other other).natAbs := (map_prod Int.natAbsHom _ _).symm
      _ = matrix.det.natAbs := congrArg Int.natAbs (Matrix.det_of_isUpperTriangular upper).symm

/-- A triangular stage minor bounds its incoming diagonal entry by the original input width. -/
theorem hermiteRowStage_diagonal_bound (width : ℕ)
    (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (source target : Fin rank) (different : source ≠ target) (column : Column)
    (earlierRows : List (Fin rank)) (sourceExcluded : source ∉ earlierRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (index : Fin rank)
    (upper : ((hermiteRowStage (selectedRows source) (selectedRows target) column (earlierRows.map selectedRows) matrix left).1.submatrix
      selectedRows selectedColumns).IsUpperTriangular)
    (others : ∀ other, other ≠ index →
      (hermiteRowStage (selectedRows source) (selectedRows target) column (earlierRows.map selectedRows) matrix left).1
        (selectedRows other) (selectedColumns other) ≠ 0) :
    ((hermiteRowStage (selectedRows source) (selectedRows target) column (earlierRows.map selectedRows) matrix left).1
      (selectedRows index) (selectedColumns index)).natAbs < 2 ^ (rank * (width + rank) + 1) :=
  (upperTriangular_diagonal_natAbs_le _ upper index others).trans_lt
    (hermiteRowStage_minor_bound width selectedRows selectedColumns source target different column earlierRows sourceExcluded matrix left entryBound)

end Polytime2.IntegerMatrix
