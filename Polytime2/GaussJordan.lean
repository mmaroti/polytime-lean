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

import Polytime2.Matrix

/-! # Gauss–Jordan elimination with independent rectangular dimensions

Each column is visited once. A nonzero entry at or below the next pivot row
is exchanged into place, normalized, and cleared from all other rows.
The mathematical definitions and correctness proofs accompany this
implementation's independent machine realization.
-/

namespace Polytime2.GaussJordan

-- scalarLevel: the mathematical field carrier; finite presentations are supplied by the backend.
universe scalarLevel
variable {Scalar : Type scalarLevel} [Field Scalar] [DecidableEq Scalar]
variable {rows columns : ℕ}

open MatrixOperations

/-- Search only the unprocessed rows of the current column. -/
def findPivot (matrix : Matrix (Fin rows) (Fin columns) Scalar) (nextRow : ℕ)
    (column : Fin columns) : Option (Fin rows) :=
  (List.finRange rows).find? fun row => decide (nextRow ≤ row.val ∧ matrix row column ≠ 0)

theorem findPivot_some (matrix : Matrix (Fin rows) (Fin columns) Scalar) (nextRow : ℕ)
    (column : Fin columns) (source : Fin rows) (found : findPivot matrix nextRow column = some source) :
    nextRow ≤ source.val ∧ matrix source column ≠ 0 := by
  simpa [findPivot] using List.find?_some found

theorem findPivot_none (matrix : Matrix (Fin rows) (Fin columns) Scalar) (nextRow : ℕ)
    (column : Fin columns) (missing : findPivot matrix nextRow column = none) :
    ∀ row : Fin rows, nextRow ≤ row.val → matrix row column = 0 := by
  have absent := List.find?_eq_none.mp missing
  intro row eligible
  have impossible := absent row (List.mem_finRange row)
  simpa [eligible] using impossible

/-- The least eligible nonzero row, with the row count as an absent sentinel,
agrees with the mathematical pivot search. -/
theorem findPivot_eq_of_minimal (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (start candidate : ℕ) (column : Fin columns) (eligible : start ≤ candidate)
    (bounded : candidate ≤ rows)
    (skipped : ∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0)
    (nonzero : ∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) :
    findPivot matrix start column =
      if valid : candidate < rows then some ⟨candidate, valid⟩ else none := by
  classical
  by_cases active : candidate < rows
  · simp only [active, ↓reduceDIte, findPivot, List.find?_eq_getElem?_findIdx]
    have index : (List.finRange rows).findIdx
        (fun row => decide (start ≤ row.val ∧ matrix row column ≠ 0)) = candidate := by
      apply (List.findIdx_eq (by simpa using active)).mpr
      constructor
      · simpa using And.intro eligible (nonzero active)
      · intro index earlier
        by_cases eligibleIndex : start ≤ index
        · have zero := skipped ⟨index, by omega⟩ eligibleIndex earlier
          simp [zero]
        · simp [eligibleIndex]
    rw [index]
    simp [active]
  · simp only [active, ↓reduceDIte]
    apply List.find?_eq_none.mpr
    intro row _
    by_cases eligibleRow : start ≤ row.val
    · have zero := skipped row eligibleRow (by have rowBound := row.isLt; omega)
      simp [eligibleRow, zero]
    · simp [eligibleRow]

/-- The pivot-row counter can reach the row count, including when there are no rows. -/
def columnStep (matrix : Matrix (Fin rows) (Fin columns) Scalar) (nextRow : ℕ)
    (column : Fin columns) : Matrix (Fin rows) (Fin columns) Scalar × ℕ :=
  if valid : nextRow < rows then
    match findPivot matrix nextRow column with
    | none => (matrix, nextRow)
    | some source => (pivotStep matrix ⟨nextRow, valid⟩ source column, nextRow + 1)
  else (matrix, nextRow)

/-- A column traversal; its finite list is the mathematical version of the bounded counter loop. -/
def eliminateColumns : Matrix (Fin rows) (Fin columns) Scalar → ℕ → List (Fin columns) →
    Matrix (Fin rows) (Fin columns) Scalar × ℕ
  | matrix, nextRow, [] => (matrix, nextRow)
  | matrix, nextRow, column :: remaining =>
    let next := columnStep matrix nextRow column
    eliminateColumns next.1 next.2 remaining

def eliminate (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    Matrix (Fin rows) (Fin columns) Scalar :=
  (eliminateColumns matrix 0 (List.finRange columns)).1

theorem columnStep_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (column : Fin columns) :
    Matrix.RowEquivalent matrix (columnStep matrix nextRow column).1 := by
  unfold columnStep
  split_ifs with valid
  · cases found : findPivot matrix nextRow column with
    | none => exact Matrix.RowEquivalent.refl matrix
    | some source =>
      exact pivotStep_rowEquivalent matrix _ source column
        (findPivot_some matrix nextRow column source found).2
  · exact Matrix.RowEquivalent.refl matrix

theorem eliminateColumns_rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (remaining : List (Fin columns)) :
    Matrix.RowEquivalent matrix (eliminateColumns matrix nextRow remaining).1 := by
  induction remaining generalizing matrix nextRow with
  | nil => exact Matrix.RowEquivalent.refl matrix
  | cons column remaining hypothesis =>
    exact (columnStep_rowEquivalent matrix nextRow column).trans
      (hypothesis (columnStep matrix nextRow column).1 (columnStep matrix nextRow column).2)

/-- This is the required invertible-matrix contract, not merely row-space equality. -/
theorem rowEquivalent (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    Matrix.RowEquivalent matrix (eliminate matrix) :=
  eliminateColumns_rowEquivalent matrix 0 (List.finRange columns)

theorem columnStep_row_bound (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (column : Fin columns) (bounded : nextRow ≤ rows) :
    nextRow ≤ (columnStep matrix nextRow column).2 ∧
      (columnStep matrix nextRow column).2 ≤ rows := by
  unfold columnStep
  split_ifs with valid
  · cases findPivot matrix nextRow column <;> simp <;> omega
  · exact ⟨le_rfl, bounded⟩

theorem eliminateColumns_row_bound (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (remaining : List (Fin columns)) (bounded : nextRow ≤ rows) :
    nextRow ≤ (eliminateColumns matrix nextRow remaining).2 ∧
      (eliminateColumns matrix nextRow remaining).2 ≤ rows := by
  induction remaining generalizing matrix nextRow with
  | nil => exact ⟨le_rfl, bounded⟩
  | cons column remaining hypothesis =>
    have stepBound := columnStep_row_bound matrix nextRow column bounded
    have tailBound := hypothesis (columnStep matrix nextRow column).1
      (columnStep matrix nextRow column).2 stepBound.2
    exact ⟨stepBound.1.trans tailBound.1, tailBound.2⟩

/-- Completed rows have isolated unit pivots and zeros below through each pivot.
Every unprocessed row vanishes in the columns already visited. -/
def Invariant (matrix : Matrix (Fin rows) (Fin columns) Scalar) (nextRow nextColumn : ℕ) : Prop :=
  nextRow ≤ rows ∧
  (∀ row : Fin rows, row.val < nextRow → ∃ pivot : Fin columns,
    pivot.val < nextColumn ∧ matrix.IsLeadingEntry row pivot ∧ matrix row pivot = 1 ∧
    (∀ other, other ≠ row → matrix other pivot = 0) ∧
    (∀ lower, row < lower → ∀ column, column ≤ pivot → matrix lower column = 0)) ∧
  (∀ row : Fin rows, nextRow ≤ row.val → ∀ column : Fin columns,
    column.val < nextColumn → matrix row column = 0)

theorem invariant_initial (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    Invariant matrix 0 0 := by
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · intro row bound; omega
  · intro row bound column earlier; omega

omit [DecidableEq Scalar] in
private theorem invariant_skip (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (column : Fin columns) (invariant : Invariant matrix nextRow column.val)
    (zero : ∀ row, nextRow ≤ row.val → matrix row column = 0) :
    Invariant matrix nextRow (column.val + 1) := by
  obtain ⟨rowBound, completed, pending⟩ := invariant
  refine ⟨rowBound, ?_, ?_⟩
  · intro row processed
    obtain ⟨pivot, earlier, leading, unit, isolated, below⟩ := completed row processed
    exact ⟨pivot, by omega, leading, unit, isolated, below⟩
  · intro row eligible other earlier
    by_cases same : other = column
    · subst other; exact zero row eligible
    · exact pending row eligible other (by have different := Fin.ext_iff.not.mp same; omega)

omit [DecidableEq Scalar] in
private theorem invariant_pivot (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (column : Fin columns) (source : Fin rows) (valid : nextRow < rows)
    (eligible : nextRow ≤ source.val) (nonzero : matrix source column ≠ 0)
    (invariant : Invariant matrix nextRow column.val) :
    Invariant (pivotStep matrix ⟨nextRow, valid⟩ source column) (nextRow + 1) (column.val + 1) := by
  obtain ⟨rowBound, completed, pending⟩ := invariant
  let target : Fin rows := ⟨nextRow, valid⟩
  let reduced := pivotStep matrix target source column
  have unchanged : ∀ row other, other.val < column.val → reduced row other = matrix row other := by
    intro row other earlier
    exact pivotStep_preserves_column matrix target source column other
      (pending target (by rfl) other earlier) (pending source eligible other earlier) row
  have pivotUnit : reduced target column = 1 := pivotStep_pivot matrix target source column nonzero
  have pivotIsolated : ∀ row, row ≠ target → reduced row column = 0 := by
    intro row otherRow
    exact pivotStep_zero matrix target source row column nonzero otherRow
  change Invariant reduced (nextRow + 1) (column.val + 1)
  refine ⟨by omega, ?_, ?_⟩
  · intro row processed
    by_cases previously : row.val < nextRow
    · obtain ⟨pivot, earlier, leading, unit, isolated, below⟩ := completed row previously
      refine ⟨pivot, by omega, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro other left
        rw [unchanged row other (by omega)]
        exact leading.1 other left
      · simpa only [unchanged row pivot earlier] using leading.2
      · rw [unchanged row pivot earlier]; exact unit
      · intro other distinct
        rw [unchanged other pivot earlier]; exact isolated other distinct
      · intro lower belowRow other left
        rw [unchanged lower other (by omega)]
        exact below lower belowRow other left
    · have same : row = target := Fin.ext (by dsimp [target]; omega)
      subst row
      refine ⟨column, by omega, ⟨?_, ?_⟩, pivotUnit, pivotIsolated, ?_⟩
      · intro other left
        rw [unchanged target other left]
        exact pending target (by rfl) other left
      · rw [pivotUnit]; exact one_ne_zero
      · intro lower belowRow other left
        by_cases same : other = column
        · subst other
          exact pivotIsolated lower (by intro equality; subst lower; exact lt_irrefl _ belowRow)
        · rw [unchanged lower other (by have different := Fin.ext_iff.not.mp same; omega)]
          exact pending lower (by dsimp [target] at belowRow; omega) other (by omega)
  · intro row eligibleRow other earlier
    have otherRow : row ≠ target := by intro same; subst row; dsimp [target] at eligibleRow; omega
    by_cases same : other = column
    · subst other; exact pivotIsolated row otherRow
    · rw [unchanged row other (by have different := Fin.ext_iff.not.mp same; omega)]
      exact pending row (by omega) other (by omega)

/-- The invariant advances even when a column has no remaining pivot. -/
theorem columnStep_invariant (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (column : Fin columns) (invariant : Invariant matrix nextRow column.val) :
    Invariant (columnStep matrix nextRow column).1 (columnStep matrix nextRow column).2
      (column.val + 1) := by
  unfold columnStep
  split_ifs with valid
  · cases found : findPivot matrix nextRow column with
    | none =>
      exact invariant_skip matrix nextRow column invariant
        (findPivot_none matrix nextRow column found)
    | some source =>
      have pivot := findPivot_some matrix nextRow column source found
      exact invariant_pivot matrix nextRow column source valid pivot.1 pivot.2 invariant
  · exact invariant_skip matrix nextRow column invariant
      (by intro row eligible; omega)

/-- Visiting the remaining consecutive columns establishes the final invariant. -/
theorem eliminateColumns_invariant (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow start : ℕ) (remaining : List (Fin columns))
    (consecutive : remaining.map Fin.val = List.range' start remaining.length)
    (invariant : Invariant matrix nextRow start) :
    Invariant (eliminateColumns matrix nextRow remaining).1
      (eliminateColumns matrix nextRow remaining).2 (start + remaining.length) := by
  induction remaining generalizing matrix nextRow start with
  | nil => simpa [eliminateColumns] using invariant
  | cons column remaining hypothesis =>
    have atStart : column.val = start := by
      simpa [List.range'_succ] using congrArg List.head? consecutive
    have tailConsecutive : remaining.map Fin.val = List.range' (start + 1) remaining.length := by
      simpa [List.range'_succ] using congrArg List.tail consecutive
    have stepInvariant := columnStep_invariant matrix nextRow column (by simpa [atStart] using invariant)
    have tailInvariant := hypothesis (columnStep matrix nextRow column).1
      (columnStep matrix nextRow column).2 (start + 1) tailConsecutive
      (by simpa [atStart] using stepInvariant)
    simpa [eliminateColumns, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailInvariant

omit [DecidableEq Scalar] in
/-- Once all columns have been visited, the invariant is Mathlib's exact RREF predicate. -/
theorem Invariant.reducedRowEchelon (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (nextRow : ℕ) (invariant : Invariant matrix nextRow columns) : matrix.IsReducedRowEchelon := by
  obtain ⟨rowBound, completed, pending⟩ := invariant
  refine ⟨?_, ?_, ?_⟩
  · intro upper lower below column zeroBefore
    by_cases processed : upper.val < nextRow
    · obtain ⟨pivot, _, leading, _, _, zeroBelow⟩ := completed upper processed
      have left : column ≤ pivot := by
        by_contra notLeft
        exact leading.2 (zeroBefore pivot (lt_of_not_ge notLeft))
      exact zeroBelow lower below column left
    · exact pending lower (by omega) column column.isLt
  · intro row column leading
    have processed : row.val < nextRow := by
      by_contra notProcessed
      exact leading.2 (pending row (by omega) column column.isLt)
    obtain ⟨pivot, _, oldLeading, unit, _, _⟩ := completed row processed
    have same := leading.unique oldLeading
    simpa [same] using unit
  · intro upper lower column below leading
    have processed : lower.val < nextRow := by
      by_contra notProcessed
      exact leading.2 (pending lower (by omega) column column.isLt)
    obtain ⟨pivot, _, oldLeading, _, isolated, _⟩ := completed lower processed
    have same := leading.unique oldLeading
    simpa [same] using isolated upper (ne_of_lt below)

/-- The executable elimination returns reduced row-echelon form for every rectangular matrix. -/
theorem reducedRowEchelon (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    (eliminate matrix).IsReducedRowEchelon := by
  apply Invariant.reducedRowEchelon _ (eliminateColumns matrix 0 (List.finRange columns)).2
  have invariant := eliminateColumns_invariant matrix 0 0 (List.finRange columns)
    (by simp [List.range_eq_range']) (invariant_initial matrix)
  simpa [eliminate, List.length_finRange] using invariant

/-- Complete mathematical contract, with the invertible transformation retained as proof data. -/
theorem correct (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    (eliminate matrix).IsReducedRowEchelon ∧
      ∃ transformation : Matrix.GeneralLinearGroup (Fin rows) Scalar,
        (transformation : Matrix (Fin rows) (Fin rows) Scalar) * matrix = eliminate matrix := by
  refine ⟨reducedRowEchelon matrix, ?_⟩
  obtain ⟨transformation, equality⟩ := rowEquivalent matrix
  exact ⟨transformation, equality⟩

end Polytime2.GaussJordan
