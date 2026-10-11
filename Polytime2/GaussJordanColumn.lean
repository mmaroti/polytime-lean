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


import Polytime2.GaussJordanPivot

/-! # A complete runtime Gauss–Jordan column step

Initialize the candidate from the pivot row, search with a checked sentinel,
and branch to the swap-normalize-clear program only when a pivot exists.
-/

namespace Polytime2.GaussJordanColumn

open MultiTape GaussJordanWorkspace

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {rows columns : ℕ}

abbrev PrepareState := Sum UnaryCopy.State PivotSearch.State
abbrev FoundState := Sum GaussJordanPivot.State (Fin 3)

noncomputable def prepare : Machine (Alphabet Scalar) PrepareState :=
  sequence copyCandidate search PivotSearch.entry

noncomputable def found : Machine (Alphabet Scalar) FoundState :=
  sequence GaussJordanPivot.machine (advancePivot false) 0

def idle : Machine (Alphabet Scalar) Unit := fun _ _ => none

abbrev SelectState := Sum (Sum Unit (Sum FoundState Unit)) Unit

noncomputable def select : Machine (Alphabet Scalar) SelectState :=
  withExit (branchMachine result found idle (.inl GaussJordanPivot.entry) ())

abbrev State := Sum (Sum PrepareState (Fin 3)) SelectState

instance statesFinite : Fintype State := inferInstance

noncomputable def machine : Machine (Alphabet Scalar) State :=
  sequence (sequence prepare (compare true true) 0) select (.inl (.inl ()))

def entry : State := .inl (.inl (.inl UnaryCopy.entry))
def exit : State := .inr (.inr ())

def bound (rows columns : ℕ) : ℕ :=
  (rows + 1) * (7 * rows * columns + 13 * rows + 7 * columns + 33) + 1 +
    GaussJordanPivot.bound rows columns + 9 * rows + 23

/-- No pivot, including a row-count sentinel, leaves the mathematical state unchanged. -/
theorem steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate pivotRow : ℕ) (candidateBound : candidate ≤ rows) (pivotBound : pivotRow ≤ rows)
    (column : Fin columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalCandidate finalSource finalTarget finalCoefficient,
      ticks ≤ bound rows columns ∧
      Steps machine ticks
        (entry, frame matrix candidate 0 pivotRow column.val sourceValue targetValue coefficient flag)
        (exit, frame (GaussJordan.columnStep matrix pivotRow column).1 finalCandidate 0
          (GaussJordan.columnStep matrix pivotRow column).2 column.val finalSource finalTarget finalCoefficient false) ∧
      finalCandidate ≤ rows := by
  have copied := copyCandidate_steps matrix candidate 0 pivotRow column.val sourceValue targetValue coefficient flag
  obtain ⟨searchTicks, selected, selectedValue, searchCost, searched, eligible, selectedBound, skipped, nonzero, foundValue⟩ :=
    search_steps matrix pivotRow pivotBound 0 pivotRow column sourceValue targetValue coefficient flag
  have prepared := sequence_steps _ _ PivotSearch.entry copied copyCandidate_halt searched
  have compared := compare_steps true true matrix selected 0 pivotRow column.val selectedValue targetValue coefficient false
  simp only [ite_true] at compared
  have checked := sequence_steps _ _ 0 prepared (by intro symbols; simp [MultiTape.sequence, search_halt]) compared
  have mathematical := GaussJordan.findPivot_eq_of_minimal matrix pivotRow selected column
    eligible selectedBound skipped nonzero
  by_cases active : selected < rows
  · have pivotValid : pivotRow < rows := by omega
    have scalar := foundValue active
    rw [scalar] at checked
    simp only [active, decide_true] at checked
    obtain ⟨pivotTicks, finalSource, finalTarget, finalCoefficient, pivotCost, pivotTrace⟩ :=
      GaussJordanPivot.steps matrix ⟨selected, active⟩ ⟨pivotRow, pivotValid⟩ column targetValue coefficient true
    have advanced := advancePivot_steps false (MatrixOperations.pivotStep matrix ⟨pivotRow, pivotValid⟩ ⟨selected, active⟩ column)
      selected 0 pivotRow column.val finalSource finalTarget finalCoefficient false
    simp only [Bool.false_eq_true, ite_false] at advanced
    have foundTrace := sequence_steps _ _ 0 pivotTrace (by intro symbols; rfl) advanced
    have selectedTrace := branch_steps_true result found idle (.inl GaussJordanPivot.entry) ()
      (by simp) foundTrace (by intro symbols; simp [found, MultiTape.sequence, advancePivot_halt])
    have complete := sequence_steps _ select (.inl (.inl ())) checked
      (by intro symbols; simp [MultiTape.sequence, compare_halt]) selectedTrace
    have value : GaussJordan.columnStep matrix pivotRow column =
        (MatrixOperations.pivotStep matrix ⟨pivotRow, pivotValid⟩ ⟨selected, active⟩ column, pivotRow + 1) := by
      simp [GaussJordan.columnStep, pivotValid, mathematical, active]
    refine ⟨_, selected, finalSource, finalTarget, finalCoefficient, ?_, by
      simpa only [machine, entry, exit, select, prepare, found, value] using complete, selectedBound⟩
    have minimum := Nat.min_le_right selected rows
    dsimp [bound]
    omega
  · simp only [active, decide_false] at checked
    have missing : GaussJordan.findPivot matrix pivotRow column = none := by simpa [active] using mathematical
    have value : GaussJordan.columnStep matrix pivotRow column = (matrix, pivotRow) := by
      by_cases valid : pivotRow < rows <;> simp [GaussJordan.columnStep, valid, missing]
    have selectedTrace := branch_steps_false result found idle (.inl GaussJordanPivot.entry) ()
      (initial := frame matrix selected 0 pivotRow column.val selectedValue targetValue coefficient false)
      (by simp) (Steps.zero ((), frame matrix selected 0 pivotRow column.val selectedValue targetValue coefficient false))
      (by intro symbols; rfl)
    have complete := sequence_steps _ select (.inl (.inl ())) checked
      (by intro symbols; simp [MultiTape.sequence, compare_halt]) selectedTrace
    refine ⟨_, selected, selectedValue, targetValue, coefficient, ?_, by
      simpa only [machine, entry, exit, select, prepare, value] using complete, selectedBound⟩
    have minimum := Nat.min_le_right selected rows
    dsimp [bound]
    omega

theorem halt (symbols : Symbols (Alphabet Scalar)) : machine exit symbols = none := by rfl

end Polytime2.GaussJordanColumn
