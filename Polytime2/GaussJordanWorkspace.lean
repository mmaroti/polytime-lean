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


import Polytime2.MatrixRowField
import Polytime2.PivotSearch
import Polytime2.UnaryCopy

/-! # Shared workspace for Gauss–Jordan elimination

Row operations use their own column traversal counter. The saved pivot column,
pivot row, and row count are separate tapes, so a call preserves them without
relocating runtime data. Candidate and target rows have distinct counter tapes.
-/

namespace Polytime2.GaussJordanWorkspace

open MultiTape

variable {Scalar : Type} {rows columns : ℕ}

inductive CounterName | pivotRow | pivotColumn | rowCount
  deriving DecidableEq

instance : Fintype CounterName :=
  ⟨{.pivotRow, .pivotColumn, .rowCount}, by intro name; cases name <;> simp⟩

abbrev TapeName := Sum MatrixRows.TapeName CounterName

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .inl name => MatrixRows.Alphabet Scalar name
  | .inr _ => Binary.Symbol

instance (name : TapeName) : Inhabited (Alphabet Scalar name) :=
  match name with
  | .inl name => MatrixRows.instInhabitedAlphabet name
  | .inr _ => (⟨0⟩ : Inhabited Binary.Symbol)

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) :=
  match name with
  | .inl name => MatrixRows.instFintypeAlphabet name
  | .inr _ => inferInstanceAs (Fintype Binary.Symbol)

def frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Tapes (Alphabet Scalar)
  | .inl name => MatrixRows.frame matrix candidate target 0 sourceValue targetValue coefficient flag name
  | .inr .pivotRow => MatrixAddress.counter 0 pivotRow
  | .inr .pivotColumn => MatrixAddress.counter 0 pivotColumn
  | .inr .rowCount => MatrixAddress.counter 0 rows

/-- `true` selects candidate-to-pivot operations; `false` selects pivot-to-target operations. -/
def rowsWiring (pivotTarget : Bool) : MatrixRows.TapeName ↪ TapeName where
  toFun
    | .inl (.inl .row) => if pivotTarget then .inr .pivotRow else .inl (.inl (.inl .row))
    | .inl (.inl .width) => .inl (.inl (.inl .width))
    | .inl (.inl .column) => .inl (.inl (.inl .column))
    | .inl (.inl .output) => .inl (.inl (.inl .output))
    | .inl (.inr name) => .inl (.inl (.inr name))
    | .inr (.inl false) => if pivotTarget then .inl (.inr (.inl false)) else .inr .pivotRow
    | .inr (.inl true) => .inl (.inr (.inl true))
    | .inr (.inr name) => .inl (.inr (.inr name))
  inj' := by
    intro first second equal
    cases pivotTarget <;> fin_cases first <;> fin_cases second <;> simp_all

def rowsEquivalences (Scalar : Type) (pivotTarget : Bool) (name : MatrixRows.TapeName) :
    MatrixRows.Alphabet Scalar name ≃ Alphabet Scalar (rowsWiring pivotTarget name) := by
  cases pivotTarget <;> cases name with
  | inl name => cases name with
    | inl name => cases name <;> exact Equiv.refl _
    | inr name => cases name <;> exact Equiv.refl _
  | inr name => cases name <;> rename_i name <;> cases name <;> exact Equiv.refl _

theorem rowsBlanks (pivotTarget : Bool) (name : MatrixRows.TapeName) :
    rowsEquivalences Scalar pivotTarget name default = default := by
  cases pivotTarget <;> fin_cases name <;> rfl

noncomputable def rowOperation [Zero Scalar] (pivotTarget writeSource : Bool)
    (operation : Scalar → Scalar → Scalar → Scalar × Scalar) : Machine (Alphabet Scalar) MatrixRows.State :=
  wire (rowsWiring pivotTarget)
    (relabel (rowsEquivalences Scalar pivotTarget) (MatrixRows.machine writeSource operation))

private theorem rowFrame (pivotTarget : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∀ name, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag
      (rowsWiring pivotTarget name) =
      mapTapes (rowsEquivalences Scalar pivotTarget) (rowsBlanks pivotTarget)
        (MatrixRows.frame matrix (if pivotTarget then candidate else pivotRow)
          (if pivotTarget then pivotRow else target) 0 sourceValue targetValue coefficient flag) name := by
  intro name
  cases pivotTarget <;> fin_cases name
  all_goals first
    | change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      exact (mapTape_identity _).symm
    | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      exact (mapTape_identity _).symm

/-- Row routines preserve the saved pivot column and all unused row counters. -/
theorem row_steps [Zero Scalar] (pivotTarget writeSource : Bool)
    (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (candidate target pivotRow pivotColumn : ℕ)
    (sourceBound : (if pivotTarget then candidate else pivotRow) < rows)
    (targetBound : (if pivotTarget then pivotRow else target) < rows)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget,
      ticks ≤ (columns + 1) * (28 * rows * columns + 36 * rows + 32 * columns + 94) + 2 * columns + 5 ∧
      Steps (rowOperation pivotTarget writeSource operation) ticks
        (MatrixRows.entry, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
        (MatrixRows.exit, frame (MatrixRows.transform writeSource operation coefficient matrix
          ⟨if pivotTarget then candidate else pivotRow, sourceBound⟩
          ⟨if pivotTarget then pivotRow else target, targetBound⟩)
          candidate target pivotRow pivotColumn finalSource finalTarget coefficient false) := by
  obtain ⟨ticks, finalSource, finalTarget, cost, trace⟩ := MatrixRows.steps writeSource operation matrix
    ⟨if pivotTarget then candidate else pivotRow, sourceBound⟩
    ⟨if pivotTarget then pivotRow else target, targetBound⟩ sourceValue targetValue coefficient flag
  have mapped := trace.relabel (rowsEquivalences Scalar pivotTarget) (rowsBlanks pivotTarget)
  refine ⟨ticks, finalSource, finalTarget, cost, ?_⟩
  apply wire_steps_of_eq (rowsWiring pivotTarget) _ mapped
  · exact rowFrame pivotTarget matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag
  · exact rowFrame pivotTarget _ candidate target pivotRow pivotColumn finalSource finalTarget coefficient false
  · intro name outside
    cases pivotTarget <;> fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inl (.inl .row), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inl .width), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inl .column), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inl .output), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inr false), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inr true), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inl true), rfl⟩)
      | exact False.elim (outside ⟨.inr (.inr false), rfl⟩)

def entryWiring : MatrixEntry.TapeName ↪ TapeName where
  toFun
    | .inl .row => .inl (.inl (.inl .row))
    | .inl .width => .inl (.inl (.inl .width))
    | .inl .column => .inr .pivotColumn
    | .inl .output => .inl (.inl (.inl .output))
    | .inr name => .inl (.inl (.inr name))
  inj' := by intro first second equal; fin_cases first <;> fin_cases second <;> simp_all

def entryEquivalences (Scalar : Type) (name : MatrixEntry.TapeName) :
    MatrixEntry.Alphabet Scalar name ≃ Alphabet Scalar (entryWiring name) := by
  cases name with
  | inl name => cases name <;> exact Equiv.refl _
  | inr name => cases name <;> exact Equiv.refl _

theorem entryBlanks (name : MatrixEntry.TapeName) : entryEquivalences Scalar name default = default := by
  fin_cases name <;> rfl

noncomputable def readTarget : Machine (Alphabet Scalar) MatrixEntry.State :=
  wire entryWiring (relabel (entryEquivalences Scalar) (MatrixEntry.machine false))

private theorem entryFrame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (target : Fin rows) (pivotRow : ℕ) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∀ name, frame matrix candidate target.val pivotRow column.val sourceValue targetValue coefficient flag
      (entryWiring name) = mapTapes (entryEquivalences Scalar) entryBlanks
        (MatrixEntry.frame matrix target column 0 targetValue) name := by
  intro name
  fin_cases name
  all_goals first
    | change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      exact (mapTape_identity _).symm
    | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      exact (mapTape_identity _).symm

theorem readTarget_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (target : Fin rows) (pivotRow : ℕ) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps readTarget (7 * target.val * columns + 9 * target.val + 7 * column.val + 20)
      (MatrixEntry.entry, frame matrix candidate target.val pivotRow column.val sourceValue targetValue coefficient flag)
      (MatrixEntry.exit, frame matrix candidate target.val pivotRow column.val
        sourceValue (matrix target column) coefficient flag) := by
  have trace := (MatrixEntry.steps false matrix target column targetValue).relabel (entryEquivalences Scalar) entryBlanks
  apply wire_steps_of_eq entryWiring _ trace
  · exact entryFrame matrix candidate target pivotRow column sourceValue targetValue coefficient flag
  · exact entryFrame matrix candidate target pivotRow column sourceValue (matrix target column) coefficient flag
  · intro name outside
    fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inl .row, rfl⟩)
      | exact False.elim (outside ⟨.inl .width, rfl⟩)
      | exact False.elim (outside ⟨.inl .column, rfl⟩)
      | exact False.elim (outside ⟨.inl .output, rfl⟩)
      | exact False.elim (outside ⟨.inr false, rfl⟩)
      | exact False.elim (outside ⟨.inr true, rfl⟩)

noncomputable def loadCoefficient [Zero Scalar] (source : Bool) (table : Scalar → Scalar) :
    Machine (Alphabet Scalar) Bool := wire Function.Embedding.inl (MatrixRows.loadCoefficient source table)

theorem loadCoefficient_steps [Zero Scalar] (selected : Bool) (table : Scalar → Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (candidate target pivotRow pivotColumn : ℕ)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (loadCoefficient selected table) 1
      (false, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (true, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue
        (table (if selected then sourceValue else targetValue)) flag) := by
  apply wire_steps_of_eq Function.Embedding.inl _
    (MatrixRows.loadCoefficient_steps selected table matrix candidate target 0 sourceValue targetValue coefficient flag)
  · intro name; rfl
  · intro name; rfl
  · intro name outside
    cases name with
    | inl name => exact False.elim (outside ⟨name, rfl⟩)
    | inr name => cases name <;> rfl

noncomputable def targetCounter (reset : Bool) : Machine (Alphabet Scalar) (Fin 3) :=
  wire (oneTape (Sum.inl (Sum.inl (Sum.inl MatrixAddress.TapeName.row)) : TapeName)) (Unary.machine reset)

theorem advanceTarget_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (targetCounter false) (2 * target + 3)
      (0, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (2, frame matrix candidate (target + 1) pivotRow pivotColumn sourceValue targetValue coefficient flag) := by
  apply wire_steps_of_eq (oneTape (Sum.inl (Sum.inl (Sum.inl MatrixAddress.TapeName.row)) : TapeName)) _
    (Unary.increment_counter_steps target)
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

theorem resetTarget_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (targetCounter true) (2 * target + 3)
      (0, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (2, frame matrix candidate 0 pivotRow pivotColumn sourceValue targetValue coefficient flag) := by
  apply wire_steps_of_eq (oneTape (Sum.inl (Sum.inl (Sum.inl MatrixAddress.TapeName.row)) : TapeName)) _
    (Unary.reset_counter_steps target)
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

/-- Compare either the candidate or target against the pivot row or row count. -/
def compareWiring (candidate untilRows : Bool) : UnaryCompare.TapeName ↪ TapeName where
  toFun
    | some false => if candidate then .inl (.inr (.inl false)) else .inl (.inl (.inl .row))
    | some true => if untilRows then .inr .rowCount else .inr .pivotRow
    | none => .inl (.inr (.inl true))
  inj' := by
    intro first second equal
    cases candidate <;> cases untilRows <;> fin_cases first <;> fin_cases second <;> simp_all

def compareEquivalences (Scalar : Type) (candidate untilRows : Bool) (name : UnaryCompare.TapeName) :
    UnaryCompare.Alphabet name ≃ Alphabet Scalar (compareWiring candidate untilRows name) := by
  cases candidate <;> cases untilRows <;> cases name with
  | none => exact Equiv.refl _
  | some name => cases name <;> exact Equiv.refl _

theorem compareBlanks (candidate untilRows : Bool) (name : UnaryCompare.TapeName) :
    compareEquivalences Scalar candidate untilRows name default = default := by
  cases candidate <;> cases untilRows <;> fin_cases name <;> rfl

noncomputable def compare (candidate untilRows : Bool) : Machine (Alphabet Scalar) (Fin 3) :=
  wire (compareWiring candidate untilRows)
    (relabel (compareEquivalences Scalar candidate untilRows) UnaryCompare.machine)

def result (symbols : Symbols (Alphabet Scalar)) : Bool :=
  decide ((show Binary.Symbol from symbols (.inl (.inr (.inl true)))) = 2)

@[simp] theorem result_frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    result (read (frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)) = flag := by
  cases flag <;> simp [result, MultiTape.read, frame, MatrixRows.frame, MatrixRows.flagTape, Binary.tape, Binary.data]

theorem compare_steps (selected untilRows : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (compare selected untilRows) (2 * min (if selected then candidate else target) (if untilRows then rows else pivotRow) + 3)
      (0, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (2, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient
        (decide ((if selected then candidate else target) < (if untilRows then rows else pivotRow)))) := by
  have trace := (UnaryCompare.steps (if selected then candidate else target) (if untilRows then rows else pivotRow)
    (MatrixRows.flagTape flag)).relabel (compareEquivalences Scalar selected untilRows) (compareBlanks selected untilRows)
  apply wire_steps_of_eq (compareWiring selected untilRows) _ trace
  · intro name
    cases selected <;> cases untilRows <;> fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals exact (mapTape_identity _).symm
  · intro name
    cases selected <;> cases untilRows <;> fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals rw [mapTape_identity]
    all_goals rfl
  · intro name outside
    cases selected <;> cases untilRows <;> fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨none, rfl⟩)

theorem rowOperation_halt [Zero Scalar] (pivotTarget writeSource : Bool)
    (operation : Scalar → Scalar → Scalar → Scalar × Scalar) (symbols : Symbols (Alphabet Scalar)) :
    rowOperation pivotTarget writeSource operation MatrixRows.exit symbols = none := by rfl

theorem readTarget_halt (symbols : Symbols (Alphabet Scalar)) : readTarget MatrixEntry.exit symbols = none := by rfl

theorem loadCoefficient_halt [Zero Scalar] (selected : Bool) (table : Scalar → Scalar)
    (symbols : Symbols (Alphabet Scalar)) : loadCoefficient selected table true symbols = none := by rfl

theorem targetCounter_halt (reset : Bool) (symbols : Symbols (Alphabet Scalar)) : targetCounter reset 2 symbols = none := by rfl

theorem compare_halt (candidate untilRows : Bool) (symbols : Symbols (Alphabet Scalar)) :
    compare candidate untilRows 2 symbols = none := by rfl

def searchWiring : PivotSearch.TapeName ↪ TapeName where
  toFun
    | .inl (.inl .row) => .inl (.inr (.inl false))
    | .inl (.inl .width) => .inl (.inl (.inl .width))
    | .inl (.inl .column) => .inr .pivotColumn
    | .inl (.inl .output) => .inl (.inl (.inl .output))
    | .inl (.inr false) => .inl (.inl (.inr false))
    | .inl (.inr true) => .inl (.inr (.inr false))
    | .inr false => .inr .rowCount
    | .inr true => .inl (.inr (.inl true))
  inj' := by intro first second equal; fin_cases first <;> fin_cases second <;> simp_all

def searchEquivalences (Scalar : Type) (name : PivotSearch.TapeName) :
    PivotSearch.Alphabet Scalar name ≃ Alphabet Scalar (searchWiring name) := by
  cases name with
  | inl name => cases name with
    | inl name => cases name <;> exact Equiv.refl _
    | inr name => cases name <;> exact Equiv.refl _
  | inr name => cases name <;> exact Equiv.refl _

theorem searchBlanks (name : PivotSearch.TapeName) : searchEquivalences Scalar name default = default := by
  fin_cases name <;> rfl

noncomputable def search [Zero Scalar] [DecidableEq Scalar] : Machine (Alphabet Scalar) PivotSearch.State :=
  wire searchWiring (relabel (searchEquivalences Scalar) PivotSearch.machine)

private theorem searchFrame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow : ℕ) (column : Fin columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∀ name, frame matrix candidate target pivotRow column.val sourceValue targetValue coefficient flag (searchWiring name) =
      mapTapes (searchEquivalences Scalar) searchBlanks (PivotSearch.frame matrix candidate column sourceValue flag) name := by
  intro name
  fin_cases name
  all_goals first
    | change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      exact (mapTape_identity _).symm
    | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      exact (mapTape_identity _).symm

theorem search_steps [Zero Scalar] [DecidableEq Scalar] (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (bounded : candidate ≤ rows) (target pivotRow : ℕ) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks found finalSource,
      ticks ≤ (rows + 1) * (7 * rows * columns + 13 * rows + 7 * columns + 33) + 1 ∧
      Steps search ticks
        (PivotSearch.entry, frame matrix candidate target pivotRow column.val sourceValue targetValue coefficient flag)
        (PivotSearch.exit, frame matrix found target pivotRow column.val finalSource targetValue coefficient false) ∧
      candidate ≤ found ∧ found ≤ rows ∧
      (∀ row : Fin rows, candidate ≤ row.val → row.val < found → matrix row column = 0) ∧
      (∀ valid : found < rows, matrix ⟨found, valid⟩ column ≠ 0) ∧
      (∀ valid : found < rows, finalSource = matrix ⟨found, valid⟩ column) := by
  obtain ⟨ticks, found, finalSource, cost, trace, eligible, foundBound, skipped, nonzero, foundValue⟩ :=
    PivotSearch.steps matrix candidate bounded column sourceValue flag
  refine ⟨ticks, found, finalSource, cost, ?_, eligible, foundBound, skipped, nonzero, foundValue⟩
  have mapped := trace.relabel (searchEquivalences Scalar) searchBlanks
  apply wire_steps_of_eq searchWiring _ mapped
  · exact searchFrame matrix candidate target pivotRow column sourceValue targetValue coefficient flag
  · exact searchFrame matrix found target pivotRow column finalSource targetValue coefficient false
  · intro name outside
    fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inl (.inl .row), rfl⟩)
      | exact False.elim (outside ⟨.inl (.inr true), rfl⟩)
      | exact False.elim (outside ⟨.inr true, rfl⟩)

theorem search_halt [Zero Scalar] [DecidableEq Scalar] (symbols : Symbols (Alphabet Scalar)) :
    search PivotSearch.exit symbols = none := by rfl

def copyWiring : Bool ↪ TapeName where
  toFun
    | false => .inr .pivotRow
    | true => .inl (.inr (.inl false))
  inj' := by intro first second equal; cases first <;> cases second <;> simp_all

def copyEquivalences (Scalar : Type) (name : Bool) : Binary.Symbol ≃ Alphabet Scalar (copyWiring name) := by
  cases name <;> exact Equiv.refl _

theorem copyBlanks (name : Bool) : copyEquivalences Scalar name default = default := by cases name <;> rfl

noncomputable def copyCandidate : Machine (Alphabet Scalar) UnaryCopy.State :=
  wire copyWiring (relabel (copyEquivalences Scalar) UnaryCopy.machine)

theorem copyCandidate_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps copyCandidate (3 * pivotRow + 2 * candidate + 11)
      (UnaryCopy.entry, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (UnaryCopy.exit, frame matrix pivotRow target pivotRow pivotColumn sourceValue targetValue coefficient flag) := by
  have trace := (UnaryCopy.steps pivotRow candidate).relabel (copyEquivalences Scalar) copyBlanks
  apply wire_steps_of_eq copyWiring _ trace
  · intro name; cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals exact (mapTape_identity _).symm
  · intro name; cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals exact (mapTape_identity _).symm
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨true, rfl⟩)

theorem copyCandidate_halt (symbols : Symbols (Alphabet Scalar)) : copyCandidate UnaryCopy.exit symbols = none := by rfl

/-- Advance the saved pivot row (`false`) or column (`true`). -/
noncomputable def advancePivot (column : Bool) : Machine (Alphabet Scalar) (Fin 3) :=
  if column then wire (oneTape (Sum.inr CounterName.pivotColumn : TapeName)) (Unary.machine false)
  else wire (oneTape (Sum.inr CounterName.pivotRow : TapeName)) (Unary.machine false)

theorem advancePivot_steps (selected : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (advancePivot selected) (2 * (if selected then pivotColumn else pivotRow) + 3)
      (0, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (2, frame matrix candidate target (if selected then pivotRow else pivotRow + 1)
        (if selected then pivotColumn + 1 else pivotColumn) sourceValue targetValue coefficient flag) := by
  have trace := Unary.increment_counter_steps (if selected then pivotColumn else pivotRow)
  cases selected <;> apply wire_steps_of_eq _ _ trace
  all_goals first
    | intro name; cases name; rfl
    | intro name outside
      fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

theorem advancePivot_halt (selected : Bool) (symbols : Symbols (Alphabet Scalar)) : advancePivot selected 2 symbols = none := by
  cases selected <;> rfl

def columnWiring : UnaryCompare.TapeName ↪ TapeName where
  toFun
    | some false => .inr .pivotColumn
    | some true => .inl (.inl (.inl .width))
    | none => .inl (.inr (.inl true))
  inj' := by intro first second equal; fin_cases first <;> fin_cases second <;> simp_all

def columnEquivalences (Scalar : Type) (name : UnaryCompare.TapeName) :
    UnaryCompare.Alphabet name ≃ Alphabet Scalar (columnWiring name) := by
  cases name with
  | none => exact Equiv.refl _
  | some name => cases name <;> exact Equiv.refl _

theorem columnBlanks (name : UnaryCompare.TapeName) : columnEquivalences Scalar name default = default := by
  fin_cases name <;> rfl

noncomputable def compareColumn : Machine (Alphabet Scalar) (Fin 3) :=
  wire columnWiring (relabel (columnEquivalences Scalar) UnaryCompare.machine)

theorem compareColumn_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate target pivotRow pivotColumn : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps compareColumn (2 * min pivotColumn columns + 3)
      (0, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient flag)
      (2, frame matrix candidate target pivotRow pivotColumn sourceValue targetValue coefficient (decide (pivotColumn < columns))) := by
  have trace := (UnaryCompare.steps pivotColumn columns (MatrixRows.flagTape flag)).relabel
    (columnEquivalences Scalar) columnBlanks
  apply wire_steps_of_eq columnWiring _ trace
  · intro name; fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals exact (mapTape_identity _).symm
  · intro name; fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals rw [mapTape_identity]
    all_goals rfl
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨none, rfl⟩)

theorem compareColumn_halt (symbols : Symbols (Alphabet Scalar)) : compareColumn 2 symbols = none := by rfl

end Polytime2.GaussJordanWorkspace
