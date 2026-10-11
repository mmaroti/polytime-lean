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


import Polytime2.MatrixEntry
import Polytime2.UnaryCompare
import Polytime2.While

/-! # Runtime operations on two matrix rows

A fixed table combines corresponding source and target entries with a runtime
coefficient. Row scaling, addition, and swapping share the same traversal.
All access routines share one dense matrix and one cleared address counter.
-/

namespace Polytime2.MatrixRows

open MultiTape

variable {Scalar : Type} {rows columns : ℕ}

/-- Extra binary tapes hold the source row and guard; extra scalar tapes hold
its entry and the coefficient. The original access tapes hold the target. -/
abbrev TapeName := Sum MatrixEntry.TapeName (Sum Bool Bool)

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .inl name => MatrixEntry.Alphabet Scalar name
  | .inr (.inl _) => Binary.Symbol
  | .inr (.inr _) => TableTraversal.Symbol Scalar

instance (name : TapeName) : Inhabited (Alphabet Scalar name) :=
  match name with
  | .inl name => MatrixEntry.instInhabitedAlphabet name
  | .inr (.inl _) => (⟨0⟩ : Inhabited Binary.Symbol)
  | .inr (.inr _) => (⟨none⟩ : Inhabited (TableTraversal.Symbol Scalar))

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) := by
  cases name with
  | inl name => exact MatrixEntry.instFintypeAlphabet name
  | inr name => cases name <;> dsimp [Alphabet] <;> infer_instance

def scalarTape (value : Scalar) : Turing.Tape (TableTraversal.Symbol Scalar) :=
  Turing.Tape.mk' (Turing.ListBlank.mk [some none]) (Turing.ListBlank.mk [some (some value)])

def flagTape (flag : Bool) : Turing.Tape Binary.Symbol := Binary.tape [3] [Binary.data flag] ()

def frame (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target column : ℕ)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) : Tapes (Alphabet Scalar)
  | .inl (.inl name) => MatrixAddress.ready target columns column 0 name
  | .inl (.inr false) => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]))
  | .inl (.inr true) => scalarTape targetValue
  | .inr (.inl false) => MatrixAddress.counter 0 source
  | .inr (.inl true) => flagTape flag
  | .inr (.inr false) => scalarTape sourceValue
  | .inr (.inr true) => scalarTape coefficient

def accessWiring (source : Bool) : MatrixEntry.TapeName ↪ TapeName where
  toFun
    | .inl .row => if source then .inr (.inl false) else .inl (.inl .row)
    | .inl .width => .inl (.inl .width)
    | .inl .column => .inl (.inl .column)
    | .inl .output => .inl (.inl .output)
    | .inr false => .inl (.inr false)
    | .inr true => if source then .inr (.inr false) else .inl (.inr true)
  inj' := by
    intro first second equal
    cases source <;> fin_cases first <;> fin_cases second <;> simp_all

def accessEquivalences (Scalar : Type) (source : Bool) (name : MatrixEntry.TapeName) :
    MatrixEntry.Alphabet Scalar name ≃ Alphabet Scalar (accessWiring source name) := by
  cases name with
  | inl name => cases name <;> cases source <;> exact Equiv.refl _
  | inr name => cases name <;> cases source <;> exact Equiv.refl _

theorem accessBlanks (source : Bool) (name : MatrixEntry.TapeName) :
    accessEquivalences Scalar source name default = default := by
  cases name with
  | inl name => cases name <;> cases source <;> rfl
  | inr name => cases name <;> cases source <;> rfl

noncomputable def access (source write : Bool) : Machine (Alphabet Scalar) MatrixEntry.State :=
  wire (accessWiring source) (relabel (accessEquivalences Scalar source) (MatrixEntry.machine write))

private theorem localFrame (selected : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∀ name, frame matrix source.val target.val column.val sourceValue targetValue coefficient flag
      (accessWiring selected name) =
      mapTapes (accessEquivalences Scalar selected) (accessBlanks selected)
        (MatrixEntry.frame matrix (if selected then source else target) column 0
          (if selected then sourceValue else targetValue)) name := by
  intro name
  cases selected <;> cases name <;> rename_i name <;> cases name
  all_goals first
    | change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      exact (mapTape_identity _).symm
    | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      exact (mapTape_identity _).symm

/-- The same access controller reads either row through static tape wiring. -/
theorem access_steps (selected write : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    let row := if selected then source else target
    let value := if selected then sourceValue else targetValue
    let result := if write then value else matrix row column
    Steps (access selected write) (7 * row.val * columns + 9 * row.val + 7 * column.val + 20)
      (MatrixEntry.entry, frame matrix source.val target.val column.val sourceValue targetValue coefficient flag)
      (MatrixEntry.exit, frame (if write then MatrixAccess.update matrix row column value else matrix)
        source.val target.val column.val (if selected then result else sourceValue)
          (if selected then targetValue else result) coefficient flag) := by
  dsimp only
  have trace := (MatrixEntry.steps write matrix (if selected then source else target) column
    (if selected then sourceValue else targetValue)).relabel (accessEquivalences Scalar selected) (accessBlanks selected)
  apply wire_steps_of_eq (accessWiring selected) _ trace
  · exact localFrame selected matrix source target column sourceValue targetValue coefficient flag
  · intro name
    cases selected <;> cases write <;> cases name <;> rename_i name <;> cases name
    all_goals first
      | change (_ : Turing.Tape Binary.Symbol) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
        exact (mapTape_identity _).symm
      | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
          Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
        exact (mapTape_identity _).symm
  · intro name outside
    cases selected <;> fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.inl .row, rfl⟩)
      | exact False.elim (outside ⟨.inl .width, rfl⟩)
      | exact False.elim (outside ⟨.inl .column, rfl⟩)
      | exact False.elim (outside ⟨.inl .output, rfl⟩)
      | exact False.elim (outside ⟨.inr false, rfl⟩)
      | exact False.elim (outside ⟨.inr true, rfl⟩)

section Combination

variable [Zero Scalar]

/-- A fixed specialization table reads three runtime scalars under stationary heads. -/
def combine (operation : Scalar → Scalar → Scalar → Scalar × Scalar) : Machine (Alphabet Scalar) Bool :=
  HeadTable.machine (fun symbols name =>
    let coefficient := (symbols (.inr (.inr true))).join.getD 0
    let source := (symbols (.inr (.inr false))).join.getD 0
    let target := (symbols (.inl (.inr true))).join.getD 0
    let output := operation coefficient source target
    match name with
    | .inl (.inl field) => symbols (.inl (.inl field))
    | .inl (.inr false) => symbols (.inl (.inr false))
    | .inl (.inr true) => some (some output.2)
    | .inr (.inl field) => symbols (.inr (.inl field))
    | .inr (.inr false) => some (some output.1)
    | .inr (.inr true) => symbols (.inr (.inr true)))

private theorem combine_steps (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target column : ℕ)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (combine operation) 1
      (false, frame matrix source target column sourceValue targetValue coefficient flag)
      (true, frame matrix source target column (operation coefficient sourceValue targetValue).1
        (operation coefficient sourceValue targetValue).2 coefficient flag) := by
  refine .next ?_ (.zero _)
  simp only [step, combine, HeadTable.machine, Bool.false_eq_true, ite_false, Option.map_some]
  apply congrArg some
  apply Prod.ext
  · rfl
  funext name
  fin_cases name
  all_goals first
    | change (scalarTape sourceValue).write (some (some (operation coefficient sourceValue targetValue).1)) =
        scalarTape (operation coefficient sourceValue targetValue).1
      simp only [scalarTape, Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
        List.tail_cons, Turing.ListBlank.cons_mk]
    | change (scalarTape targetValue).write (some (some (operation coefficient sourceValue targetValue).2)) =
        scalarTape (operation coefficient sourceValue targetValue).2
      simp only [scalarTape, Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
        List.tail_cons, Turing.ListBlank.cons_mk]
    | exact Turing.Tape.write_self _

/-- Copy a scalar through a fixed unary table into the runtime coefficient slot. -/
def loadCoefficient (source : Bool) (table : Scalar → Scalar) : Machine (Alphabet Scalar) Bool :=
  HeadTable.machine (fun symbols name => match name with
    | .inr (.inr true) => some (some (table
        ((if source then symbols (.inr (.inr false)) else symbols (.inl (.inr true))).join.getD 0)))
    | .inl field => symbols (.inl field)
    | .inr (.inl field) => symbols (.inr (.inl field))
    | .inr (.inr false) => symbols (.inr (.inr false)))

theorem loadCoefficient_steps (selected : Bool) (table : Scalar → Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target column : ℕ)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (loadCoefficient selected table) 1
      (false, frame matrix source target column sourceValue targetValue coefficient flag)
      (true, frame matrix source target column sourceValue targetValue
        (table (if selected then sourceValue else targetValue)) flag) := by
  refine .next ?_ (.zero _)
  simp only [step, loadCoefficient, HeadTable.machine, Bool.false_eq_true, ite_false, Option.map_some]
  apply congrArg some
  apply Prod.ext
  · rfl
  funext name
  cases selected <;> fin_cases name
  all_goals first
    | change (scalarTape coefficient).write (some (some (table sourceValue))) = scalarTape (table sourceValue)
      simp only [scalarTape, Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
        List.tail_cons, Turing.ListBlank.cons_mk]
    | change (scalarTape coefficient).write (some (some (table targetValue))) = scalarTape (table targetValue)
      simp only [scalarTape, Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
        List.tail_cons, Turing.ListBlank.cons_mk]
    | exact Turing.Tape.write_self _

def entryUpdate (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) : Matrix (Fin rows) (Fin columns) Scalar :=
  let output := operation coefficient (matrix source column) (matrix target column)
  MatrixAccess.update (if writeSource then MatrixAccess.update matrix source column output.1 else matrix)
    target column output.2

omit [Zero Scalar] in
theorem entryUpdate_apply (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target row : Fin rows) (column position : Fin columns) :
    entryUpdate writeSource operation coefficient matrix source target column row position =
      if row = target ∧ position = column then (operation coefficient (matrix source column) (matrix target column)).2
      else if writeSource = true ∧ row = source ∧ position = column then
        (operation coefficient (matrix source column) (matrix target column)).1 else matrix row position := by
  cases writeSource <;> by_cases isTarget : row = target <;> by_cases isSource : row = source <;>
    by_cases same : position = column <;>
      simp_all [entryUpdate, MatrixAccess.update, Function.update]

abbrev EntryState := Sum (Sum (Sum (Sum MatrixEntry.State MatrixEntry.State) Bool) MatrixEntry.State) MatrixEntry.State

noncomputable def entryMachine (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    Machine (Alphabet Scalar) EntryState :=
  sequence (sequence (sequence (sequence (access true false) (access false false) MatrixEntry.entry)
    (combine operation) false) (access true writeSource) MatrixEntry.entry) (access false true) MatrixEntry.entry

def entryEntry : EntryState := .inl (.inl (.inl (.inl MatrixEntry.entry)))
def entryExit : EntryState := .inr MatrixEntry.exit

omit [Zero Scalar] in
private theorem access_halt (selected write : Bool) (symbols : Symbols (Alphabet Scalar)) :
    access selected write MatrixEntry.exit symbols = none := by
  simp [access, wire, relabel, MatrixEntry.machine, MatrixEntry.exit, MultiTape.sequence,
    MatrixEntry.clearAddress, Unary.machine]

/-- One pair of entries is transformed without changing any index or coefficient. -/
theorem entry_steps (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    let output := operation coefficient (matrix source column) (matrix target column)
    Steps (entryMachine writeSource operation)
      (14 * (source.val + target.val) * columns + 18 * (source.val + target.val) + 28 * column.val + 85)
      (entryEntry, frame matrix source.val target.val column.val sourceValue targetValue coefficient flag)
      (entryExit, frame (entryUpdate writeSource operation coefficient matrix source target column)
        source.val target.val column.val (if writeSource then output.1 else matrix source column)
          output.2 coefficient flag) := by
  dsimp only
  have sourceRead := access_steps true false matrix source target column sourceValue targetValue coefficient flag
  have targetRead := access_steps false false matrix source target column (matrix source column) targetValue coefficient flag
  have combined := combine_steps operation matrix source.val target.val column.val
    (matrix source column) (matrix target column) coefficient flag
  let output := operation coefficient (matrix source column) (matrix target column)
  have sourceWrite := access_steps true writeSource matrix source target column output.1 output.2 coefficient flag
  have targetWrite := access_steps false true
    (if writeSource then MatrixAccess.update matrix source column output.1 else matrix)
    source target column (if writeSource then output.1 else matrix source column) output.2 coefficient flag
  simp only [Bool.false_eq_true, ite_true, ite_false] at sourceRead targetRead sourceWrite targetWrite
  have first := sequence_steps _ _ MatrixEntry.entry sourceRead (access_halt true false) targetRead
  have second := sequence_steps _ _ false first
    (by intro symbols; simp [MultiTape.sequence, access_halt]) combined
  have third := sequence_steps _ _ MatrixEntry.entry second
    (by intro symbols; simp [MultiTape.sequence, combine, HeadTable.machine]) sourceWrite
  have complete := sequence_steps _ _ MatrixEntry.entry third
    (by intro symbols; simp [MultiTape.sequence, access_halt]) targetWrite
  convert complete using 1 <;> first | rfl | ring

end Combination

def compareWiring : UnaryCompare.TapeName ↪ TapeName where
  toFun
    | some false => .inl (.inl .column)
    | some true => .inl (.inl .width)
    | none => .inr (.inl true)
  inj' := by intro first second equal; fin_cases first <;> fin_cases second <;> simp_all

def compareEquivalences (Scalar : Type) (name : UnaryCompare.TapeName) :
    UnaryCompare.Alphabet name ≃ Alphabet Scalar (compareWiring name) := by
  cases name with
  | none => exact Equiv.refl _
  | some name => cases name <;> exact Equiv.refl _

theorem compareBlanks (name : UnaryCompare.TapeName) : compareEquivalences Scalar name default = default := by
  fin_cases name <;> rfl

noncomputable def compare : Machine (Alphabet Scalar) (Fin 3) :=
  wire compareWiring (relabel (compareEquivalences Scalar) UnaryCompare.machine)

def result (symbols : Symbols (Alphabet Scalar)) : Bool :=
  decide ((show Binary.Symbol from symbols (.inr (.inl true))) = 2)

@[simp] theorem result_frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target column : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    result (read (frame matrix source target column sourceValue targetValue coefficient flag)) = flag := by
  cases flag <;> simp [result, MultiTape.read, frame, flagTape, Binary.tape, Binary.data]

private theorem compare_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target column : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps compare (2 * min column columns + 3)
      (0, frame matrix source target column sourceValue targetValue coefficient flag)
      (2, frame matrix source target column sourceValue targetValue coefficient (decide (column < columns))) := by
  have trace := (UnaryCompare.steps column columns (flagTape flag)).relabel (compareEquivalences Scalar) compareBlanks
  apply wire_steps_of_eq compareWiring _ trace
  · intro name
    fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals exact (mapTape_identity _).symm
  · intro name
    fin_cases name
    all_goals change (_ : Turing.Tape Binary.Symbol) =
      Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
    all_goals rw [mapTape_identity]
    all_goals rfl
  · intro name outside
    fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨some false, rfl⟩)
      | exact False.elim (outside ⟨some true, rfl⟩)
      | exact False.elim (outside ⟨none, rfl⟩)

noncomputable def counterMachine (reset : Bool) : Machine (Alphabet Scalar) (Fin 3) :=
  wire (oneTape (Sum.inl (Sum.inl MatrixAddress.TapeName.column) : TapeName)) (Unary.machine reset)

private theorem advance_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target column : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (counterMachine false) (2 * column + 3)
      (0, frame matrix source target column sourceValue targetValue coefficient flag)
      (2, frame matrix source target (column + 1) sourceValue targetValue coefficient flag) := by
  have blank : Turing.ListBlank.mk (List.replicate (column + 1) (2 : Binary.Symbol) ++ [0]) =
      Turing.ListBlank.mk (List.replicate (column + 1) (2 : Binary.Symbol)) :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  apply wire_steps_of_eq (oneTape (Sum.inl (Sum.inl MatrixAddress.TapeName.column) : TapeName)) _
    (Unary.increment_steps column [] [])
  · intro name; cases name; rfl
  · intro name; cases name
    change Turing.Tape.mk' _ (Turing.ListBlank.mk (List.replicate (column + 1) 2 ++ [0])) = _
    rw [blank]
    simp [Binary.tape]
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

private theorem reset_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target column : ℕ) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    Steps (counterMachine true) (2 * column + 3)
      (0, frame matrix source target column sourceValue targetValue coefficient flag)
      (2, frame matrix source target 0 sourceValue targetValue coefficient flag) := by
  have blank : Turing.ListBlank.mk (List.replicate column (0 : Binary.Symbol) ++ [0]) = Turing.ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨column + 1, by simp [List.replicate_succ']⟩)
  apply wire_steps_of_eq (oneTape (Sum.inl (Sum.inl MatrixAddress.TapeName.column) : TapeName)) _
    (Unary.reset_steps column [] [])
  · intro name; cases name; rfl
  · intro name; cases name
    change Turing.Tape.mk' _ (Turing.ListBlank.mk [0]) =
      Turing.Tape.mk' _ (Turing.ListBlank.mk (List.replicate column 0 ++ [0]))
    rw [blank]
    congr 1
    exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

section Traversal

variable [Zero Scalar]

/-- Apply the entry table independently to every column of the two rows. -/
def transform (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  entryUpdate writeSource operation coefficient matrix source target column row column

private def processedMatrix (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (processed : ℕ) : Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  if column.val < processed then transform writeSource operation coefficient matrix source target row column
  else matrix row column

omit [Zero Scalar] in
private theorem partial_zero (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    processedMatrix writeSource operation coefficient matrix source target 0 = matrix := by
  ext row column
  simp [processedMatrix]

omit [Zero Scalar] in
private theorem partial_complete (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    processedMatrix writeSource operation coefficient matrix source target columns =
      transform writeSource operation coefficient matrix source target := by
  ext row column
  simp [processedMatrix, column.isLt]

omit [Zero Scalar] in
private theorem partial_next (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) :
    entryUpdate writeSource operation coefficient
      (processedMatrix writeSource operation coefficient matrix source target column.val) source target column =
      processedMatrix writeSource operation coefficient matrix source target (column.val + 1) := by
  ext row position
  by_cases same : position = column
  · subst position
    simp [entryUpdate_apply, processedMatrix, transform]
  · have unequal : position.val ≠ column.val := by intro equal; exact same (Fin.ext equal)
    have before : position.val < column.val + 1 ↔ position.val < column.val := by omega
    simp [entryUpdate_apply, processedMatrix, same, before]

abbrev BodyState := Sum EntryState (Fin 3)

noncomputable def body (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    Machine (Alphabet Scalar) BodyState := sequence (entryMachine writeSource operation) (counterMachine false) 0

def bodyEntry : BodyState := .inl entryEntry
def bodyExit : BodyState := .inr 2

abbrev LoopState := Sum (Sum (Fin 3) BodyState) Unit

noncomputable def loop (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    Machine (Alphabet Scalar) LoopState := withExit (whileMachine compare (body writeSource operation) 0 bodyEntry result)

abbrev State := Sum LoopState (Fin 3)

-- Reuse the finite enumeration when several row programs share a controller shape.
instance statesFinite : Fintype State := inferInstance

noncomputable def machine (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    Machine (Alphabet Scalar) State := sequence (loop writeSource operation) (counterMachine true) 0

def entry : State := .inl (.inl (.inl 0))
def exit : State := .inr 2

omit [Zero Scalar] in
private theorem compare_halt (symbols : Symbols (Alphabet Scalar)) : compare 2 symbols = none := by
  simp [compare, wire, relabel, UnaryCompare.machine]

omit [Zero Scalar] in
private theorem counter_halt (reset : Bool) (symbols : Symbols (Alphabet Scalar)) : counterMachine reset 2 symbols = none := by
  simp [counterMachine, wire, Unary.machine]

private theorem body_halt (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (symbols : Symbols (Alphabet Scalar)) : body writeSource operation bodyExit symbols = none := by
  simp [body, bodyExit, MultiTape.sequence, counter_halt]

private theorem body_steps (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    let output := operation coefficient (matrix source column) (matrix target column)
    Steps (body writeSource operation)
      (14 * (source.val + target.val) * columns + 18 * (source.val + target.val) + 30 * column.val + 89)
      (bodyEntry, frame matrix source.val target.val column.val sourceValue targetValue coefficient flag)
      (bodyExit, frame (entryUpdate writeSource operation coefficient matrix source target column)
        source.val target.val (column.val + 1) (if writeSource then output.1 else matrix source column)
          output.2 coefficient flag) := by
  dsimp only
  have trace := sequence_steps _ _ 0
    (entry_steps writeSource operation matrix source target column sourceValue targetValue coefficient flag)
    (by intro symbols; simp [entryMachine, entryExit, MultiTape.sequence, access_halt])
    (advance_steps (entryUpdate writeSource operation coefficient matrix source target column)
      source.val target.val column.val
      (if writeSource then (operation coefficient (matrix source column) (matrix target column)).1 else matrix source column)
      (operation coefficient (matrix source column) (matrix target column)).2 coefficient flag)
  convert trace using 1 <;> first | rfl | ring

private theorem traverse_steps (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows)
    (start : ℕ) (bounded : start ≤ columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget,
      ticks ≤ (columns - start + 1) * (28 * rows * columns + 36 * rows + 32 * columns + 94) ∧
      Steps (whileMachine compare (body writeSource operation) 0 bodyEntry result) ticks
        (.inl 0, frame (processedMatrix writeSource operation coefficient matrix source target start)
          source.val target.val start sourceValue targetValue coefficient flag)
        (.inl 2, frame (transform writeSource operation coefficient matrix source target)
          source.val target.val columns finalSource finalTarget coefficient false) := by
  generalize ranking : columns - start = remaining
  induction remaining using Nat.strong_induction_on generalizing start sourceValue targetValue flag with
  | h remaining hypothesis =>
    have comparison := compare_steps (processedMatrix writeSource operation coefficient matrix source target start)
      source.val target.val start sourceValue targetValue coefficient flag
    have liftedGuard := comparison.rename Sum.inl
      (target := whileMachine compare (body writeSource operation) 0 bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    by_cases valid : start < columns
    · simp only [valid, decide_true] at liftedGuard
      let column : Fin columns := ⟨start, valid⟩
      let current := processedMatrix writeSource operation coefficient matrix source target start
      let output := operation coefficient (current source column) (current target column)
      let nextSource := if writeSource then output.1 else current source column
      have advanced := body_steps writeSource operation current source target column sourceValue targetValue coefficient true
      have nextMatrix := partial_next writeSource operation coefficient matrix source target column
      change entryUpdate writeSource operation coefficient current source target column =
        processedMatrix writeSource operation coefficient matrix source target (start + 1) at nextMatrix
      rw [nextMatrix] at advanced
      have liftedBody := advanced.rename Sum.inr
        (target := whileMachine compare (body writeSource operation) 0 bodyEntry result)
        (by intro state symbols next actions transition; simp [whileMachine, transition])
      obtain ⟨restTicks, finalSource, finalTarget, restCost, restTrace⟩ :=
        hypothesis (columns - (start + 1)) (by omega) (start + 1) (by omega) nextSource output.2 true rfl
      have toBody : step (whileMachine compare (body writeSource operation) 0 bodyEntry result)
          (.inl 2, frame current source.val target.val start sourceValue targetValue coefficient true) =
          some (.inr bodyEntry, frame current source.val target.val start sourceValue targetValue coefficient true) := by
        simp [step, whileMachine, compare_halt]
      have toGuard : step (whileMachine compare (body writeSource operation) 0 bodyEntry result)
          (.inr bodyExit, frame (processedMatrix writeSource operation coefficient matrix source target (start + 1))
            source.val target.val (start + 1) nextSource output.2 coefficient true) =
          some (.inl 0, frame (processedMatrix writeSource operation coefficient matrix source target (start + 1))
            source.val target.val (start + 1) nextSource output.2 coefficient true) := by
        simp [step, whileMachine, body_halt]
      have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      refine ⟨_, finalSource, finalTarget, ?_, trace⟩
      have sourceBound := source.isLt
      have targetBound := target.isLt
      have sumBound : source.val + target.val ≤ 2 * rows := by omega
      have product := Nat.mul_le_mul_right columns sumBound
      have minimum := Nat.min_le_right start columns
      have stepCost : (2 * min start columns + 3) +
          (14 * (source.val + target.val) * columns + 18 * (source.val + target.val) + 30 * column.val + 89) + 2 ≤
          28 * rows * columns + 36 * rows + 32 * columns + 94 := by
        dsimp [column]
        nlinarith
      have split : columns - start + 1 = (columns - (start + 1) + 1) + 1 := by omega
      rw [← ranking, split, Nat.add_mul, one_mul]
      omega
    · have finalIndex : start = columns := by omega
      subst start
      simp only [lt_self_iff_false, decide_false, partial_complete] at liftedGuard
      rw [partial_complete]
      refine ⟨2 * min columns columns + 3, sourceValue, targetValue, ?_, liftedGuard⟩
      have dominates := Nat.mul_le_mul_right (28 * rows * columns + 36 * rows + 32 * columns + 94)
        (show 1 ≤ remaining + 1 by omega)
      simp only [one_mul, min_self] at dominates ⊢
      omega

/-- A complete row operation resets its traversal counter and Boolean guard. -/
theorem steps (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget,
      ticks ≤ (columns + 1) * (28 * rows * columns + 36 * rows + 32 * columns + 94) + 2 * columns + 5 ∧
      Steps (machine writeSource operation) ticks
        (entry, frame matrix source.val target.val 0 sourceValue targetValue coefficient flag)
        (exit, frame (transform writeSource operation coefficient matrix source target)
          source.val target.val 0 finalSource finalTarget coefficient false) := by
  obtain ⟨ticks, finalSource, finalTarget, cost, trace⟩ :=
    traverse_steps writeSource operation matrix source target 0 (by omega) sourceValue targetValue coefficient flag
  simp only [partial_zero, Nat.sub_zero] at trace cost
  have halted : step (whileMachine compare (body writeSource operation) 0 bodyEntry result)
      (.inl 2, frame (transform writeSource operation coefficient matrix source target)
        source.val target.val columns finalSource finalTarget coefficient false) = none := by
    simp [step, whileMachine, compare_halt]
  have loopTrace := withExit_steps _ trace halted
  have complete := sequence_steps _ _ 0 loopTrace (by intro symbols; rfl)
    (reset_steps (transform writeSource operation coefficient matrix source target)
      source.val target.val columns finalSource finalTarget coefficient false)
  refine ⟨ticks + 1 + (2 * columns + 3) + 1, finalSource, finalTarget, by omega, complete⟩

/-- Runtime coefficients and dimensions vary; the table and finite controller stay fixed. -/
theorem realizes [Fintype Scalar] (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    Realizes (machine writeSource operation) entry exit
      (fun assignment initial =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (source target : Fin (assignment false)) (sourceValue targetValue coefficient : Scalar) (flag : Bool),
          initial = frame matrix source.val target.val 0 sourceValue targetValue coefficient flag)
      (fun assignment initial final =>
        ∀ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (source target : Fin (assignment false)) (sourceValue targetValue coefficient : Scalar) (flag : Bool),
          initial = frame matrix source.val target.val 0 sourceValue targetValue coefficient flag →
          ∃ finalSource finalTarget,
            final = frame (transform writeSource operation coefficient matrix source target)
              source.val target.val 0 finalSource finalTarget coefficient false) := by
  refine ⟨by intro symbols; simp [machine, exit, MultiTape.sequence, counter_halt],
    (MvPolynomial.X true + 1) *
      (28 * MvPolynomial.X false * MvPolynomial.X true + 36 * MvPolynomial.X false +
        32 * MvPolynomial.X true + 94) + 2 * MvPolynomial.X true + 5, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, source, target, sourceValue, targetValue, coefficient, flag, rfl⟩ := valid
  obtain ⟨ticks, finalSource, finalTarget, cost, trace⟩ :=
    steps writeSource operation matrix source target sourceValue targetValue coefficient flag
  refine ⟨ticks, _, ?_, trace, ?_⟩
  · simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using cost
  · intro otherMatrix otherSource otherTarget otherSourceValue otherTargetValue otherCoefficient otherFlag equal
    obtain ⟨otherTicks, otherFinalSource, otherFinalTarget, _, otherTrace⟩ :=
      steps writeSource operation otherMatrix otherSource otherTarget otherSourceValue otherTargetValue otherCoefficient otherFlag
    rw [← equal] at otherTrace
    exact ⟨otherFinalSource, otherFinalTarget, congrArg Prod.snd
      (trace.final_eq otherTrace (by simp [step, machine, exit, MultiTape.sequence, counter_halt])
        (by simp [step, machine, exit, MultiTape.sequence, counter_halt]))⟩

end Traversal

end Polytime2.MatrixRows
