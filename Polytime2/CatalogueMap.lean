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

import Polytime2.Contracts
import Polytime2.ScalarAccess
import Polytime2.HeadTable
import Polytime2.Unary
import Polytime2.Alphabet

/-! # Two active catalogue maps on shared storage

The catalogue maps are fixed specialization tables. Active count and both
selected coordinates are runtime data. Two calls share the array and scalar
scratch, restore all heads, and preserve inactive entries without inspecting
or initializing them. Equal selected indices have sequential semantics.
-/

namespace Polytime2.CatalogueMap

open MultiTape

variable {Scalar : Type}

inductive TapeName | firstIndex | secondIndex | active | array | element
  deriving DecidableEq

instance : Fintype TapeName :=
  ⟨{.firstIndex, .secondIndex, .active, .array, .element}, by intro name; cases name <;> simp⟩

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .firstIndex | .secondIndex | .active => Binary.Symbol
  | .array | .element => TableTraversal.Symbol Scalar

instance (name : TapeName) : Inhabited (Alphabet Scalar name) := by
  cases name <;> infer_instance

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) := by
  cases name <;> infer_instance

def localFrame (values : List Scalar) (index : ℕ) (scratch : Scalar) :
    Tapes (ScalarAccess.Alphabet Scalar) :=
  ScalarAccess.frame [3] (List.replicate index 2 ++ [0]) [some none]
    (TableTraversal.word values ++ [none])
    (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk [some (some scratch)]))

def table (operation : Scalar → Scalar) : Symbols (ScalarAccess.Alphabet Scalar) →
    Symbols (ScalarAccess.Alphabet Scalar) := fun symbols name =>
  match name with
  | .index => symbols .index
  | .array => symbols .array
  | .element => (symbols .element).map (Option.map operation)

abbrev LocalState := Sum (Sum (Fin 3) Bool) (Fin 3)
def localEntry : LocalState := .inl (.inl 0)
def localExit : LocalState := .inr 2

def localMachine (operation : Scalar → Scalar) : Machine (ScalarAccess.Alphabet Scalar) LocalState :=
  sequence (sequence (ScalarAccess.machine false) (HeadTable.machine (table operation)) false)
    (ScalarAccess.machine true) 0

private theorem local_halt (operation : Scalar → Scalar) (symbols : Symbols (ScalarAccess.Alphabet Scalar)) :
    localMachine operation localExit symbols = none := by rfl

private theorem table_steps (operation : Scalar → Scalar) (values : List Scalar) (index : ℕ) (scratch : Scalar) :
    Steps (HeadTable.machine (table operation)) 1
      (false, localFrame values index scratch) (true, localFrame values index (operation scratch)) := by
  have trace := HeadTable.steps (table operation) (localFrame values index scratch)
  convert trace using 1
  congr 1
  funext name
  cases name with
  | index => exact (Turing.Tape.write_self _).symm
  | array => exact (Turing.Tape.write_self _).symm
  | element => simp [table, localFrame, ScalarAccess.frame, MultiTape.read,
      Turing.Tape.write_mk', Turing.ListBlank.cons_mk]

/-- Read, apply a fixed table, and update, preserving the index and all heads. -/
theorem local_steps (operation : Scalar → Scalar) (values : List Scalar)
    (index : Fin values.length) (scratch : Scalar) :
    Steps (localMachine operation) (4 * index.val + 9)
      (localEntry, localFrame values index.val scratch)
      (localExit, localFrame (values.modify index.val operation) index.val (operation values[index.val])) := by
  have read := ScalarAccess.lookup_steps values index scratch [] [] [some none] [none] [] []
  have applied := table_steps operation values index.val values[index.val]
  have written := ScalarAccess.update_steps values index (operation values[index.val]) [] [] [some none] [none] [] []
  have first := sequence_steps _ _ false read (by intro symbols; rfl) applied
  have complete := sequence_steps _ _ 0 first (by intro symbols; rfl) written
  convert complete using 1 <;> first
    | rfl
    | omega
    | simp [localExit, localFrame,
        List.modify_eq_set_get operation index.isLt]

def frame (active firstIndex secondIndex : ℕ) (values : List Scalar) (scratch : Scalar) : Tapes (Alphabet Scalar)
  | .firstIndex => Binary.tape [3] (List.replicate firstIndex 2 ++ [0]) ()
  | .secondIndex => Binary.tape [3] (List.replicate secondIndex 2 ++ [0]) ()
  | .active => Binary.tape [3] (List.replicate active 2 ++ [0]) ()
  | .array => localFrame values 0 scratch .array
  | .element => localFrame values 0 scratch .element

def wiring (first : Bool) : ScalarAccess.TapeName ↪ TapeName where
  toFun
    | .index => if first then .firstIndex else .secondIndex
    | .array => .array
    | .element => .element
  inj' := by intro left right equal; cases first <;> cases left <;> cases right <;> simp_all

def equivalences (Scalar : Type) (first : Bool) (name : ScalarAccess.TapeName) :
    ScalarAccess.Alphabet Scalar name ≃ Alphabet Scalar (wiring first name) := by
  cases first <;> cases name <;> exact Equiv.refl _

private theorem blanks (first : Bool) (name : ScalarAccess.TapeName) :
    equivalences Scalar first name default = default := by cases first <;> cases name <;> rfl

noncomputable def mapAt (first : Bool) (operation : Scalar → Scalar) : Machine (Alphabet Scalar) LocalState :=
  wire (wiring first) (relabel (equivalences Scalar first) (localMachine operation))

private theorem frame_at (first : Bool) (active firstIndex secondIndex : ℕ)
    (values : List Scalar) (scratch : Scalar) (name : ScalarAccess.TapeName) :
    frame active firstIndex secondIndex values scratch (wiring first name) =
      mapTapes (equivalences Scalar first) (blanks first)
        (localFrame values (if first then firstIndex else secondIndex) scratch) name := by
  cases first <;> cases name
  all_goals first
    | change (_ : Turing.Tape Binary.Symbol) = Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap _ _) _
      exact (mapTape_identity _).symm
    | change (_ : Turing.Tape (TableTraversal.Symbol Scalar)) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap _ _) _
      exact (mapTape_identity _).symm

/-- Static wiring preserves the active count and the unused index tape. -/
theorem map_steps (selected : Bool) (operation : Scalar → Scalar)
    (active firstIndex secondIndex : ℕ) (values : List Scalar) (scratch : Scalar)
    (bounded : (if selected then firstIndex else secondIndex) < values.length) :
    let index := if selected then firstIndex else secondIndex
    Steps (mapAt selected operation) (4 * index + 9)
      (localEntry, frame active firstIndex secondIndex values scratch)
      (localExit, frame active firstIndex secondIndex (values.modify index operation) (operation values[index])) := by
  apply wire_steps_of_eq (wiring selected) _
    ((local_steps operation values ⟨_, bounded⟩ scratch).relabel (equivalences Scalar selected) (blanks selected))
  · exact frame_at selected active firstIndex secondIndex values scratch
  · exact frame_at selected active firstIndex secondIndex _ _
  · intro name outside
    cases selected <;> cases name <;> first
      | rfl
      | exact False.elim (outside ⟨.index, rfl⟩)
      | exact False.elim (outside ⟨.array, rfl⟩)
      | exact False.elim (outside ⟨.element, rfl⟩)

abbrev State := Sum LocalState LocalState
def entry : State := .inl localEntry
def exit : State := .inr localExit

noncomputable def machine (first second : Scalar → Scalar) : Machine (Alphabet Scalar) State :=
  sequence (mapAt true first) (mapAt false second) localEntry

/-- Active count, first index, second index, and the complete reserved array. -/
abbrev Value (Scalar : Type) := ℕ × (ℕ × (ℕ × List Scalar))

def applyAt (selected : Bool) (operation : Scalar → Scalar) (value : Value Scalar) : Value Scalar :=
  (value.1, value.2.1, value.2.2.1,
    value.2.2.2.modify (if selected then value.2.1 else value.2.2.1) operation)

def compute (first second : Scalar → Scalar) (value : Value Scalar) : Value Scalar :=
  applyAt false second (applyAt true first value)

def valid (capacity : ℕ) (value : Value Scalar) : Prop :=
  value.1 ≤ value.2.2.2.length ∧ value.2.2.2.length ≤ capacity ∧
    value.2.1 < value.1 ∧ value.2.2.1 < value.1

def representation (value : Value Scalar) (tapes : Tapes (Alphabet Scalar)) : Prop :=
  ∃ scratch, tapes = frame value.1 value.2.1 value.2.2.1 value.2.2.2 scratch

/-- One active operation, with unused storage hidden behind its representation. -/
theorem map_contract [Fintype Scalar] (selected : Bool) (operation : Scalar → Scalar) :
    Computes (mapAt selected operation) localEntry localExit
      (fun _sizes : Unit → ℕ => representation) (fun _ => representation)
      (fun sizes => valid (sizes ())) (fun _ => applyAt selected operation) := by
  refine ⟨by intro symbols; simp [mapAt, wire, relabel, local_halt], 4 * MvPolynomial.X () + 9, ?_⟩
  intro sizes value initial bounded represented
  obtain ⟨scratch, rfl⟩ := represented
  have selectedBound : (if selected then value.2.1 else value.2.2.1) < value.1 := by
    cases selected <;> simp_all [valid]
  have inRange := selectedBound.trans_le bounded.1
  have trace := map_steps selected operation value.1 value.2.1 value.2.2.1 value.2.2.2 scratch inRange
  refine ⟨_, _, ?_, trace, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    have capacity := inRange.le.trans bounded.2.1
    omega
  · exact ⟨_, rfl⟩

-- catalogueLevel: specialization-fixed identifiers for finite catalogue maps.
universe catalogueLevel

/-- Two catalogue tables compose on shared storage with a mathematical output.
The machine is fixed before the capacity, active count, indices, and data. -/
theorem contract [Fintype Scalar] {Catalogue : Type catalogueLevel}
    (maps : Catalogue → Scalar → Scalar) (first second : Catalogue) :
    Computes (machine (maps first) (maps second)) entry exit
      (fun _sizes : Unit → ℕ => representation) (fun _ => representation)
      (fun sizes => valid (sizes ())) (fun _ => compute (maps first) (maps second)) := by
  exact (map_contract true (maps first)).sequence (map_contract false (maps second))
    (by intro sizes value bounded; simpa [valid, applyAt] using bounded)

/-- Inactive data is preserved even when it is not a chosen padding value. -/
theorem inactive_preserved (first second : Scalar → Scalar) (capacity : ℕ)
    (value : Value Scalar) (bounded : valid capacity value) (index : Fin value.2.2.2.length)
    (inactive : value.1 ≤ index.val) :
    (compute first second value).2.2.2[index.val]'(by simp [compute, applyAt]) = value.2.2.2[index.val] := by
  have firstDifferent : value.2.1 ≠ index.val := by have selected := bounded.2.2.1; omega
  have secondDifferent : value.2.2.1 ≠ index.val := by have selected := bounded.2.2.2; omega
  simp [compute, applyAt, List.getElem_modify_ne, firstDifferent, secondDifferent]

end Polytime2.CatalogueMap
