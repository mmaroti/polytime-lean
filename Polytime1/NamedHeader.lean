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

import Polytime1.HeaderMoves

/-! # Header positions and relocation programs derived from field names

A layout is a fixed list of names. Moving a named field computes its current
position after earlier moves; runtime counter values never influence the
controller. The tape realization preserves all storage following the header.
-/

namespace Polytime1.NamedHeader

-- nameLevel: compile-time field identifiers.
universe nameLevel
variable {Name : Type nameLevel} [DecidableEq Name]

/-- Move the selected named field to the front of a layout. -/
def move (layout : List Name) (name : Name) : List Name := name :: layout.erase name

def positions : List Name → List Name → List ℕ
  | _, [] => []
  | layout, name :: rest => layout.idxOf name :: positions (move layout name) rest

def result : List Name → List Name → List Name
  | layout, [] => layout
  | layout, name :: rest => result (move layout name) rest

private theorem move_perm (layout : List Name) (name : Name) (available : name ∈ layout) :
    (move layout name).Perm layout := (List.perm_cons_erase available).symm

/-- The generated positions are valid in every intermediate layout. -/
theorem positions_valid (layout moves : List Name) (available : ∀ name ∈ moves, name ∈ layout) :
    ∀ position ∈ positions layout moves, position < layout.length := by
  induction moves generalizing layout with
  | nil => simp [positions]
  | cons name rest hypothesis =>
    have present := available name (by simp)
    have permutation := move_perm layout name present
    intro position member
    simp only [positions, List.mem_cons] at member
    rcases member with equal | member
    · subst position
      exact List.idxOf_lt_length_iff.mpr present
    · have restAvailable : ∀ other ∈ rest, other ∈ move layout name := by
        intro other member
        exact permutation.mem_iff.mpr (available other (by simp [member]))
      simpa only [permutation.length_eq] using hypothesis _ restAvailable position member

private theorem map_move (layout : List Name) (name : Name) (values : Name → ℕ) (available : name ∈ layout) :
    HeaderMoves.moveToFront (layout.idxOf name) (layout.map values) = (move layout name).map values := by
  simp only [HeaderMoves.moveToFront, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf available, Option.map_some, Option.getD_some, move, List.map_cons]
  rw [List.erase_eq_eraseIdx_of_idxOf rfl, List.eraseIdx_eq_take_drop_succ]
  simp only [List.map_append, List.map_take, List.map_drop]

/-- Numerical relocation agrees with the named layout for arbitrary counter
values, including equal values in different fields. -/
theorem apply_positions (layout moves : List Name) (values : Name → ℕ)
    (available : ∀ name ∈ moves, name ∈ layout) :
    HeaderMoves.applyMoves (positions layout moves) (layout.map values) = (result layout moves).map values := by
  induction moves generalizing layout with
  | nil => rfl
  | cons name rest hypothesis =>
    have present := available name (by simp)
    have permutation := move_perm layout name present
    simp only [positions, HeaderMoves.applyMoves, List.foldl_cons, map_move layout name values present, result]
    exact hypothesis _ (by intro other member; exact permutation.mem_iff.mpr (available other (by simp [member])))

/-- Compile named moves once; the finite controller is independent of values
and the preserved suffix. All navigation and handovers are counted. -/
theorem realizes (layout moves : List Name) (available : ∀ name ∈ moves, name ∈ layout) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine UnaryMachine.Symbol Controller),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (values : Name → ℕ) (tail : List UnaryMachine.Symbol),
          ∃ ticks, ticks ≤ (positions layout moves).length *
            (128 * ((UnaryMachine.fields (layout.map values)).length + 1) ^ 2 + 1) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (UnaryMachine.fields (layout.map values) ++ tail))
              (Tape.configuration exit [] (UnaryMachine.fields ((result layout moves).map values) ++ tail)) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, halt, runs⟩ := HeaderMoves.realizes (positions layout moves)
  refine ⟨Controller, finite, inhabited, entry, exit, machine, halt, ?_⟩
  intro values tail
  obtain ⟨ticks, cost, trace⟩ := runs (layout.map values) (by
    intro position member
    simpa using positions_valid layout moves available position member) tail
  exact ⟨ticks, cost, by simpa only [apply_positions layout moves values available] using trace⟩

end Polytime1.NamedHeader
