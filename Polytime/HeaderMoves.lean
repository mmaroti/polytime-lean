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

import Polytime.HeaderMoveMachine

/-! # Fixed compositions of runtime header relocations

Column elimination changes between a guard header and a row-operation header.
A fixed list of positions compiles to a finite controller; only field values
are runtime inputs. Every relocation preserves all trailing storage.
-/

namespace Polytime.HeaderMoves

open UnaryMachine (Symbol fields)

/-- Move a valid selected field to the front. Invalid positions are excluded
by the realization theorem's input hypothesis. -/
def moveToFront (position : ℕ) (values : List ℕ) : List ℕ :=
  values.getD position 0 :: (values.take position ++ values.drop (position + 1))

/-- Apply the fixed relocations in their program order. -/
def applyMoves (positions values : List ℕ) : List ℕ := positions.foldl (fun values position => moveToFront position values) values

/-- Compile fixed header relocations with a quadratic bound in header storage.
The controller and polynomial coefficient depend on the fixed position list,
never on the runtime field values or tail. -/
theorem realizes (positions : List ℕ) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (values : List ℕ) (_valid : ∀ position ∈ positions, position < values.length) (tail : List Symbol),
          ∃ ticks, ticks ≤ positions.length * (128 * ((fields values).length + 1) ^ 2 + 1) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (fields values ++ tail))
              (Tape.configuration exit [] (fields (applyMoves positions values) ++ tail)) := by
  induction positions with
  | nil =>
    refine ⟨Unit, inferInstance, inferInstance, (), (), (fun _ _ => none), by simp, ?_⟩
    intro values _ tail
    exact ⟨0, by simp, .zero _⟩
  | cons position positions hypothesis =>
    obtain ⟨RestState, restFinite, restInhabited, restEntry, restExit, restMachine, restHalt, restRuns⟩ := hypothesis
    let restControllerFinite : Fintype RestState := restFinite
    let restControllerInhabited : Inhabited RestState := restInhabited
    let moveControllerFinite : Fintype (HeaderMoveMachine.State position) := inferInstance
    let moveEntry : HeaderMoveMachine.State position := .inl (Fin.last position, 0)
    let moveExit : HeaderMoveMachine.State position := .inr (.inr (.inr (0, 7)))
    refine ⟨Sum (HeaderMoveMachine.State position) RestState, inferInstance, inferInstance,
      .inl moveEntry, .inr restExit,
      Tape.sequence (HeaderMoveMachine.machine position) restMachine restEntry, ?_, ?_⟩
    · intro symbol; simp [Tape.sequence, restHalt]
    · intro values valid tail
      have active : position < values.length := valid position (by simp)
      let before := values.take position
      let value := values[position]
      let after := values.drop (position + 1)
      let moved := value :: (before ++ after)
      have split : before ++ value :: after = values := by
        simp [before, value, after]
      have movedEquality : moveToFront position values = moved := by
        simp [moveToFront, moved, before, value, after, List.getD_eq_getElem?_getD, active]
      have lengthEquality : moved.length = values.length := by
        rw [← split]
        simp [moved, Nat.add_comm, Nat.add_left_comm]
      have storageEquality : (fields moved).length = (fields values).length := by
        rw [← split]
        simp [moved, fields, List.flatMap_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      obtain ⟨moveTicks, moveCost, moveTrace⟩ := HeaderMoveMachine.realizes before after value tail
      have beforeLength : before.length = position := by simp [before, Nat.min_eq_left (Nat.le_of_lt active)]
      rw [beforeLength] at moveTrace
      have moveTrace' : Tape.Steps (HeaderMoveMachine.machine position) moveTicks
          (Tape.configuration moveEntry [] (fields values ++ tail))
          (Tape.configuration moveExit [] (fields moved ++ tail)) := by
        simpa only [moveEntry, moveExit, split, moved, List.cons_append] using moveTrace
      obtain ⟨restTicks, restCost, restTrace⟩ := restRuns moved
        (by intro index member; rw [lengthEquality]; exact valid index (by simp [member])) tail
      have moveHalt (symbol : Symbol) : HeaderMoveMachine.machine position moveExit symbol = none := by
        simp [moveExit, HeaderMoveMachine.halt]
      have computation := Tape.sequence_steps restEntry moveTrace' moveHalt restTrace
      rw [split] at moveCost
      rw [storageEquality] at restCost
      refine ⟨moveTicks + (restTicks + 1), ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa only [applyMoves, List.foldl_cons, movedEquality, moveEntry, moveExit, Tape.configuration] using computation


/-- Remove a fixed number of leading counters, preserving all following storage.
Column elimination uses this to discard its completed traversal counters. -/
theorem realizes_remove_front (count : ℕ) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (values : List ℕ) (_valid : count ≤ values.length) (tail : List Symbol),
          ∃ ticks, ticks ≤ count * (4 * (fields values).length + 8) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (fields values ++ tail))
              (Tape.configuration exit [] (fields (values.drop count) ++ tail)) := by
  induction count with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, (), (), (fun _ _ => none), by simp, ?_⟩
    intro values _ tail
    exact ⟨0, by simp, .zero _⟩
  | succ count hypothesis =>
    obtain ⟨RestState, finite, inhabited, restEntry, restExit, restMachine, restHalt, restRuns⟩ := hypothesis
    let restControllerFinite : Fintype RestState := finite
    let restControllerInhabited : Inhabited RestState := inhabited
    let removeEntry : Sum (HeaderResetMachine.State 0) (HeaderMoveMachine.RemoveZero.State 0) := .inl (.inl (Fin.last 0))
    let removeExit : Sum (HeaderResetMachine.State 0) (HeaderMoveMachine.RemoveZero.State 0) := .inr (.inr (0, 7))
    refine ⟨Sum (Sum (HeaderResetMachine.State 0) (HeaderMoveMachine.RemoveZero.State 0)) RestState,
      inferInstance, inferInstance, .inl removeEntry, .inr restExit,
      Tape.sequence (HeaderMoveMachine.remove 0) restMachine restEntry, ?_, ?_⟩
    · intro symbol; simp [Tape.sequence, restHalt]
    · intro values valid tail
      cases values with
      | nil => simp at valid
      | cons value values =>
        have removed := HeaderMoveMachine.removes [] value (fields values ++ tail)
        have removed' : Tape.Steps (HeaderMoveMachine.remove 0) (4 * value + 7)
            (Tape.configuration removeEntry [] (fields (value :: values) ++ tail))
            (Tape.configuration removeExit [] (fields values ++ tail)) := by
          simpa [removeEntry, removeExit, fields, List.append_assoc, Nat.mul_comm] using removed
        obtain ⟨restTicks, restCost, restTrace⟩ := restRuns values (by simpa using valid) tail
        have removeHalt (symbol : Symbol) : HeaderMoveMachine.remove 0 removeExit symbol = none := by
          simp [HeaderMoveMachine.remove, removeExit, Tape.sequence, HeaderMoveMachine.RemoveZero.halt]
        have computation := Tape.sequence_steps restEntry removed' removeHalt restTrace
        refine ⟨4 * value + 7 + (restTicks + 1), ?_, ?_⟩
        · have storage : (fields (value :: values)).length = value + 1 + (fields values).length := by
            simp [UnaryMachine.fields_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [storage]
          nlinarith
        · simpa only [removeEntry, removeExit, List.drop_succ_cons, Tape.configuration] using computation

/-- Relocate the row-limit counter between the loop-guard and row-update layouts. -/
theorem realizes_guard_to_row :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (source target limit column columns pivotColumn : ℕ) (tail : List Symbol),
          ∃ ticks, ticks ≤ 6 * (128 * (source + target + limit + column + columns + pivotColumn + 7) ^ 2 + 1) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (fields [source, target, limit, column, columns, pivotColumn] ++ tail))
              (Tape.configuration exit [] (fields [source, target, column, columns, pivotColumn, limit] ++ tail)) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, halt, runs⟩ := realizes [2, 5, 5, 5, 5, 5]
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, halt, ?_⟩
  intro source target limit column columns pivotColumn tail
  obtain ⟨ticks, cost, trace⟩ := runs [source, target, limit, column, columns, pivotColumn] (by simp) tail
  refine ⟨ticks, ?_, ?_⟩
  · simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cost
  · simpa [applyMoves, moveToFront, List.getD] using trace

/-- Relocate the row-limit counter between the loop-guard and row-update layouts. -/
theorem realizes_row_to_guard :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (source target limit column columns pivotColumn : ℕ) (tail : List Symbol),
          ∃ ticks, ticks ≤ 6 * (128 * (source + target + limit + column + columns + pivotColumn + 7) ^ 2 + 1) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (fields [source, target, column, columns, pivotColumn, limit] ++ tail))
              (Tape.configuration exit [] (fields [source, target, limit, column, columns, pivotColumn] ++ tail)) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, halt, runs⟩ := realizes [4, 4, 4, 5, 5, 5]
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, halt, ?_⟩
  intro source target limit column columns pivotColumn tail
  obtain ⟨ticks, cost, trace⟩ := runs [source, target, column, columns, pivotColumn, limit] (by simp) tail
  refine ⟨ticks, ?_, ?_⟩
  · simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cost
  · simpa [applyMoves, moveToFront, List.getD] using trace

end Polytime.HeaderMoves
