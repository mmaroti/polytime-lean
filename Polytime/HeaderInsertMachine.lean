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

import Polytime.UnaryMachine

/-! # Inserting fixed symbols after runtime header counters

Move only the counter prefix left into blank storage. The suffix stays in
place. Matrix preparation uses this to insert a scalar slot and its separator.
-/

namespace Polytime.HeaderInsertMachine

open UnaryMachine (Symbol fields units)

abbrev State (position : ℕ) := Sum (Fin (position + 1)) (Symbol × Fin 3)

/-- Locate the insertion boundary, then carry the prefix one cell left. -/
def machine (position : ℕ) (inserted : Symbol) : Turing.TM0.Machine Symbol (State position) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else some (.inr (inserted, 0), .move .left)
  | .inr (carried, phase) =>
    match phase.val with
    | 0 => if symbol = 0 then some (.inr (0, 2), .write carried)
        else some (.inr (symbol, 1), .write carried)
    | 1 => some (.inr (carried, 0), .move .left)
    | _ => none

variable {position : ℕ}

private theorem carry (inserted : Symbol) (cells : List Symbol) (carried : Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position inserted) (2 * cells.length + 1)
      (Tape.configuration (.inr (carried, 0)) cells.tail (cells.headD 0 :: tail))
      (Tape.configuration (.inr (0, 2)) [] (cells.reverse ++ carried :: tail)) := by
  induction cells generalizing carried tail with
  | nil =>
    exact .next (Tape.write [] tail 0 carried (by simp [machine])) (.zero _)
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have written := Tape.write (machine := machine position inserted)
      (state := .inr (carried, 0)) (nextState := .inr (symbol, 1)) cells tail symbol carried
      (by simp [machine, distinct])
    have moved := Tape.move_left_headD (machine := machine position inserted)
      (state := .inr (symbol, 1)) (nextState := .inr (symbol, 0)) cells tail carried (by rfl)
    have rest := hypothesis symbol (carried :: tail)
      (by intro current member; exact valid current (by simp [member]))
    have trace := Tape.Steps.next written (Tape.Steps.next moved rest)
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using trace

private theorem skip (inserted : Symbol) (prior : List ℕ) (remaining : Fin (position + 1))
    (index : remaining.val = prior.length) (left right : List Symbol) :
    Tape.Steps (machine position inserted) (fields prior).length
      (Tape.configuration (.inl remaining) left (fields prior ++ right))
      (Tape.configuration (.inl 0) ((fields prior).reverse ++ left) right) := by
  induction prior generalizing remaining left with
  | nil =>
    have same : remaining = 0 := Fin.ext index
    subst remaining
    simp [fields]
    exact .zero _
  | cons value prior hypothesis =>
    have positive : remaining.val > 0 := by simp at index; omega
    let next : Fin (position + 1) := ⟨remaining.val - 1, by omega⟩
    have scanned := Tape.scan_right (machine := machine position inserted) (state := .inl remaining)
      (units value) left (1 :: (fields prior ++ right))
      (by intro symbol member
          have equality : symbol = 2 := List.eq_of_mem_replicate member
          subst symbol
          simp [machine, positive])
    simp only [UnaryMachine.units_reverse] at scanned
    have crossed := Tape.move_right (machine := machine position inserted) (state := .inl remaining)
      (nextState := .inl next) (units value ++ left) (fields prior ++ right) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by simp at index; simp [next]; omega) (1 :: (units value ++ left))
    have trace := scanned.trans (.next crossed rest)
    simpa [fields, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using trace

/-- Insert one fixed symbol, preserving all counter values and the arbitrary tail. -/
theorem realizes (prior : List ℕ) (inserted : Symbol) (tail : List Symbol) :
    Tape.Steps (machine prior.length inserted) (3 * (fields prior).length + 2)
      (Tape.configuration (.inl (Fin.last prior.length)) [] (fields prior ++ tail))
      (Tape.configuration (.inr (0, 2)) [] (fields prior ++ inserted :: tail)) := by
  have scanned := skip inserted prior (Fin.last prior.length) rfl [] tail
  simp only [List.append_nil] at scanned
  let cells := (fields prior).reverse
  have enter : Turing.TM0.step (machine prior.length inserted)
      (Tape.configuration (.inl 0) cells tail) =
      some (Tape.configuration (.inr (inserted, 0)) cells.tail (cells.headD 0 :: tail)) := by
    cases cells with
    | nil => exact Tape.move_left_empty tail (by simp [machine])
    | cons symbol cells => exact Tape.move_left_list cells tail symbol (by simp [machine])
  have shifted := carry (position := prior.length) inserted cells inserted tail (by
    intro symbol member
    rcases UnaryMachine.fields_symbols prior symbol (List.mem_reverse.mp member) with rfl | rfl <;> decide)
  have trace := scanned.trans (.next enter shifted)
  have ticks : (fields prior).length + (2 * cells.length + 1 + 1) = 3 * (fields prior).length + 2 := by
    simp only [cells, List.length_reverse]; omega
  rw [ticks] at trace
  simpa only [cells, List.reverse_reverse] using trace

@[simp] theorem halt (inserted symbol : Symbol) : machine position inserted (.inr (0, 2)) symbol = none := rfl

/-- Insert a fixed word after a fixed number of runtime counters. The controller
and word are independent of those counter values and the preserved suffix. -/
theorem realizes_word (position : ℕ) (inserted : List Symbol) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (inserter : Turing.TM0.Machine Symbol Controller),
        (∀ symbol, inserter exit symbol = none) ∧
        ∀ (prior : List ℕ) (_length : prior.length = position) (tail : List Symbol),
          ∃ ticks, ticks ≤ inserted.length * (3 * (fields prior).length + 3) ∧
            Tape.Steps inserter ticks
              (Tape.configuration entry [] (fields prior ++ tail))
              (Tape.configuration exit [] (fields prior ++ inserted ++ tail)) := by
  induction inserted with
  | nil =>
    refine ⟨Unit, inferInstance, inferInstance, (), (), (fun _ _ => none), by simp, ?_⟩
    intro prior _ tail
    refine ⟨0, by simp, ?_⟩
    simp only [List.append_nil]
    exact .zero _
  | cons symbol inserted hypothesis =>
    obtain ⟨RestState, finite, inhabited, restEntry, restExit, restMachine, restHalt, restRuns⟩ := hypothesis
    let restControllerFinite : Fintype RestState := finite
    let restControllerInhabited : Inhabited RestState := inhabited
    let insertEntry : State position := .inl (Fin.last position)
    let insertExit : State position := .inr (0, 2)
    refine ⟨Sum RestState (State position), inferInstance, inferInstance, .inl restEntry, .inr insertExit,
      Tape.sequence restMachine (machine position symbol) insertEntry, ?_, ?_⟩
    · intro current; simp [Tape.sequence, insertExit]
    · intro prior length tail
      obtain ⟨restTicks, restCost, restTrace⟩ := restRuns prior length tail
      have insertedTrace := realizes prior symbol (inserted ++ tail)
      rw [length] at insertedTrace
      simp only [List.append_assoc] at restTrace
      have trace := Tape.sequence_steps insertEntry restTrace restHalt insertedTrace
      refine ⟨restTicks + (3 * (fields prior).length + 2 + 1), ?_, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · simpa only [insertEntry, insertExit, List.cons_append, List.append_assoc, Tape.configuration] using trace

namespace CounterDelimiter

/-- Turn the selected unary capacity into an all-one binary window terminated
by marker four, then return to the original header. -/
def machine (position : ℕ) : Turing.TM0.Machine Symbol (State position) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else if symbol = 2 then some (.inl 0, .move .right)
    else if symbol = 1 then some (.inr (0, 0), .write 4) else none
  | .inr (carried, phase) =>
    match phase.val with
    | 0 => some (.inr (carried, 1), .move .left)
    | 1 => if symbol = 0 then some (.inr (0, 2), .move .right)
        else some (.inr (carried, 1), .move .left)
    | _ => none

private theorem skip (prior : List ℕ) (remaining : Fin (position + 1))
    (index : remaining.val = prior.length) (left right : List Symbol) :
    Tape.Steps (machine position) (fields prior).length
      (Tape.configuration (.inl remaining) left (fields prior ++ right))
      (Tape.configuration (.inl 0) ((fields prior).reverse ++ left) right) := by
  induction prior generalizing remaining left with
  | nil =>
    have same : remaining = 0 := Fin.ext index
    subst remaining
    simp [fields]
    exact .zero _
  | cons value prior hypothesis =>
    have positive : remaining.val > 0 := by simp at index; omega
    let next : Fin (position + 1) := ⟨remaining.val - 1, by omega⟩
    have scanned := Tape.scan_right (machine := machine position) (state := .inl remaining)
      (units value) left (1 :: (fields prior ++ right))
      (by intro symbol member
          have equality : symbol = 2 := List.eq_of_mem_replicate member
          subst symbol
          simp [machine, positive])
    simp only [UnaryMachine.units_reverse] at scanned
    have crossed := Tape.move_right (machine := machine position) (state := .inl remaining)
      (nextState := .inl next) (units value ++ left) (fields prior ++ right) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by simp at index; simp [next]; omega) (1 :: (units value ++ left))
    have trace := scanned.trans (.next crossed rest)
    simpa [fields, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using trace

private theorem back (cells tail : List Symbol) (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position) (cells.length + 1)
      (Tape.configuration (.inr (0, 1)) cells.tail (cells.headD 0 :: tail))
      (Tape.configuration (.inr (0, 2)) [] (cells.reverse ++ tail)) := by
  induction cells generalizing tail with
  | nil =>
    have moved := Tape.move_right (machine := machine position) (state := .inr (0, 1))
      (nextState := .inr (0, 2)) [] tail 0 (by simp [machine])
    have blank : Tape.configuration (.inr (0, 2) : State position) [0] tail =
        Tape.configuration (.inr (0, 2) : State position) [] tail :=
      Tape.configuration_append_blank (Symbol := Symbol) _ [] tail
    rw [blank] at moved
    exact .next moved (.zero _)
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have moved := Tape.move_left_headD (machine := machine position) (state := .inr (0, 1))
      (nextState := .inr (0, 1)) cells tail symbol (by simp [machine, distinct])
    have rest := hypothesis (symbol :: tail)
      (by intro current member; exact valid current (by simp [member]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Tape.Steps.next moved rest

/-- Format the capacity field while preserving the header and arbitrary suffix. -/
theorem realizes (prior : List ℕ) (capacity : ℕ) (tail : List Symbol) :
    Tape.Steps (machine prior.length) (2 * ((fields prior).length + capacity) + 3)
      (Tape.configuration (.inl (Fin.last prior.length)) []
        (fields prior ++ units capacity ++ 1 :: tail))
      (Tape.configuration (.inr (0, 2)) []
        (fields prior ++ units capacity ++ 4 :: tail)) := by
  have skipped := skip prior (Fin.last prior.length) rfl [] (units capacity ++ 1 :: tail)
  simp only [List.append_nil] at skipped
  have scanned := Tape.scan_right (machine := machine prior.length) (state := .inl 0)
    (units capacity) (fields prior).reverse (1 :: tail)
    (by intro symbol member
        have equal : symbol = 2 := List.eq_of_mem_replicate member
        subst symbol
        simp [machine])
  have written := Tape.write (machine := machine prior.length) (state := .inl 0)
    (nextState := .inr (0, 0)) ((units capacity).reverse ++ (fields prior).reverse) tail 1 4
    (by simp [machine])
  let cells := (units capacity).reverse ++ (fields prior).reverse
  have entered := Tape.move_left_headD (machine := machine prior.length) (state := .inr (0, 0))
    (nextState := .inr (0, 1)) cells tail 4 (by rfl)
  have returned := back (position := prior.length) cells (4 :: tail) (by
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · have equal : symbol = 2 := List.eq_of_mem_replicate (List.mem_reverse.mp member)
      subst symbol; decide
    · rcases UnaryMachine.fields_symbols prior symbol (List.mem_reverse.mp member) with rfl | rfl <;> decide)
  have trace := skipped.trans (scanned.trans (.next written (.next entered returned)))
  have ticks : (fields prior).length + ((units capacity).length + (cells.length + 1 + 1 + 1)) =
      2 * ((fields prior).length + capacity) + 3 := by
    simp [cells, units]; omega
  rw [ticks] at trace
  simpa [cells, List.reverse_append, List.append_assoc] using trace

@[simp] theorem halt (symbol : Symbol) : machine position (.inr (0, 2)) symbol = none := rfl

end CounterDelimiter

end Polytime.HeaderInsertMachine
