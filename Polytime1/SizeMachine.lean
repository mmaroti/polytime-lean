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

import Polytime1.UnaryMachine

/-! # Tape realization of executable size expressions

Unary counters use the size-header alphabet. Every routine preserves the
untouched suffix, including the canonical input. Controller sizes depend on
expressions and field positions, never on a runtime size assignment.
-/

namespace Polytime1.SizeMachine

open UnaryMachine (Symbol units fields)

namespace Copy

abbrev State (index : ℕ) := Fin (index + 1) × UnaryMachine.State
instance (index : ℕ) : Inhabited (State index) := ⟨(0, 0)⟩

def machine (index : ℕ) : Turing.TM0.Machine Symbol (State index) := fun (remaining, phase) symbol =>
  if phase = 3 ∧ remaining.val > 0 then
    some ((if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining, 3), .move .right)
  else (UnaryMachine.machine false true phase symbol).map fun (next, action) =>
    ((remaining, next), action)

theorem lift (index : ℕ) {ticks : ℕ} {initial final : Tape.Configuration Symbol UnaryMachine.State}
    (trace : UnaryMachine.CopySteps false true ticks initial final) :
    Tape.Steps (machine index) ticks ⟨((0 : Fin (index + 1)), initial.q), initial.Tape⟩
      ⟨((0 : Fin (index + 1)), final.q), final.Tape⟩ := by
  apply trace.rename (fun phase => ((0 : Fin (index + 1)), phase))
  intro phase symbol next action transition
  simp [machine, transition]

theorem skip (index : ℕ) (before : List ℕ) (remaining : Fin (index + 1))
    (position : remaining.val = before.length) (left right : List Symbol) :
    Tape.Steps (machine index) (fields before).length
      (Tape.configuration (remaining, 3) left (fields before ++ right))
      (Tape.configuration ((0 : Fin (index + 1)), 3) ((fields before).reverse ++ left) right) := by
  induction before generalizing remaining left with
  | nil =>
    have equality : remaining = 0 := Fin.ext position
    subst remaining
    simp [fields]
    exact .zero _
  | cons value before hypothesis =>
    have positive : remaining.val > 0 := by simp at position; omega
    let next : Fin (index + 1) := ⟨remaining.val - 1, by omega⟩
    have scan := Tape.scan_right (machine := machine index) (state := (remaining, 3))
      (units value) left (1 :: (fields before ++ right))
      (by intro symbol member
          have equality : symbol = 2 := List.eq_of_mem_replicate member
          subst symbol
          simp [machine, positive])
    simp only [UnaryMachine.units_reverse] at scan
    have advance := Tape.move_right (machine := machine index) (state := (remaining, 3))
      (nextState := (next, 3)) (units value ++ left) (fields before ++ right) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by simp at position; simp [next]; omega)
      (1 :: (units value ++ left))
    have trace := scan.trans (.next advance rest)
    simpa [fields, List.reverse_append, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using trace

/-- Copy a selected field inside finite reserved workspace. `value + 2`
blank cells suffice; one remains before the copied field, and both callers survive. -/
theorem realizes_reserved (before suffix : List ℕ) (value : ℕ) (caller tail : List Symbol) :
    ∃ ticks, ticks ≤ 64 * ((fields (before ++ value :: suffix)).length + 1) ^ 2 ∧
      Tape.Steps (machine before.length) ticks
        (Tape.configuration (Fin.last before.length, 0) (List.replicate (value + 2) 0 ++ caller)
          (fields (before ++ value :: suffix) ++ tail))
        (Tape.configuration ((0 : Fin (before.length + 1)), 19) (0 :: caller)
          (fields (value :: before ++ value :: suffix) ++ tail)) := by
  let right := fields (before ++ value :: suffix) ++ tail
  have move := Tape.move_left_list (machine := machine before.length)
    (state := (Fin.last before.length, 0)) (nextState := (Fin.last before.length, 1)) (List.replicate (value + 1) 0 ++ caller) right 0
    (by intro symbol; simp [machine, UnaryMachine.machine])
  have mark := Tape.write (machine := machine before.length)
    (state := (Fin.last before.length, 1)) (nextState := (Fin.last before.length, 2))
    (List.replicate (value + 1) 0 ++ caller) right 0 5 (by simp [machine, UnaryMachine.machine])
  have enter := Tape.move_right (machine := machine before.length)
    (state := (Fin.last before.length, 2)) (nextState := (Fin.last before.length, 3))
    (List.replicate (value + 1) 0 ++ caller) right 5 (by simp [machine, UnaryMachine.machine])
  have scan := skip before.length before (Fin.last before.length) rfl (5 :: (List.replicate (value + 1) 0 ++ caller))
    (units value ++ 1 :: (fields suffix ++ tail))
  have switch := Tape.write (machine := machine before.length)
    (state := ((0 : Fin (before.length + 1)), 3)) (nextState := (0, 6))
    ((fields before).reverse ++ 5 :: (List.replicate (value + 1) 0 ++ caller)) (units value ++ 1 :: (fields suffix ++ tail)).tail
    (units value ++ 1 :: (fields suffix ++ tail)).head!
    (units value ++ 1 :: (fields suffix ++ tail)).head!
    (by simp [machine, UnaryMachine.machine])
  have switch' : Tape.Steps (machine before.length) 1
      (Tape.configuration ((0 : Fin (before.length + 1)), 3)
        ((fields before).reverse ++ 5 :: (List.replicate (value + 1) 0 ++ caller)) (units value ++ 1 :: (fields suffix ++ tail)))
      (Tape.configuration ((0 : Fin (before.length + 1)), 6)
        ((fields before).reverse ++ 5 :: (List.replicate (value + 1) 0 ++ caller)) (units value ++ 1 :: (fields suffix ++ tail))) := by
    cases value <;> simpa [units, List.replicate_succ] using Tape.Steps.next switch (.zero _)
  have copy := lift before.length (UnaryMachine.copy_loop_reserved false value 0 (fields before)
    (fields suffix ++ tail) (0 :: caller)
    (by intro symbol member
        rcases UnaryMachine.fields_symbols before symbol member with rfl | rfl <;> decide)
    (copyMode := true))
  have finish := lift before.length (UnaryMachine.finish_copy_reserved (fields before ++ units value)
    (fields suffix ++ tail) caller value
    (by intro symbol member
        rcases List.mem_append.mp member with member | member
        · rcases UnaryMachine.fields_symbols before symbol member with rfl | rfl <;> decide
        · have equality : symbol = 2 := List.eq_of_mem_replicate member
          subst symbol; decide))
  simp only [Nat.zero_add, units, List.replicate_zero] at copy
  simp only [List.reverse_append, UnaryMachine.units_reverse] at finish
  have bootstrap := Tape.Steps.next move (Tape.Steps.next mark (Tape.Steps.next enter (.zero _)))
  simp only [right, UnaryMachine.fields_append, UnaryMachine.fields_cons, List.append_assoc,
    List.cons_append] at bootstrap
  simp only [List.replicate_succ', List.append_assoc, List.singleton_append] at bootstrap scan switch'
  have trace := bootstrap.trans (scan.trans (switch'.trans (copy.trans finish)))
  have margin : 0 :: (List.replicate value (0 : Symbol) ++ 0 :: caller) =
      List.replicate (value + 2) 0 ++ caller := by
    rw [← List.cons_append, ← List.replicate_succ]
    rw [← (show ([0] : List Symbol) ++ caller = 0 :: caller from rfl),
      ← List.append_assoc, ← List.replicate_succ']
  rw [margin] at trace
  refine ⟨3 + ((fields before).length + (1 + (UnaryMachine.copyTicks (fields before).length 0 value +
    ((fields before ++ units value).length + value + 5)))), ?_, ?_⟩
  · have localBound : 3 + ((fields before).length +
        (1 + (UnaryMachine.copyTicks (fields before).length 0 value +
          ((fields before ++ units value).length + value + 5)))) ≤
        64 * ((fields before).length + value + 1) ^ 2 := by
      simp only [UnaryMachine.copyTicks, List.length_append, UnaryMachine.units_length,
        Nat.mul_zero, Nat.add_zero]
      nlinarith [Nat.zero_le ((fields before).length * value)]
    have widthBound : (fields before).length + value + 1 ≤
        (fields (before ++ value :: suffix)).length + 1 := by
      simp only [UnaryMachine.fields_length, List.sum_append, List.sum_cons,
        List.length_append, List.length_cons]; omega
    exact localBound.trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left widthBound 2))
  · simpa only [right, UnaryMachine.fields_cons, UnaryMachine.fields_append,
      List.append_assoc, List.cons_append, UnaryMachine.configuration, Tape.configuration,
      Nat.zero_add, Nat.add_zero, Nat.zero_add] using trace

/-- The original blank-left convention is the empty-caller case. -/
theorem realizes (before suffix : List ℕ) (value : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ 64 * ((fields (before ++ value :: suffix)).length + 1) ^ 2 ∧
      Tape.Steps (machine before.length) ticks
        (Tape.configuration (Fin.last before.length, 0) []
          (fields (before ++ value :: suffix) ++ tail))
        (Tape.configuration ((0 : Fin (before.length + 1)), 19) []
          (fields (value :: before ++ value :: suffix) ++ tail)) := by
  obtain ⟨ticks, cost, trace⟩ := realizes_reserved before suffix value [] tail
  refine ⟨ticks, cost, ?_⟩
  simp only [List.append_nil] at trace
  change Tape.Steps (machine before.length) ticks
    (Tape.configuration (Fin.last before.length, 0) (List.replicate (value + 2) default)
      (fields (before ++ value :: suffix) ++ tail))
    (Tape.configuration ((0 : Fin (before.length + 1)), 19) (List.replicate 1 default)
      (fields (value :: before ++ value :: suffix) ++ tail)) at trace
  simpa only [Tape.configuration_replicate_blank] using trace

end Copy

namespace Constant

abbrev State (value : ℕ) := Fin (value + 1) × Fin 5
instance (value : ℕ) : Inhabited (State value) := ⟨(0, 0)⟩

def machine (value : ℕ) : Turing.TM0.Machine Symbol (State value) := fun (remaining, phase) symbol =>
  match phase.val with
  | 0 => some ((remaining, 1), .move .left)
  | 1 => some ((remaining, 2), .write 1)
  | 2 => if remaining.val = 0 then some ((remaining, 4), .write symbol)
      else some ((remaining, 3), .move .left)
  | 3 => some ((⟨remaining.val - 1, by omega⟩, 2), .write 2)
  | _ => none

theorem loop_reserved (value : ℕ) (remaining : Fin (value + 1)) (caller right : List Symbol) :
    Tape.Steps (machine value) (2 * remaining.val + 1)
      (Tape.configuration (remaining, 2) (List.replicate remaining.val 0 ++ caller) right)
      (Tape.configuration ((0 : Fin (value + 1)), 4) caller (units remaining.val ++ right)) := by
  generalize equality : remaining.val = count
  induction count generalizing remaining right with
  | zero =>
    have same : remaining = 0 := Fin.ext equality
    subst remaining
    have stay : Turing.TM0.step (machine value)
        (Tape.configuration ((0 : Fin (value + 1)), 2) caller right) =
        some (Tape.configuration ((0 : Fin (value + 1)), 4) caller right) := by
      have command : ∀ symbol, machine value ((0 : Fin (value + 1)), 2) symbol =
          some ((0, 4), .write symbol) := by intro symbol; simp [machine]
      simp only [Turing.TM0.step, Tape.configuration, command, Option.map_some,
        Turing.Tape.write_self]
    simpa [units] using Tape.Steps.next stay (.zero _)
  | succ count hypothesis =>
    let next : Fin (value + 1) := ⟨count, by omega⟩
    have move := Tape.move_left_list (machine := machine value)
      (state := (remaining, 2)) (nextState := (remaining, 3)) (List.replicate count 0 ++ caller) right
      0 (by intro symbol; simp [machine, equality])
    have write := Tape.write (machine := machine value)
      (state := (remaining, 3)) (nextState := (next, 2)) (List.replicate count 0 ++ caller) right 0 2
      (by simp [machine, next, equality])
    have rest := hypothesis next (2 :: right) rfl
    have trace := Tape.Steps.next move (Tape.Steps.next write rest)
    convert trace using 1
    all_goals first | omega | simp [units, List.replicate_succ', List.append_assoc]
    have rotate := congrArg (fun cells : List Symbol => cells ++ caller)
      ((List.replicate_succ' (n := count) (a := (0 : Symbol))).symm.trans
        (List.replicate_succ (n := count) (a := (0 : Symbol))))
    exact congrArg (fun cells => Tape.configuration (remaining, 2) cells right)
      (by simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using rotate)

/-- Allocate a constant field in exactly `value + 1` reserved blank cells.
The exit head is on its first cell; both caller regions are preserved. -/
theorem realizes_reserved (value : ℕ) (caller right : List Symbol) :
    Tape.Steps (machine value) (2 * value + 3)
      (Tape.configuration (Fin.last value, 0) (List.replicate (value + 1) 0 ++ caller) right)
      (Tape.configuration ((0 : Fin (value + 1)), 4) caller (units value ++ 1 :: right)) := by
  have move := Tape.move_left_list (machine := machine value)
    (state := (Fin.last value, 0)) (nextState := (Fin.last value, 1)) (List.replicate value 0 ++ caller) right 0
    (by intro symbol; rfl)
  have write := Tape.write (machine := machine value)
    (state := (Fin.last value, 1)) (nextState := (Fin.last value, 2)) (List.replicate value 0 ++ caller) right 0 1 (by rfl)
  simpa [Nat.add_assoc, List.replicate_succ] using Tape.Steps.next move
    (Tape.Steps.next write (loop_reserved value (Fin.last value) caller (1 :: right)))

theorem loop (value : ℕ) (remaining : Fin (value + 1)) (right : List Symbol) :
    Tape.Steps (machine value) (2 * remaining.val + 1)
      (Tape.configuration (remaining, 2) [] right)
      (Tape.configuration ((0 : Fin (value + 1)), 4) [] (units remaining.val ++ right)) := by
  simpa only [List.append_nil, show (0 : Symbol) = default from rfl,
    Tape.configuration_replicate_blank] using loop_reserved value remaining [] right

theorem realizes (value : ℕ) (right : List Symbol) :
    Tape.Steps (machine value) (2 * value + 3)
      (Tape.configuration (Fin.last value, 0) [] right)
      (Tape.configuration ((0 : Fin (value + 1)), 4) [] (units value ++ 1 :: right)) := by
  simpa only [List.append_nil, show (0 : Symbol) = default from rfl,
    Tape.configuration_replicate_blank] using realizes_reserved value [] right

end Constant
namespace Addition

abbrev State := Fin 9
instance : Inhabited State := ⟨0⟩

def machine : Turing.TM0.Machine Symbol State := fun phase symbol =>
  match phase.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write 5)
  | 2 => some (3, .move .right)
  | 3 => if symbol = 1 then some (4, .write 2) else some (3, .move .right)
  | 4 => if symbol = 5 then some (5, .write 0) else some (4, .move .left)
  | 5 => some (6, .move .right)
  | 6 => some (7, .write 0)
  | 7 => some (8, .move .right)
  | _ => none

/-- Join two unary fields using one reserved blank before them. The exit
head advances one cell; two cleared cells separate it from the unchanged caller. -/
theorem realizes_reserved (left right : ℕ) (caller tail : List Symbol) :
    Tape.Steps machine (2 * left + 9)
      (Tape.configuration 0 (0 :: caller) (units left ++ 1 :: (units right ++ 1 :: tail)))
      (Tape.configuration 8 (0 :: 0 :: caller) (units (left + right) ++ 1 :: tail)) := by
  let input := units left ++ 1 :: (units right ++ 1 :: tail)
  have move := Tape.move_left_list (machine := machine) (state := 0) (nextState := 1)
    caller input 0 (by intro symbol; rfl)
  have mark := Tape.write (machine := machine) (state := 1) (nextState := 2)
    caller input 0 5 (by rfl)
  have enter := Tape.move_right (machine := machine) (state := 2) (nextState := 3)
    caller input 5 (by rfl)
  have scan := Tape.scan_right (machine := machine) (state := 3) (units left) (5 :: caller)
    (1 :: (units right ++ 1 :: tail))
    (by intro symbol member
        have equality : symbol = 2 := List.eq_of_mem_replicate member
        subst symbol; rfl)
  simp only [UnaryMachine.units_reverse] at scan
  have join := Tape.write (machine := machine) (state := 3) (nextState := 4)
    (units left ++ 5 :: caller) (units right ++ 1 :: tail) 1 2 (by rfl)
  have back := Tape.scan_left (machine := machine) (state := 4) (units left) caller
    (units right ++ 1 :: tail) 5 2
    (by intro symbol member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · have equality : symbol = 2 := List.eq_of_mem_replicate member
          subst symbol; rfl)
  simp only [UnaryMachine.units_length, UnaryMachine.units_reverse] at back
  have clear := Tape.write (machine := machine) (state := 4) (nextState := 5) caller
    (units left ++ 2 :: (units right ++ 1 :: tail)) 5 0 (by rfl)
  have advance := Tape.move_right (machine := machine) (state := 5) (nextState := 6) caller
    (units left ++ 2 :: (units right ++ 1 :: tail)) 0 (by rfl)
  have split : units left ++ 2 :: (units right ++ 1 :: tail) =
      2 :: (units (left + right) ++ 1 :: tail) := by
    have equality : units left ++ [2] = 2 :: units left := by
      change List.replicate left (2 : Symbol) ++ [2] = 2 :: List.replicate left 2
      rw [← List.replicate_succ', List.replicate_succ]
    simpa only [UnaryMachine.units_add, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append] using congrArg (fun part => part ++ (units right ++ 1 :: tail)) equality
  rw [split] at back clear advance
  have erase := Tape.write (machine := machine) (state := 6) (nextState := 7) (0 :: caller)
    (units (left + right) ++ 1 :: tail) 2 0 (by rfl)
  have finish := Tape.move_right (machine := machine) (state := 7) (nextState := 8) (0 :: caller)
    (units (left + right) ++ 1 :: tail) 0 (by rfl)
  have trace := Tape.Steps.next move (Tape.Steps.next mark (Tape.Steps.next enter
    (scan.trans (Tape.Steps.next join (back.trans (Tape.Steps.next clear
      (Tape.Steps.next advance (Tape.Steps.next erase (Tape.Steps.next finish (.zero _))))))))))
  convert trace using 1
  · simp [UnaryMachine.units_length]; omega

/-- The empty caller recovers the original blank-left convention. -/
theorem realizes (left right : ℕ) (tail : List Symbol) :
    Tape.Steps machine (2 * left + 9)
      (Tape.configuration 0 [] (units left ++ 1 :: (units right ++ 1 :: tail)))
      (Tape.configuration 8 [] (units (left + right) ++ 1 :: tail)) := by
  have trace := realizes_reserved left right [] tail
  change Tape.Steps machine (2 * left + 9)
    (Tape.configuration 0 (List.replicate 1 default) (units left ++ 1 :: (units right ++ 1 :: tail)))
    (Tape.configuration 8 (List.replicate 2 default) (units (left + right) ++ 1 :: tail)) at trace
  simpa only [Tape.configuration_replicate_blank] using trace

end Addition
end Polytime1.SizeMachine
