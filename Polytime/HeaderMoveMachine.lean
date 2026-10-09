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

import Polytime.HeaderResetMachine
import Polytime.SizeMachine

/-! # Moving runtime header fields

Copy a selected field to the front, then remove its original occurrence.
The field position fixes the controller, while every counter value is runtime
data. In particular, moving the second field exchanges two runtime row indices.
-/

namespace Polytime.HeaderMoveMachine

open UnaryMachine (Symbol units fields)

namespace RemoveZero

abbrev State (position : ℕ) := Sum (Fin (position + 1)) (Symbol × Fin 8)

def machine (position : ℕ) : Turing.TM0.Machine Symbol (State position) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else some (.inr (0, 0), .write 0)
  | .inr (carried, phase) =>
    match phase.val with
    | 0 => some (.inr (0, 1), .move .left)
    | 1 => if symbol = 0 then some (.inr (0, 6), .move .right)
        else some (.inr (symbol, 2), .write 0)
    | 2 => some (.inr (carried, 3), .move .right)
    | 3 => some (.inr (carried, 4), .write carried)
    | 4 => some (.inr (carried, 5), .move .left)
    | 5 => some (.inr (0, 1), .move .left)
    | 6 => some (.inr (0, 7), .move .right)
    | _ => none

variable {position : ℕ}

private theorem carry (cells : List Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position) (5 * cells.length)
      (Tape.configuration (.inr (0, 1)) cells.tail (cells.headD 0 :: 0 :: tail))
      (Tape.configuration (.inr (0, 1)) [] (0 :: 0 :: (cells.reverse ++ tail))) := by
  induction cells generalizing tail with
  | nil => exact .zero _
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have write := Tape.write (machine := machine position) (state := .inr (0, 1))
      (nextState := .inr (symbol, 2)) cells (0 :: tail) symbol 0 (by simp [machine, distinct])
    have right := Tape.move_right (machine := machine position) (state := .inr (symbol, 2))
      (nextState := .inr (symbol, 3)) cells (0 :: tail) 0 (by rfl)
    have copy := Tape.write (machine := machine position) (state := .inr (symbol, 3))
      (nextState := .inr (symbol, 4)) (0 :: cells) tail 0 symbol (by rfl)
    have left := Tape.move_left (machine := machine position) (state := .inr (symbol, 4))
      (nextState := .inr (symbol, 5)) cells tail 0 symbol (by rfl)
    have next := Tape.move_left_headD (machine := machine position) (state := .inr (symbol, 5))
      (nextState := .inr (0, 1)) cells (symbol :: tail) 0 (by rfl)
    have rest := hypothesis (symbol :: tail) (by intro current member; exact valid current (by simp [member]))
    have trace := Tape.Steps.next write (Tape.Steps.next right (Tape.Steps.next copy
      (Tape.Steps.next left (Tape.Steps.next next rest))))
    convert trace using 1 <;> simp [List.reverse_cons, List.append_assoc]

private theorem skip (values : List ℕ) (remaining : Fin (position + 1))
    (count : remaining.val = values.length) (left tail : List Symbol) :
    Tape.Steps (machine position) (fields values).length
      (Tape.configuration (.inl remaining) left (fields values ++ tail))
      (Tape.configuration (.inl 0) ((fields values).reverse ++ left) tail) := by
  induction values generalizing remaining left with
  | nil =>
    have equality : remaining = 0 := Fin.ext count
    subst remaining
    simp only [fields, List.flatMap_nil, List.nil_append, List.reverse_nil]
    exact .zero _
  | cons value values hypothesis =>
    have positive : remaining.val > 0 := by simp at count; omega
    let next : Fin (position + 1) := ⟨remaining.val - 1, by omega⟩
    have scan := Tape.scan_right (machine := machine position) (state := .inl remaining)
      (units value) left (1 :: (fields values ++ tail)) (by
        intro symbol member
        have equality := List.eq_of_mem_replicate member
        subst symbol; simp [machine, positive])
    have advance := Tape.move_right (machine := machine position) (state := .inl remaining)
      (nextState := .inl next) ((units value).reverse ++ left) (fields values ++ tail) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by dsimp [next]; simp at count; omega)
      (1 :: ((units value).reverse ++ left))
    have trace := scan.trans (Tape.Steps.next advance rest)
    simpa [UnaryMachine.fields_cons, List.reverse_append, List.append_assoc] using trace

/-- Remove the separator of a zero field, shifting only its prefix right. -/
theorem realizes (prior : List ℕ) (tail : List Symbol) :
    Tape.Steps (machine prior.length) (6 * (fields prior).length + 4)
      (Tape.configuration (.inl (Fin.last prior.length)) [] (fields (prior ++ [0]) ++ tail))
      (Tape.configuration (.inr (0, 7)) [] (fields prior ++ tail)) := by
  have skipped := skip prior (Fin.last prior.length) (by simp) [] (1 :: tail)
  simp only [List.append_nil] at skipped
  have erase := Tape.write (machine := machine prior.length) (state := .inl 0)
    (nextState := .inr (0, 0)) (fields prior).reverse tail 1 0 (by rfl)
  have enter := Tape.move_left_headD (machine := machine prior.length) (state := .inr (0, 0))
    (nextState := .inr (0, 1)) (fields prior).reverse tail 0 (by rfl)
  have shifted := carry (position := prior.length) (fields prior).reverse tail (by
    intro symbol member
    rcases UnaryMachine.fields_symbols prior symbol (List.mem_reverse.mp member) with equality | equality <;>
      subst symbol <;> decide)
  have move := Tape.move_right (machine := machine prior.length) (state := .inr (0, 1))
    (nextState := .inr (0, 6)) [] (0 :: (fields prior ++ tail)) 0 (by rfl)
  have blank : Tape.configuration (.inr (0, 6) : State prior.length) [0] (0 :: (fields prior ++ tail)) =
      Tape.configuration (.inr (0, 6) : State prior.length) [] (0 :: (fields prior ++ tail)) :=
    Tape.configuration_append_blank (Symbol := Symbol) _ [] _
  rw [blank] at move
  have last := Tape.move_right (machine := machine prior.length) (state := .inr (0, 6))
    (nextState := .inr (0, 7)) [] (fields prior ++ tail) 0 (by rfl)
  have lastBlank : Tape.configuration (.inr (0, 7) : State prior.length) [0] (fields prior ++ tail) =
      Tape.configuration (.inr (0, 7) : State prior.length) [] (fields prior ++ tail) :=
    Tape.configuration_append_blank (Symbol := Symbol) _ [] _
  rw [lastBlank] at last
  simp only [List.reverse_reverse] at shifted
  have trace := skipped.trans (Tape.Steps.next erase (Tape.Steps.next enter
    (shifted.trans (Tape.Steps.next move (Tape.Steps.next last (.zero _))))))
  convert trace using 1 <;> simp [fields, units, List.flatMap_append, List.append_assoc]
  omega

@[simp] theorem halt (symbol : Symbol) : machine position (.inr (0, 7)) symbol = none := rfl

end RemoveZero

/-- Remove one complete unary field, leaving its prefix and suffix intact. -/
def remove (position : ℕ) := Tape.sequence
  (HeaderResetMachine.machine position) (RemoveZero.machine position) (.inl (Fin.last position))

theorem removes (prior : List ℕ) (value : ℕ) (tail : List Symbol) :
    Tape.Steps (remove prior.length)
      (value * (6 * (fields prior).length + 4) + 8 * (fields prior).length + 7)
      (Tape.configuration (.inl (.inl (Fin.last prior.length))) [] (fields (prior ++ [value]) ++ tail))
      (Tape.configuration (.inr (.inr (0, 7))) [] (fields prior ++ tail)) := by
  have reset := HeaderResetMachine.realizes prior value tail
  have deleted := RemoveZero.realizes prior tail
  have trace := Tape.sequence_steps (Sum.inl (Fin.last prior.length) : RemoveZero.State prior.length)
    reset HeaderResetMachine.halt deleted
  convert trace using 1 <;> simp [remove, Tape.configuration]
  omega

@[simp] theorem remove_halt (position : ℕ) (symbol : Symbol) :
    remove position (.inr (.inr (0, 7))) symbol = none := by simp [remove, Tape.sequence, RemoveZero.halt]

/-- Finite control for copying a selected header field and deleting its old occurrence. -/
abbrev State (position : ℕ) := Sum (SizeMachine.Copy.State position)
  (Sum (HeaderResetMachine.State (position + 1)) (RemoveZero.State (position + 1)))

/-- Move the selected field to the front without retaining a duplicate. -/
def machine (position : ℕ) := Tape.sequence (SizeMachine.Copy.machine position)
  (remove (position + 1)) (.inl (.inl (Fin.last (position + 1))))

/-- Runtime counter relocation preserves the suffix and clears left storage.
The transition bound is polynomial in the total original header length. -/
theorem realizes (before after : List ℕ) (value : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ 128 * ((fields (before ++ value :: after)).length + 1) ^ 2 ∧
      Tape.Steps (machine before.length) ticks
        (Tape.configuration (.inl (Fin.last before.length, 0)) [] (fields (before ++ value :: after) ++ tail))
        (Tape.configuration (.inr (.inr (.inr (0, 7)))) [] (fields (value :: before ++ after) ++ tail)) := by
  obtain ⟨copyTicks, copyCost, copied⟩ := SizeMachine.Copy.realizes before after value tail
  have removed := removes (value :: before) value (fields after ++ tail)
  have removed' : Tape.Steps (remove (before.length + 1))
      (value * (6 * (fields (value :: before)).length + 4) + 8 * (fields (value :: before)).length + 7)
      (Tape.configuration (.inl (.inl (Fin.last (before.length + 1)))) []
        (fields (value :: before ++ value :: after) ++ tail))
      (Tape.configuration (.inr (.inr (0, 7))) [] (fields (value :: before ++ after) ++ tail)) := by
    simpa [fields, List.flatMap_append, List.append_assoc, Nat.add_comm] using removed
  have copyHalt (symbol : Symbol) : SizeMachine.Copy.machine before.length (0, 19) symbol = none := by
    simp [SizeMachine.Copy.machine, UnaryMachine.machine]
  have trace := Tape.sequence_steps
    (Sum.inl (Sum.inl (Fin.last (before.length + 1))) :
      Sum (HeaderResetMachine.State (before.length + 1)) (RemoveZero.State (before.length + 1)))
    copied copyHalt removed'
  refine ⟨copyTicks +
    (value * (6 * (fields (value :: before)).length + 4) + 8 * (fields (value :: before)).length + 7 + 1), ?_, ?_⟩
  · let length := (fields (before ++ value :: after)).length + 1
    have prefixBound : (fields (value :: before)).length ≤ length := by
      simp [length, fields, List.flatMap_append, List.length_flatMap]
      omega
    have valueBound : value ≤ length := by
      simp [length, fields, List.flatMap_append, List.length_flatMap]
      omega
    have deletionCost := Nat.mul_le_mul valueBound
      (Nat.add_le_add_right (Nat.mul_le_mul_left 6 prefixBound) 4)
    have prefixCost := Nat.mul_le_mul_left 8 prefixBound
    have positive : 1 ≤ length := by dsimp [length]; omega
    change copyTicks ≤ 64 * length ^ 2 at copyCost
    change _ ≤ 128 * length ^ 2
    nlinarith
  · simpa only [machine, Tape.configuration] using trace

@[simp] theorem halt (position : ℕ) (symbol : Symbol) :
    machine position (.inr (.inr (.inr (0, 7)))) symbol = none := by
  simp [machine, Tape.sequence, remove_halt]

/-- Exchange source and target row counters while retaining a shared column
counter, the column count, and all scalar/counter/matrix storage in `tail`. -/
theorem swaps_row_indices (first second column columns : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ 128 * (first + second + column + columns + 5) ^ 2 ∧
      Tape.Steps (machine 1) ticks
        (Tape.configuration (.inl (Fin.last 1, 0)) [] (fields [first, second, column, columns] ++ tail))
        (Tape.configuration (.inr (.inr (.inr (0, 7)))) [] (fields [second, first, column, columns] ++ tail)) := by
  obtain ⟨ticks, cost, trace⟩ := realizes [first] [column, columns] second tail
  refine ⟨ticks, ?_, ?_⟩
  · simpa [fields, Nat.add_assoc] using cost
  · simpa using trace

end Polytime.HeaderMoveMachine
