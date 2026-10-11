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

import Polytime1.TupleMachine

/-! # Binary scratch counter increment

A four-state controller propagates carry, then returns to the counter's first
bit. The start marker and both neighboring regions are preserved.
-/

namespace Polytime1.CounterMachine

open TupleMachine

abbrev State := Fin 4

/-- Phases: 0 carry, 1 advance, 2 return, 3 halt. -/
def machine : Turing.TM0.Machine Symbol State := fun state symbol =>
  match state.val with
  | 0 => if symbol = data true then some (1, .write (data false))
      else if symbol = data false then some (2, .write (data true)) else none
  | 1 => some (0, .move .right)
  | 2 => if symbol = 3 then some (3, .move .right) else some (2, .move .left)
  | _ => none

/-- Each trailing one costs a write and a right move. -/
theorem carry (ones : ℕ) (left right : List Symbol) :
    Tape.Steps machine (2 * ones)
      (Tape.configuration 0 left (List.replicate ones (data true) ++ right))
      (Tape.configuration 0 (List.replicate ones (data false) ++ left) right) := by
  induction ones generalizing left with
  | zero => exact .zero _
  | succ ones hypothesis =>
    have write := Tape.write (machine := machine) (state := 0) (nextState := 1)
      left (List.replicate ones (data true) ++ right) (data true) (data false) (by rfl)
    have advance := Tape.move_right (machine := machine) (state := 1) (nextState := 0)
      left (List.replicate ones (data true) ++ right) (data false) (by rfl)
    have rest := hypothesis (data false :: left)
    have trace := Tape.Steps.next write (Tape.Steps.next advance rest)
    have changed : List.replicate ones (data false) ++ data false :: left =
        List.replicate (ones + 1) (data false) ++ left := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    rw [changed] at trace
    simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc] using trace

/-- Finish carry and rewind across the changed prefix, preserving the start
marker and all storage beyond this counter. -/
theorem finish (ones : ℕ) (rest : List Bool) (left right : List Symbol) :
    Tape.Steps machine (ones + 3)
      (Tape.configuration 0 (List.replicate ones (data false) ++ 3 :: left)
        (data false :: word rest ++ right))
      (Tape.configuration 3 (3 :: left)
        (List.replicate ones (data false) ++ data true :: word rest ++ right)) := by
  have write := Tape.write (machine := machine) (state := 0) (nextState := 2)
    (List.replicate ones (data false) ++ 3 :: left) (word rest ++ right)
    (data false) (data true) (by rfl)
  have back := Tape.scan_left (machine := machine) (state := 2)
    (List.replicate ones (data false)) left (word rest ++ right) 3 (data true) (by
      intro symbol member
      simp only [List.mem_cons, List.mem_replicate] at member
      rcases member with equality | ⟨_, equality⟩
      · subst symbol; rfl
      · subst symbol; rfl)
  simp only [List.length_replicate, List.reverse_replicate] at back
  have enter := Tape.move_right (machine := machine) (state := 2) (nextState := 3) left
    (List.replicate ones (data false) ++ data true :: (word rest ++ right)) 3 (by rfl)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Tape.Steps.next write (back.trans (Tape.Steps.next enter (.zero _)))

/-- Actual tape realization of non-overflowing fixed-width increment. -/
theorem realizes (bits : List Bool) (left right : List Symbol)
    (fits : Binary.value bits + 1 < 2 ^ bits.length) :
    ∃ ticks, ticks ≤ 3 * bits.length + 3 ∧
      Tape.Steps machine ticks
        (Tape.configuration 0 (3 :: left) (word bits ++ right))
        (Tape.configuration 3 (3 :: left) (word (Binary.increment bits) ++ right)) := by
  obtain ⟨ones, rest, split⟩ := Binary.carry_split bits fits
  have propagate := carry ones (3 :: left) (data false :: word rest ++ right)
  have ending := finish ones rest left right
  refine ⟨2 * ones + (ones + 3), ?_, ?_⟩
  · have lengthEq := congrArg List.length split
    simp only [List.length_append, List.length_replicate, List.length_cons] at lengthEq
    omega
  · simpa [split, Binary.increment_split, word] using propagate.trans ending

/-- Canonical padded binary addresses increment without changing their width. -/
theorem realizes_digits (width number : ℕ) (left right : List Symbol)
    (fits : number + 1 < 2 ^ width) :
    ∃ ticks, ticks ≤ 3 * width + 3 ∧
      Tape.Steps machine ticks
        (Tape.configuration 0 (3 :: left) (word (Binary.digits width number) ++ right))
        (Tape.configuration 3 (3 :: left) (word (Binary.digits width (number + 1)) ++ right)) := by
  have numberFits : number < 2 ^ width := by omega
  have counterValue : Binary.value (Binary.digits width number) = number := by
    simp [Nat.mod_eq_of_lt numberFits]
  obtain ⟨ticks, bound, trace⟩ := realizes (Binary.digits width number) left right (by simpa [counterValue] using fits)
  have canonical : Binary.increment (Binary.digits width number) = Binary.digits width (number + 1) := by
    apply Binary.value_length_injective
    · simp
    · rw [Binary.increment_value _ (by simpa [counterValue] using fits)]
      simp [counterValue, Nat.mod_eq_of_lt fits]
  exact ⟨ticks, by simpa using bound, by simpa only [canonical] using trace⟩

@[simp] theorem halt (symbol : Symbol) : machine 3 symbol = none := rfl

end Polytime1.CounterMachine
