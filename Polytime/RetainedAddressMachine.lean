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

import Polytime.AddressMachine

/-! # Address conversion across retained evaluator fields

A delimiter separates the consumable unary address from a preserved gap holding
intermediate fields, the original counters, and the scalar output window.
-/

namespace Polytime.RetainedAddressMachine

open TupleMachine

abbrev State := Sum CounterMachine.State (Fin 5)

/-- Outer phases: find the delimiter, consume an address unit, return for an
increment, return after exhaustion, and halt. -/
def machine : Turing.TM0.Machine Symbol State
  | .inl state, symbol =>
    if state = 3 then some (.inr 0, .move .left)
    else (CounterMachine.machine state symbol).map fun (next, action) => (.inl next, action)
  | .inr state, symbol => match state.val with
    | 0 => if symbol = 6 then some (.inr 1, .write symbol) else some (.inr 0, .move .left)
    | 1 => if symbol = data true then some (.inr 2, .write 0)
        else if symbol = 7 then some (.inr 3, .move .right) else some (.inr 1, .move .left)
    | 2 => if symbol = 3 then some (.inl 0, .move .right) else some (.inr 2, .move .right)
    | 3 => if symbol = 3 then some (.inr 4, .move .right) else some (.inr 3, .move .right)
    | _ => none

private theorem increment (width number : ℕ) (left right : List Symbol)
    (fits : number + 1 < 2 ^ width) :
    ∃ ticks, ticks ≤ 3 * width + 3 ∧ Tape.Steps machine ticks
      (Tape.configuration (.inl 0) (3 :: left) (word (Binary.digits width number) ++ right))
      (Tape.configuration (.inl 3) (3 :: left) (word (Binary.digits width (number + 1)) ++ right)) := by
  obtain ⟨ticks, bound, trace⟩ := CounterMachine.realizes_digits width number left right fits
  have lifted := trace.rename Sum.inl (targetMachine := machine) (by
    intro state symbol next action command
    by_cases halted : state = 3
    · subst state; simp at command
    · simp [machine, halted, command])
  exact ⟨ticks, bound, lifted⟩

/-- Retained fields are traversed on each iteration but are never altered.
Neither their length nor their values enter the finite controller. -/
theorem loop (remaining completed width number : ℕ) (gap left right : List Symbol)
    (gapValid : ∀ symbol ∈ gap, symbol ≠ 3 ∧ symbol ≠ 6)
    (fits : number + remaining < 2 ^ width) :
    ∃ ticks, ticks ≤ (remaining + 1) * (3 * width + 2 * (completed + remaining + gap.length) + 20) ∧
      Tape.Steps machine ticks
        (Tape.configuration (.inl 3)
          (3 :: (gap.reverse ++ 6 :: (List.replicate completed 0 ++ UnaryMachine.units remaining ++ 7 :: left)))
          (word (Binary.digits width number) ++ right))
        (Tape.configuration (.inr 4)
          (3 :: (gap.reverse ++ 6 :: (List.replicate (completed + remaining) 0 ++ 7 :: left)))
          (word (Binary.digits width (number + remaining)) ++ right)) := by
  induction remaining generalizing completed number with
  | zero =>
    let rest := List.replicate completed 0 ++ 7 :: left
    let tail := word (Binary.digits width number) ++ right
    have leave := Tape.move_left_list (machine := machine) (state := .inl 3) (nextState := .inr 0)
      (gap.reverse ++ 6 :: rest) tail 3 (by intro symbol; rfl)
    have seekGap := Tape.scan_left (machine := machine) (state := .inr 0) gap.reverse rest tail 6 3 (by
      intro symbol member
      simp only [List.mem_cons, List.mem_reverse] at member
      rcases member with equality | member
      · subst symbol; rfl
      · simp [machine, (gapValid symbol member).2])
    have switch := Tape.write (machine := machine) (state := .inr 0) (nextState := .inr 1)
      rest (gap ++ 3 :: tail) 6 6 (by rfl)
    have seek := Tape.scan_left (machine := machine) (state := .inr 1)
      (List.replicate completed 0) left (gap ++ 3 :: tail) 7 6 (by
        intro symbol member
        simp only [List.mem_cons, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> rfl)
    have turn := Tape.move_right (machine := machine) (state := .inr 1) (nextState := .inr 3)
      left (List.replicate completed 0 ++ 6 :: (gap ++ 3 :: tail)) 7 (by rfl)
    have back := Tape.scan_right (machine := machine) (state := .inr 3)
      (List.replicate completed 0 ++ 6 :: gap) (7 :: left) (3 :: tail) (by
        intro symbol member
        simp only [List.mem_append, List.mem_cons, List.mem_replicate] at member
        rcases member with ⟨_, equality⟩ | equality | member
        · subst symbol; rfl
        · subst symbol; rfl
        · simp [machine, (gapValid symbol member).1])
    have enter := Tape.move_right (machine := machine) (state := .inr 3) (nextState := .inr 4)
      (gap.reverse ++ 6 :: (List.replicate completed 0 ++ 7 :: left)) tail 3 (by rfl)
    simp only [List.reverse_reverse, List.reverse_replicate, List.length_reverse,
      List.length_replicate, List.length_append, List.length_cons, List.reverse_append,
      List.reverse_cons, List.append_assoc] at leave seekGap switch seek turn back enter
    have result := Tape.Steps.next leave (seekGap.trans (Tape.Steps.next switch
      (seek.trans (Tape.Steps.next turn (back.trans (Tape.Steps.next enter (.zero _)))))))
    refine ⟨2 * completed + 2 * gap.length + 7, by simp; omega, ?_⟩
    convert result using 1
    · omega
    · simp [rest, tail, UnaryMachine.units]
  | succ remaining hypothesis =>
    let rest := List.replicate completed 0 ++ UnaryMachine.units (remaining + 1) ++ 7 :: left
    let tail := word (Binary.digits width number) ++ right
    have leave := Tape.move_left_list (machine := machine) (state := .inl 3) (nextState := .inr 0)
      (gap.reverse ++ 6 :: rest) tail 3 (by intro symbol; rfl)
    have seekGap := Tape.scan_left (machine := machine) (state := .inr 0) gap.reverse rest tail 6 3 (by
      intro symbol member
      simp only [List.mem_cons, List.mem_reverse] at member
      rcases member with equality | member
      · subst symbol; rfl
      · simp [machine, (gapValid symbol member).2])
    have switch := Tape.write (machine := machine) (state := .inr 0) (nextState := .inr 1)
      rest (gap ++ 3 :: tail) 6 6 (by rfl)
    have seek := Tape.scan_left (machine := machine) (state := .inr 1) (List.replicate completed 0)
      (UnaryMachine.units remaining ++ 7 :: left) (gap ++ 3 :: tail) (data true) 6 (by
        intro symbol member
        simp only [List.mem_cons, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> rfl)
    have erase := Tape.write (machine := machine) (state := .inr 1) (nextState := .inr 2)
      (UnaryMachine.units remaining ++ 7 :: left)
      (List.replicate completed 0 ++ 6 :: (gap ++ 3 :: tail)) (data true) 0 (by rfl)
    have back := Tape.scan_right (machine := machine) (state := .inr 2)
      (List.replicate (completed + 1) 0 ++ 6 :: gap) (UnaryMachine.units remaining ++ 7 :: left)
      (3 :: tail) (by
        intro symbol member
        simp only [List.mem_append, List.mem_cons, List.mem_replicate] at member
        rcases member with ⟨_, equality⟩ | equality | member
        · subst symbol; rfl
        · subst symbol; rfl
        · simp [machine, (gapValid symbol member).1])
    have enter := Tape.move_right (machine := machine) (state := .inr 2) (nextState := .inl 0)
      (gap.reverse ++ 6 :: (List.replicate (completed + 1) 0 ++ UnaryMachine.units remaining ++ 7 :: left)) tail 3 (by rfl)
    obtain ⟨incrementTicks, incrementBound, incrementTrace⟩ := increment width number
      (gap.reverse ++ 6 :: (List.replicate (completed + 1) 0 ++ UnaryMachine.units remaining ++ 7 :: left)) right (by omega)
    obtain ⟨restTicks, restBound, restTrace⟩ := hypothesis (completed + 1) (number + 1) (by omega)
    simp only [List.reverse_reverse, List.reverse_replicate, List.length_reverse,
      List.length_replicate, List.length_append, List.length_cons, List.reverse_append,
      List.reverse_cons, List.append_assoc] at leave seekGap switch seek erase back enter incrementTrace restTrace
    simp only [rest, UnaryMachine.units, List.replicate_succ, List.append_assoc]
      at leave seekGap switch seek erase back enter incrementTrace restTrace
    have result := Tape.Steps.next leave (seekGap.trans (Tape.Steps.next switch
      (seek.trans (Tape.Steps.next erase (back.trans (Tape.Steps.next enter (incrementTrace.trans restTrace)))))))
    refine ⟨2 * completed + 2 * gap.length + 8 + incrementTicks + restTicks, ?_, ?_⟩
    · have restBound' : restTicks ≤ (remaining + 1) *
          (3 * width + 2 * (completed + (remaining + 1) + gap.length) + 20) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restBound
      nlinarith
    · convert result using 1
      all_goals first | omega | simp [tail, UnaryMachine.units, List.replicate_succ,
        List.append_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem halt (symbol : Symbol) : machine (.inr 4) symbol = none := rfl

end Polytime.RetainedAddressMachine
