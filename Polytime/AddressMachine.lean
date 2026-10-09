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

import Polytime.CounterMachine
import Polytime.UnaryMachine

/-! # Preparing padded binary addresses from bounded unary scratch values

The unary value is consumed into blanks. Its start marker, the counter marker,
and both caller contexts remain. One eight-state controller handles every width.
-/

namespace Polytime.AddressMachine

open TupleMachine

abbrev State := Sum CounterMachine.State (Fin 4)

/-- Outer phases: 0 find an unconsumed unit, 1 return to the counter,
2 return after exhaustion, 3 halt. -/
def machine : Turing.TM0.Machine Symbol State
  | .inl state, symbol =>
    if state = 3 then some (.inr 0, .move .left)
    else (CounterMachine.machine state symbol).map fun (next, action) => (.inl next, action)
  | .inr state, symbol => match state.val with
    | 0 => if symbol = data true then some (.inr 1, .write 0)
        else if symbol = 7 then some (.inr 2, .move .right) else some (.inr 0, .move .left)
    | 1 => if symbol = 3 then some (.inl 0, .move .right) else some (.inr 1, .move .right)
    | 2 => if symbol = 3 then some (.inr 3, .move .right) else some (.inr 2, .move .right)
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

/-- Convert all remaining units into increments of the padded binary counter.
Completed units are blanks; the guard stops at the unary start marker. -/
theorem loop (remaining completed width number : ℕ) (left right : List Symbol)
    (fits : number + remaining < 2 ^ width) :
    ∃ ticks, ticks ≤ (remaining + 1) * (3 * width + 2 * (completed + remaining) + 12) ∧
      Tape.Steps machine ticks
        (Tape.configuration (.inl 3)
          (3 :: (List.replicate completed 0 ++ UnaryMachine.units remaining ++ 7 :: left))
          (word (Binary.digits width number) ++ right))
        (Tape.configuration (.inr 3)
          (3 :: (List.replicate (completed + remaining) 0 ++ 7 :: left))
          (word (Binary.digits width (number + remaining)) ++ right)) := by
  induction remaining generalizing completed number with
  | zero =>
    have leave := Tape.move_left_list (machine := machine) (state := .inl 3) (nextState := .inr 0)
      (List.replicate completed 0 ++ 7 :: left) (word (Binary.digits width number) ++ right) 3
      (by intro symbol; rfl)
    have seek := Tape.scan_left (machine := machine) (state := .inr 0)
      (List.replicate completed 0) left (word (Binary.digits width number) ++ right) 7 3 (by
        intro symbol member
        simp only [List.mem_cons, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> rfl)
    simp only [List.length_replicate, List.reverse_replicate] at seek
    have turn := Tape.move_right (machine := machine) (state := .inr 0) (nextState := .inr 2)
      left (List.replicate completed 0 ++ 3 :: (word (Binary.digits width number) ++ right)) 7 (by rfl)
    have back := Tape.scan_right (machine := machine) (state := .inr 2) (List.replicate completed 0)
      (7 :: left) (3 :: (word (Binary.digits width number) ++ right)) (by
        intro symbol member
        simp only [List.mem_replicate] at member
        rcases member with ⟨_, equality⟩
        subst symbol; rfl)
    simp only [List.length_replicate, List.reverse_replicate] at back
    have enter := Tape.move_right (machine := machine) (state := .inr 2) (nextState := .inr 3)
      (List.replicate completed 0 ++ 7 :: left) (word (Binary.digits width number) ++ right) 3 (by rfl)
    have result := Tape.Steps.next leave (seek.trans (Tape.Steps.next turn
      (back.trans (Tape.Steps.next enter (.zero _)))))
    refine ⟨2 * completed + 4, by simp; omega, ?_⟩
    convert result using 1
    · omega
    · simp [UnaryMachine.units]
  | succ remaining hypothesis =>
    have leave := Tape.move_left_list (machine := machine) (state := .inl 3) (nextState := .inr 0)
      (List.replicate completed 0 ++ UnaryMachine.units (remaining + 1) ++ 7 :: left)
      (word (Binary.digits width number) ++ right) 3 (by intro symbol; rfl)
    have seek := Tape.scan_left (machine := machine) (state := .inr 0) (List.replicate completed 0)
      (UnaryMachine.units remaining ++ 7 :: left) (word (Binary.digits width number) ++ right) (data true) 3
      (by
        intro symbol member
        simp only [List.mem_cons, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> rfl)
    simp only [List.length_replicate, List.reverse_replicate] at seek
    have erase := Tape.write (machine := machine) (state := .inr 0) (nextState := .inr 1)
      (UnaryMachine.units remaining ++ 7 :: left)
      (List.replicate completed 0 ++ 3 :: (word (Binary.digits width number) ++ right)) (data true) 0 (by rfl)
    have back := Tape.scan_right (machine := machine) (state := .inr 1) (List.replicate (completed + 1) 0)
      (UnaryMachine.units remaining ++ 7 :: left) (3 :: (word (Binary.digits width number) ++ right)) (by
        intro symbol member
        simp only [List.mem_replicate] at member
        rcases member with ⟨_, equality⟩
        subst symbol; rfl)
    simp only [List.length_replicate, List.reverse_replicate] at back
    have enter := Tape.move_right (machine := machine) (state := .inr 1) (nextState := .inl 0)
      (List.replicate (completed + 1) 0 ++ UnaryMachine.units remaining ++ 7 :: left)
      (word (Binary.digits width number) ++ right) 3 (by rfl)
    have incrementFits : number + 1 < 2 ^ width := by omega
    obtain ⟨incrementTicks, incrementBound, incrementTrace⟩ := increment width number
      (List.replicate (completed + 1) 0 ++ UnaryMachine.units remaining ++ 7 :: left) right incrementFits
    obtain ⟨restTicks, restBound, restTrace⟩ := hypothesis (completed + 1) (number + 1) (by omega)
    simp only [List.append_assoc] at leave seek erase back enter incrementTrace restTrace
    have result := Tape.Steps.next leave (seek.trans (Tape.Steps.next erase
      (back.trans (Tape.Steps.next enter (incrementTrace.trans restTrace)))))
    refine ⟨2 * completed + 5 + incrementTicks + restTicks, ?_, ?_⟩
    · have restBound' : restTicks ≤ (remaining + 1) *
          (3 * width + 2 * (completed + (remaining + 1)) + 12) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restBound
      nlinarith
    · convert result using 1
      all_goals first | omega | simp [UnaryMachine.units, List.replicate_succ,
        List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Prepare an address from a bounded unary value and a zeroed binary window.
The finite controller and alphabet are independent of both values and widths. -/
theorem realizes (value width : ℕ) (left right : List Symbol) (fits : value < 2 ^ width) :
    ∃ ticks, ticks ≤ (value + 1) * (3 * width + 2 * value + 12) ∧
      Tape.Steps machine ticks
        (Tape.configuration (.inl 3) (3 :: (UnaryMachine.units value ++ 7 :: left))
          (word (Binary.digits width 0) ++ right))
        (Tape.configuration (.inr 3) (3 :: (List.replicate value 0 ++ 7 :: left))
          (word (Binary.digits width value) ++ right)) := by
  simpa using loop value 0 width 0 left right (by simpa using fits)

@[simp] theorem halt (symbol : Symbol) : machine (.inr 3) symbol = none := rfl

namespace ZeroWindow

/-- Initialize a marker-delimited blank counter window, then restore its head. -/
def machine : Turing.TM0.Machine Symbol (Fin 4) := fun state symbol =>
  match state.val with
  | 0 => if symbol = 4 then some (2, .write symbol) else some (1, .write (data false))
  | 1 => some (0, .move .right)
  | 2 => if symbol = 3 then some (3, .move .right) else some (2, .move .left)
  | _ => none

private theorem fill (length : ℕ) (inputSymbol : Symbol) (left right : List Symbol)
    (valid : inputSymbol ≠ 4) :
    Tape.Steps machine (2 * length)
      (Tape.configuration 0 left (List.replicate length inputSymbol ++ right))
      (Tape.configuration 0 (List.replicate length (data false) ++ left) right) := by
  induction length generalizing left with
  | zero => exact .zero _
  | succ length hypothesis =>
    have write := Tape.write (machine := machine) (state := 0) (nextState := 1)
      left (List.replicate length inputSymbol ++ right) inputSymbol (data false) (by simp [machine, valid])
    have advance := Tape.move_right (machine := machine) (state := 1) (nextState := 0)
      left (List.replicate length inputSymbol ++ right) (data false) (by rfl)
    have trace := Tape.Steps.next write (Tape.Steps.next advance (hypothesis (data false :: left)))
    have changed : List.replicate length (data false) ++ data false :: left =
        List.replicate (length + 1) (data false) ++ left := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    rw [changed] at trace
    simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc] using trace

/-- Reset a uniform scratch window, including the ones left by lookup, to a
canonical zero counter. Neighboring storage and the head position survive. -/
theorem realizes_from_uniform (width : ℕ) (inputSymbol : Symbol) (left right : List Symbol)
    (valid : inputSymbol ≠ 4) :
    Tape.Steps machine (3 * width + 3)
      (Tape.configuration 0 (3 :: left) (List.replicate width inputSymbol ++ 4 :: right))
      (Tape.configuration 3 (3 :: left) (word (Binary.digits width 0) ++ 4 :: right)) := by
  have initialized := fill width inputSymbol (3 :: left) (4 :: right) valid
  have turn := Tape.write (machine := machine) (state := 0) (nextState := 2)
    (List.replicate width (data false) ++ 3 :: left) right 4 4 (by rfl)
  have back := Tape.scan_left (machine := machine) (state := 2) (List.replicate width (data false))
    left right 3 4 (by
      intro symbol member
      simp only [List.mem_cons, List.mem_replicate] at member
      rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> rfl)
  simp only [List.length_replicate, List.reverse_replicate] at back
  have enter := Tape.move_right (machine := machine) (state := 2) (nextState := 3)
    left (List.replicate width (data false) ++ 4 :: right) 3 (by rfl)
  have result := initialized.trans (Tape.Steps.next turn (back.trans (Tape.Steps.next enter (.zero _))))
  have zeros : word (Binary.digits width 0) = List.replicate width (data false) := by
    have bits := Binary.zero_bits (Binary.digits width 0) (by simp)
    simpa using congrArg word bits
  convert result using 1
  · omega
  · rw [zeros]

/-- Initialize the preparer's blank cells without changing neighboring storage. -/
theorem realizes (width : ℕ) (left right : List Symbol) :
    Tape.Steps machine (3 * width + 3)
      (Tape.configuration 0 (3 :: left) (List.replicate width 0 ++ 4 :: right))
      (Tape.configuration 3 (3 :: left) (word (Binary.digits width 0) ++ 4 :: right)) :=
  realizes_from_uniform width 0 left right (by decide)

@[simp] theorem halt (symbol : Symbol) : machine 3 symbol = none := rfl

end ZeroWindow

end Polytime.AddressMachine
