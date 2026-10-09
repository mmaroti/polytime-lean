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

import Polytime.RetainedAddressMachine
import Polytime.BlockLookupMachine

/-! # Indexed scalar lookup preserving evaluator fields -/

namespace Polytime.RetainedLookupMachine

open TupleMachine

abbrev State (width : ℕ) := Sum RetainedAddressMachine.State (BlockLookupMachine.State width)

instance {width : ℕ} : Inhabited (State width) := ⟨.inl (.inl 3)⟩

variable {width : ℕ}

def machine : Turing.TM0.Machine Symbol (State width)
  | .inl state, symbol => match RetainedAddressMachine.machine state symbol with
    | some (next, action) => some (.inl next, action)
    | none => some (.inr (.inl (false, 2)), .move .left)
  | .inr state, symbol =>
    (BlockLookupMachine.machine state symbol).map fun (next, action) => (.inr next, action)

/-- Consume the selected unary address while preserving evaluator fields, then
read a scalar into the adjacent output window. Retained fields may contain
arbitrary encoded counter bits; only the two navigation markers are excluded. -/
theorem realizes (bits : Fin width → Bool) (before after : List Bool)
    (window retained left right : List Symbol)
    (windowWidth : window.length = width)
    (windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1024 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (.inl 3))
          (3 :: (window.reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (word (Binary.digits length 0) ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr .halt)))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ window
  let tail := 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)
  let caller := retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left)
  have indexFits : before.length < 2 ^ length :=
    (by dsimp [length]; omega : before.length < length).trans Nat.lt_two_pow_self
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 ∧ symbol ≠ 6 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact retainedValid symbol member
    · exact windowValid symbol member
  obtain ⟨addressTicks, addressBound, converted⟩ :=
    RetainedAddressMachine.loop before.length 0 length 0 gap left tail gapValid (by simpa using indexFits)
  have converted' := converted.rename Sum.inl (targetMachine := machine (width := width)) (by
    intro state symbol next action command
    simp [machine, command])
  have handoff := Tape.move_left_list (machine := machine (width := width))
    (state := .inl (.inr 4)) (nextState := .inr (.inl (false, 2)))
    (window.reverse ++ caller) (word (Binary.digits length before.length) ++ tail) 3
    (by intro symbol; simp [machine])
  have indexValue : Binary.value (Binary.digits length before.length) = before.length := by
    simp [Nat.mod_eq_of_lt indexFits]
  obtain ⟨readTicks, readBound, read⟩ := BlockLookupMachine.lookup_from_marker bits
    (Binary.digits length before.length) before after (window.reverse) caller right positive
    (by simpa using windowWidth) indexValue
  have read' := read.rename Sum.inr (targetMachine := machine (width := width)) (by
    intro state symbol next action command
    simp [machine, command])
  have converted'' : Tape.Steps (machine (width := width)) addressTicks
      (Tape.configuration (.inl (.inl 3))
        (3 :: (window.reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left)))
        (word (Binary.digits length 0) ++ tail))
      (Tape.configuration (.inl (.inr 4)) (3 :: (window.reverse ++ caller))
        (word (Binary.digits length before.length) ++ tail)) := by
    simpa [Tape.configuration, gap, caller, List.reverse_append, List.append_assoc] using converted'
  have read'' : Tape.Steps (machine (width := width)) readTicks
      (Tape.configuration (.inr (.inl (false, 2))) (window.reverse ++ caller)
        (3 :: (word (Binary.digits length before.length) ++ tail)))
      (Tape.configuration (.inr (.inr (.inr .halt))) caller
        (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
          4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
    simpa [Tape.configuration, tail] using read'
  have result := converted''.trans (Tape.Steps.next handoff read'')
  refine ⟨addressTicks + (readTicks + 1), ?_, ?_⟩
  · let capacity := length + retained.length + 1
    have addressCost : addressTicks ≤ 25 * capacity ^ 2 := by
      calc
        addressTicks ≤ (before.length + 1) * (3 * length + 2 * (before.length + gap.length) + 20) := by
          simpa using addressBound
        _ ≤ capacity * (5 * capacity + 20) := Nat.mul_le_mul
          (by dsimp [capacity, length]; omega)
          (by simp only [gap, List.length_append, windowWidth]; dsimp [capacity, length]; omega)
        _ ≤ 25 * capacity ^ 2 := by dsimp [capacity]; ring_nf; nlinarith
    have frameWidth : length + before.length + width + after.length + 2 = 2 * (length + 1) := by dsimp [length]; omega
    simp only [Binary.digits_length] at readBound
    rw [frameWidth] at readBound
    have cost : 96 * (2 * (length + 1)) ^ 2 = 384 * (length + 1) ^ 2 := by ring
    rw [cost] at readBound
    have readCost : readTicks ≤ 384 * capacity ^ 2 := readBound.trans (Nat.mul_le_mul_left 384
      (Nat.pow_le_pow_left (by dsimp [capacity]; omega : length + 1 ≤ capacity) 2))
    dsimp [capacity] at addressCost readCost
    ring_nf at addressCost readCost ⊢
    nlinarith
  · simpa [caller, tail] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr (.inr .halt))) symbol = none := rfl

/-- Initialize fresh or previously consumed uniform scratch, preserving retained fields. -/
theorem realizes_from_uniform (bits : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (window retained left right : List Symbol)
    (windowWidth : window.length = width)
    (windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1152 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) ticks
        (Tape.configuration (.inl 0)
          (3 :: (window.reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr .halt))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  have initialized := AddressMachine.ZeroWindow.realizes_from_uniform length inputSymbol
    (window.reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left))
    (word (before ++ List.ofFn bits ++ after) ++ right) inputValid
  obtain ⟨ticks, bound, lookup⟩ := realizes bits before after window retained left right windowWidth windowValid retainedValid positive
  have result := Tape.sequence_steps (.inl (.inl 3) : State width) initialized
    (by intro symbol; exact AddressMachine.ZeroWindow.halt symbol) lookup
  refine ⟨3 * length + 3 + (ticks + 1), ?_, ?_⟩
  · dsimp only [length]
    ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result


namespace Entry

/-- Install the unary start marker in the adjacent blank cell, replace its
separator by the address delimiter, and cross the retained fields. -/
def machine : Turing.TM0.Machine Symbol (Fin 6) := fun state symbol =>
  match state.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .write 7)
  | 2 => some (3, .move .right)
  | 3 => if symbol = 1 then some (4, .write 6) else some (3, .move .right)
  | 4 => if symbol = 3 then some (5, .move .right) else some (4, .move .right)
  | _ => none

/-- This is exactly the evaluator's result format, followed by prepared scratch.
The address is runtime data, and the retained gap is traversed without changes. -/
theorem realizes (address : ℕ) (gap right : List Symbol)
    (gapValid : ∀ symbol ∈ gap, symbol ≠ 3) :
    Tape.Steps machine (address + gap.length + 6)
      (Tape.configuration 0 [] (UnaryMachine.units address ++ 1 :: (gap ++ 3 :: right)))
      (Tape.configuration 5
        (3 :: (gap.reverse ++ 6 :: (UnaryMachine.units address ++ [7]))) right) := by
  let payload := UnaryMachine.units address ++ 1 :: (gap ++ 3 :: right)
  have back := Tape.move_left_empty (machine := machine) (state := 0) (nextState := 1)
    payload (by intro symbol; rfl)
  have mark := Tape.write (machine := machine) (state := 1) (nextState := 2) [] payload 0 7 (by rfl)
  have advance := Tape.move_right (machine := machine) (state := 2) (nextState := 3) [] payload 7 (by rfl)
  have scanAddress := Tape.scan_right (machine := machine) (state := 3) (UnaryMachine.units address)
    [7] (1 :: (gap ++ 3 :: right)) (by
      intro symbol member
      simp only [UnaryMachine.units, List.mem_replicate] at member
      rcases member with ⟨_, equality⟩
      subst symbol; rfl)
  have delimiter := Tape.write (machine := machine) (state := 3) (nextState := 4)
    (UnaryMachine.units address ++ [7]) (gap ++ 3 :: right) 1 6 (by rfl)
  have scanGap := Tape.scan_right (machine := machine) (state := 4) (6 :: gap)
    (UnaryMachine.units address ++ [7]) (3 :: right) (by
      intro symbol member
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst symbol; rfl
      · simp [machine, gapValid symbol member])
  have enter := Tape.move_right (machine := machine) (state := 4) (nextState := 5)
    (gap.reverse ++ 6 :: (UnaryMachine.units address ++ [7])) right 3 (by rfl)
  simp only [UnaryMachine.units, List.reverse_replicate, List.reverse_cons,
    List.append_assoc, List.length_replicate, List.length_cons] at scanAddress scanGap
  have result := Tape.Steps.next back (Tape.Steps.next mark (Tape.Steps.next advance
    (scanAddress.trans (Tape.Steps.next delimiter (scanGap.trans (Tape.Steps.next enter (.zero _)))))))
  convert result using 1

@[simp] theorem halt (symbol : Symbol) : machine 5 symbol = none := rfl

end Entry

/-- Start directly from a unary evaluator result, retain its intermediate and
input fields, initialize the binary scratch, and return the selected scalar. -/
theorem realizes_evaluated_address (bits : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (window retained right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (windowWidth : window.length = width)
    (windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1280 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence Entry.machine
        (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)) ticks
        (Tape.configuration (.inl 0) []
          (UnaryMachine.units before.length ++ 1 :: (retained ++ window ++ 3 ::
            (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt)))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ [7]))
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ window
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact (retainedValid symbol member).1
    · exact (windowValid symbol member).1
  have positioned := Entry.realizes before.length gap
    (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)) gapValid
  obtain ⟨ticks, bound, lookup⟩ := realizes_from_uniform bits before after inputSymbol window retained [] right
    windowWidth windowValid inputValid retainedValid positive
  have positioned' : Tape.Steps Entry.machine (before.length + retained.length + width + 6)
      (Tape.configuration 0 []
        (UnaryMachine.units before.length ++ 1 :: (retained ++ window ++ 3 ::
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))))
      (Tape.configuration 5
        (3 :: (window.reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ [7])))
        (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right))) := by
    simpa [gap, List.reverse_append, List.append_assoc, windowWidth, Nat.add_assoc] using positioned
  have result := Tape.sequence_steps (.inl 0 : Sum (Fin 4) (State width)) positioned'
    (by intro symbol; exact Entry.halt symbol) lookup
  refine ⟨before.length + retained.length + width + 6 + (ticks + 1), ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

end Polytime.RetainedLookupMachine
