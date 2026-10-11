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

import Polytime1.AddressMachine
import Polytime1.BlockLookupMachine

/-! # Address conversion and indexed lookup in one prepared frame

The scalar output window and a bounded unary address precede a zeroed binary
window. Conversion consumes the unary scratch, then installs the lookup cursor.
-/

namespace Polytime1.AddressLookupMachine

open TupleMachine

abbrev State (width : ℕ) := Sum AddressMachine.State (BlockLookupMachine.State width)

instance {width : ℕ} : Inhabited (State width) := ⟨.inl (.inl 3)⟩

variable {width : ℕ}

/-- Conversion halts at the binary counter. One left move transfers control
at its start marker to the existing scalar reader. -/
def machine : Turing.TM0.Machine Symbol (State width)
  | .inl state, symbol => match AddressMachine.machine state symbol with
    | some (next, action) => some (.inl next, action)
    | none => some (.inr (.inl (false, 2)), .move .left)
  | .inr state, symbol =>
    (BlockLookupMachine.machine state symbol).map fun (next, action) => (.inr next, action)

/-- Convert a bounded unary address, install the cursor, and read its complete
field, preserving the array and both caller contexts. Both tape controllers
are fixed before array length and address vary. -/
theorem realizes (bits : Fin width → Bool) (before after : List Bool) (left right : List Symbol)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 512 * (length + 1) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (.inl 3))
          (3 :: (List.replicate width 0 ++ UnaryMachine.units before.length ++ 7 :: left))
          (word (Binary.digits length 0) ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr .halt)))
          (List.replicate before.length 0 ++ 7 :: left)
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let tail := 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)
  let scratch := List.replicate before.length 0 ++ 7 :: left
  let reserved : List Symbol := List.replicate width 0
  have indexFits : before.length < 2 ^ length := (by dsimp [length]; omega : before.length < length).trans Nat.lt_two_pow_self
  obtain ⟨addressTicks, addressBound, converted⟩ := AddressMachine.loop before.length width length 0 left tail
    (by simpa using indexFits)
  have converted' := converted.rename Sum.inl (targetMachine := machine (width := width)) (by
    intro state symbol next action command
    simp [machine, command])
  have handoff := Tape.move_left_list (machine := machine (width := width))
    (state := .inl (.inr 3)) (nextState := .inr (.inl (false, 2)))
    (reserved ++ scratch) (word (Binary.digits length before.length) ++ tail) 3
    (by intro symbol; simp [machine])
  have indexValue : Binary.value (Binary.digits length before.length) = before.length := by
    simp [Nat.mod_eq_of_lt indexFits]
  obtain ⟨readTicks, readBound, read⟩ := BlockLookupMachine.lookup_from_marker bits
    (Binary.digits length before.length) before after reserved scratch right positive
    (by simp [reserved]) indexValue
  have read' := read.rename Sum.inr (targetMachine := machine (width := width)) (by
    intro state symbol next action command
    simp [machine, command])
  have converted'' : Tape.Steps (machine (width := width)) addressTicks
      (Tape.configuration (.inl (.inl 3))
        (3 :: (reserved ++ UnaryMachine.units before.length ++ 7 :: left))
        (word (Binary.digits length 0) ++ tail))
      (Tape.configuration (.inl (.inr 3)) (3 :: (reserved ++ scratch))
        (word (Binary.digits length before.length) ++ tail)) := by
    simpa [Tape.configuration, reserved, scratch, List.append_assoc, ← List.replicate_append_replicate] using converted'
  have read'' : Tape.Steps (machine (width := width)) readTicks
      (Tape.configuration (.inr (.inl (false, 2))) (reserved ++ scratch)
        (3 :: (word (Binary.digits length before.length) ++ tail)))
      (Tape.configuration (.inr (.inr (.inr .halt))) scratch
        (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
          4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
    simpa [Tape.configuration, tail, Binary.digits_length] using read'
  have result := converted''.trans (Tape.Steps.next handoff read'')
  refine ⟨addressTicks + (readTicks + 1), ?_, ?_⟩
  · have addressCost : addressTicks ≤ 12 * (length + 1) ^ 2 := by
      calc
        addressTicks ≤ (before.length + 1) * (3 * length + 2 * (width + before.length) + 12) := addressBound
        _ ≤ (length + 1) * (5 * length + 12) :=
          Nat.mul_le_mul (by dsimp [length]; omega) (by dsimp [length]; omega)
        _ ≤ 12 * (length + 1) ^ 2 := by ring_nf; nlinarith
    have frameWidth : length + before.length + width + after.length + 2 = 2 * (length + 1) := by dsimp [length]; omega
    simp only [Binary.digits_length] at readBound
    rw [frameWidth] at readBound
    have cost : 96 * (2 * (length + 1)) ^ 2 = 384 * (length + 1) ^ 2 := by ring
    rw [cost] at readBound
    ring_nf at addressCost readBound ⊢
    nlinarith
  · simpa [reserved, scratch, tail] using result

/-- Initialize blank scratch, convert the unary address, and read the field.
The caller supplies neither encoded zero bits nor a binary address. -/
theorem realizes_from_blank (bits : Fin width → Bool) (before after : List Bool)
    (left right : List Symbol) (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 640 * (length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) ticks
        (Tape.configuration (.inl 0)
          (3 :: (List.replicate width 0 ++ UnaryMachine.units before.length ++ 7 :: left))
          (List.replicate length 0 ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr .halt))))
          (List.replicate before.length 0 ++ 7 :: left)
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  have initialized := AddressMachine.ZeroWindow.realizes length
    (List.replicate width 0 ++ UnaryMachine.units before.length ++ 7 :: left)
    (word (before ++ List.ofFn bits ++ after) ++ right)
  obtain ⟨ticks, bound, lookup⟩ := realizes bits before after left right positive
  have result := Tape.sequence_steps (.inl (.inl 3) : State width) initialized
    (by intro symbol; exact AddressMachine.ZeroWindow.halt symbol) lookup
  refine ⟨3 * length + 3 + (ticks + 1), ?_, ?_⟩
  · dsimp only [length]
    ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr (.inr .halt))) symbol = none := rfl

namespace PositionCursor

/-- Cross a forward-stored unary address and blank output slot, stopping just
after the binary-window marker. The controller does not know their lengths. -/
def machine : Turing.TM0.Machine Symbol (Fin 2)
  | 0, symbol => if symbol = 3 then some (1, .move .right) else some (0, .move .right)
  | _, _ => none

theorem realizes (address outputWidth : ℕ) (left right : List Symbol) :
    Tape.Steps machine (address + outputWidth + 2)
      (Tape.configuration 0 left
        (7 :: (UnaryMachine.units address ++ List.replicate outputWidth 0 ++ 3 :: right)))
      (Tape.configuration 1
        (3 :: (List.replicate outputWidth 0 ++ UnaryMachine.units address ++ 7 :: left)) right) := by
  let segment : List Symbol := 7 :: (UnaryMachine.units address ++ List.replicate outputWidth 0)
  have scanned := Tape.scan_right (machine := machine) (state := 0) segment left (3 :: right) (by
    intro symbol member
    have different : symbol ≠ 3 := by
      simp only [segment, List.mem_cons, List.mem_append, UnaryMachine.units,
        List.mem_replicate] at member
      rcases member with equality | ⟨_, equality⟩ | ⟨_, equality⟩ <;> subst symbol <;> decide
    simp [machine, different])
  have entered := Tape.move_right (machine := machine) (state := 0) (nextState := 1)
    (segment.reverse ++ left) right 3 (by simp [machine])
  simpa [segment, UnaryMachine.units, List.reverse_append, List.reverse_cons,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    scanned.trans (Tape.Steps.next entered (.zero _))

@[simp] theorem halt (symbol : Symbol) : machine 1 symbol = none := rfl

end PositionCursor

/-- Forward-stored address fields can enter the same lookup pipeline without
requiring a prepositioned tape head. All positioning costs are included. -/
theorem realizes_forward_address (bits : Fin width → Bool) (before after : List Bool)
    (left right : List Symbol) (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 704 * (length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence PositionCursor.machine
        (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)) ticks
        (Tape.configuration (.inl 0) left
          (7 :: (UnaryMachine.units before.length ++ List.replicate width 0 ++ 3 ::
            (List.replicate length 0 ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt)))))
          (List.replicate before.length 0 ++ 7 :: left)
          (word (List.ofFn bits) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  have positioned := PositionCursor.realizes before.length width left
    (List.replicate length 0 ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right))
  obtain ⟨ticks, bound, lookup⟩ := realizes_from_blank bits before after left right positive
  have result := Tape.sequence_steps
    (.inl 0 : Sum (Fin 4) (State width)) positioned
    (by intro symbol; exact PositionCursor.halt symbol) lookup
  refine ⟨before.length + width + 2 + (ticks + 1), ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

end Polytime1.AddressLookupMachine
