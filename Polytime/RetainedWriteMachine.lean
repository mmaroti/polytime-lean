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

import Polytime.RetainedLookupMachine
import Polytime.BlockWriteMachine

/-! # Runtime address conversion followed by an indexed scalar write -/

namespace Polytime.RetainedWriteMachine

open TupleMachine

namespace PrepareWrite

abbrev State (width : ℕ) := Fin (width + 1) × Fin 3

/-- Restore the writer's counter separator and move back across the replacement
slot. Only the fixed scalar width is held in finite controller states. -/
def machine (width : ℕ) : Turing.TM0.Machine Symbol (State width) := fun (remaining, phase) symbol =>
  match phase.val with
  | 0 => some ((remaining, 1), .move .left)
  | 1 => some ((remaining, 2), .write (data false))
  | _ => if remaining.val > 0 then
      some ((⟨remaining.val - 1, by omega⟩, 2), .move .left) else none

private theorem rewind {width : ℕ} (symbols left right : List Symbol) (remaining : Fin (width + 1))
    (position : remaining.val = symbols.length) :
    Tape.Steps (machine width) symbols.length
      (Tape.configuration (remaining, 2) (symbols ++ left) right)
      (Tape.configuration (0, 2) left (symbols.reverse ++ right)) := by
  induction symbols generalizing remaining right with
  | nil =>
    have equality : remaining = 0 := Fin.ext position
    subst remaining
    exact .zero _
  | cons symbol symbols hypothesis =>
    have positive : remaining.val > 0 := by simp at position; omega
    let next : Fin (width + 1) := ⟨remaining.val - 1, by omega⟩
    have step := Tape.move_left_list (machine := machine width) (state := (remaining, 2)) (nextState := (next, 2))
      (symbols ++ left) right symbol (by intro current; simp [machine, positive, next])
    have rest := hypothesis (symbol :: right) next (by dsimp [next]; simp at position; omega)
    simpa [List.reverse_cons, List.append_assoc] using Tape.Steps.next step rest

/-- Reposition the head from the binary counter to the runtime replacement. -/
theorem realizes {width : ℕ} (bits : Fin width → Bool) (left right : List Symbol) :
    Tape.Steps (machine width) (width + 2)
      (Tape.configuration (Fin.last width, 0) (3 :: ((word (List.ofFn bits)).reverse ++ left)) right)
      (Tape.configuration (0, 2) left (word (List.ofFn bits) ++ data false :: right)) := by
  have back := Tape.move_left_list (machine := machine width) (state := (Fin.last width, 0)) (nextState := (Fin.last width, 1))
    ((word (List.ofFn bits)).reverse ++ left) right 3 (by intro current; rfl)
  have separator := Tape.write (machine := machine width) (state := (Fin.last width, 1)) (nextState := (Fin.last width, 2))
    ((word (List.ofFn bits)).reverse ++ left) right 3 (data false) (by rfl)
  have rewound := rewind (word (List.ofFn bits)).reverse left (data false :: right) (Fin.last width) (by simp)
  simpa only [List.length_reverse, word_length, List.length_ofFn, List.reverse_reverse] using
    Tape.Steps.next back (Tape.Steps.next separator rewound)

@[simp] theorem halt {width : ℕ} (symbol : Symbol) : machine width (0, 2) symbol = none := rfl

end PrepareWrite

abbrev State (width : ℕ) := Sum RetainedAddressMachine.State
  (Sum (PrepareWrite.State width) (BlockWriteMachine.State width))

variable {width : ℕ}

def machine : Turing.TM0.Machine Symbol (State width) :=
  Tape.sequence RetainedAddressMachine.machine
    (Tape.sequence (PrepareWrite.machine width) (BlockWriteMachine.machine (width := width))
      (.inl (.read 0 (fun _ => false)))) (.inl (Fin.last width, 0))

/-- Compute the padded address from unary scratch, read the replacement from
its runtime slot, and update exactly that array field. Retained fields survive. -/
theorem realizes (replacement original : Fin width → Bool) (before after : List Bool)
    (retained left right : List Symbol)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 768 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (.inl 3))
          (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (word (Binary.digits length 0) ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt)))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ word (List.ofFn replacement)
  let tail := 4 :: (word (before ++ List.ofFn original ++ after) ++ right)
  let caller := retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left)
  have indexFits : before.length < 2 ^ length :=
    (by dsimp [length]; omega : before.length < length).trans Nat.lt_two_pow_self
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 ∧ symbol ≠ 6 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact retainedValid symbol member
    · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
  obtain ⟨addressTicks, addressBound, converted⟩ := RetainedAddressMachine.loop before.length 0 length 0
    gap left tail gapValid (by simpa using indexFits)
  have converted' : Tape.Steps RetainedAddressMachine.machine addressTicks
      (Tape.configuration (.inl 3)
        (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left)))
        (word (Binary.digits length 0) ++ tail))
      (Tape.configuration (.inr 4) (3 :: ((word (List.ofFn replacement)).reverse ++ caller))
        (word (Binary.digits length before.length) ++ tail)) := by
    simpa [gap, caller, List.reverse_append, List.append_assoc] using converted
  have prepared := PrepareWrite.realizes replacement caller (word (Binary.digits length before.length) ++ tail)
  have indexValue : Binary.value (Binary.digits length before.length) = before.length := by
    simp [Nat.mod_eq_of_lt indexFits]
  obtain ⟨writeTicks, writeBound, written⟩ := BlockWriteMachine.store replacement original
    (Binary.digits length before.length) before after caller right positive indexValue
  have written' : Tape.Steps (BlockWriteMachine.machine (width := width)) writeTicks
      (Tape.configuration (.inl (.read 0 (fun _ => false))) caller
        (word (List.ofFn replacement) ++ data false :: (word (Binary.digits length before.length) ++ tail)))
      (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) caller
        (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
          4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
    simpa [tail, List.append_assoc] using written
  have writeTrace := Tape.sequence_steps (.inl (.read 0 (fun _ => false)) : BlockWriteMachine.State width)
    prepared (by intro symbol; exact PrepareWrite.halt symbol) written'
  have result := Tape.sequence_steps
    (.inl (Fin.last width, 0) : Sum (PrepareWrite.State width) (BlockWriteMachine.State width)) converted'
    (by intro symbol; exact RetainedAddressMachine.halt symbol) writeTrace
  refine ⟨addressTicks + (width + 2 + (writeTicks + 1) + 1), ?_, ?_⟩
  · let capacity := length + retained.length + 1
    have addressCost : addressTicks ≤ 25 * capacity ^ 2 := by
      calc
        addressTicks ≤ (before.length + 1) * (3 * length + 2 * (before.length + gap.length) + 20) := by simpa using addressBound
        _ ≤ capacity * (5 * capacity + 20) := Nat.mul_le_mul
          (by dsimp [capacity, length]; omega)
          (by simp only [gap, List.length_append, word_length, List.length_ofFn]; dsimp [capacity, length]; omega)
        _ ≤ 25 * capacity ^ 2 := by dsimp [capacity]; ring_nf; nlinarith
    have frameWidth : length + before.length + width + after.length + 2 = 2 * (length + 1) := by dsimp [length]; omega
    simp only [Binary.digits_length] at writeBound
    rw [frameWidth] at writeBound
    have cost : 128 * (2 * (length + 1)) ^ 2 = 512 * (length + 1) ^ 2 := by ring
    rw [cost] at writeBound
    have writeCost : writeTicks ≤ 512 * capacity ^ 2 := writeBound.trans (Nat.mul_le_mul_left 512
      (Nat.pow_le_pow_left (by dsimp [capacity]; omega : length + 1 ≤ capacity) 2))
    have widthBound : width ≤ capacity := by dsimp [capacity, length]; omega
    dsimp [capacity] at addressCost writeCost widthBound
    ring_nf at addressCost writeCost ⊢
    nlinarith
  · simpa [machine, caller, tail, Tape.configuration] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))) symbol = none := by
  simp [machine, Tape.sequence]

/-- Initialize a fresh or consumed binary window before address conversion and
the indexed write. The replacement and retained fields remain runtime tape data. -/
theorem realizes_from_uniform (replacement original : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (retained left right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 896 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) ticks
        (Tape.configuration (.inl 0)
          (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 ::
            (UnaryMachine.units before.length ++ 7 :: left)))
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ 7 :: left))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  have initialized := AddressMachine.ZeroWindow.realizes_from_uniform length inputSymbol
    ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ 7 :: left))
    (word (before ++ List.ofFn original ++ after) ++ right) inputValid
  obtain ⟨ticks, bound, write⟩ := realizes replacement original before after retained left right retainedValid positive
  have result := Tape.sequence_steps (.inl (.inl 3) : State width) initialized
    (by intro symbol; exact AddressMachine.ZeroWindow.halt symbol) write
  refine ⟨3 * length + 3 + (ticks + 1), ?_, ?_⟩
  · dsimp only [length]
    ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

/-- Accept the evaluator's unary address and retained fields, prepare navigation,
initialize scratch, and write the runtime replacement into the selected field. -/
theorem realizes_evaluated_address (replacement original : Fin width → Bool) (before after : List Bool)
    (inputSymbol : Symbol) (retained right : List Symbol)
    (inputValid : inputSymbol ≠ 4)
    (retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6)
    (positive : 0 < width) :
    let length := before.length + width + after.length
    ∃ ticks, ticks ≤ 1024 * (length + retained.length + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence RetainedLookupMachine.Entry.machine
        (Tape.sequence AddressMachine.ZeroWindow.machine (machine (width := width)) (.inl (.inl 3))) (.inl 0)) ticks
        (Tape.configuration (.inl 0) []
          (UnaryMachine.units before.length ++ 1 :: (retained ++ word (List.ofFn replacement) ++ 3 ::
            (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt)))))))))
          (retained.reverse ++ 6 :: (List.replicate before.length 0 ++ [7]))
          (word (List.ofFn replacement) ++ 3 :: (List.replicate length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  dsimp only
  let length := before.length + width + after.length
  let gap := retained ++ word (List.ofFn replacement)
  have gapValid : ∀ symbol ∈ gap, symbol ≠ 3 := by
    intro symbol member
    simp only [gap, List.mem_append] at member
    rcases member with member | member
    · exact (retainedValid symbol member).1
    · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
  have positioned := RetainedLookupMachine.Entry.realizes before.length gap
    (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)) gapValid
  obtain ⟨ticks, bound, write⟩ := realizes_from_uniform replacement original before after inputSymbol
    retained [] right inputValid retainedValid positive
  have positioned' : Tape.Steps RetainedLookupMachine.Entry.machine (before.length + retained.length + width + 6)
      (Tape.configuration 0 []
        (UnaryMachine.units before.length ++ 1 :: (retained ++ word (List.ofFn replacement) ++ 3 ::
          (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)))))
      (Tape.configuration 5
        (3 :: ((word (List.ofFn replacement)).reverse ++ retained.reverse ++ 6 :: (UnaryMachine.units before.length ++ [7])))
        (List.replicate length inputSymbol ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right))) := by
    simpa [gap, List.reverse_append, List.append_assoc, Nat.add_assoc] using positioned
  have result := Tape.sequence_steps (.inl 0 : Sum (Fin 4) (State width)) positioned'
    (by intro symbol; exact RetainedLookupMachine.Entry.halt symbol) write
  refine ⟨before.length + retained.length + width + 6 + (ticks + 1), ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa only [Tape.configuration] using result

end Polytime.RetainedWriteMachine
