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

import Polytime2.TerminatedCopy
import Polytime2.BinaryGuard
import Polytime2.Head
import Polytime2.While

/-! # Binary-indexed arrays on named tapes

Index, array, and element are argument tapes; counter and flag are private
scratch tapes. Array blocks have a specialization-fixed width. The counter
controls traversal while the input index remains unchanged.
-/

namespace Polytime2.Array

open MultiTape
open Binary (Symbol data word)

inductive TapeName | index | array | element | counter | flag
  deriving DecidableEq

instance : Fintype TapeName :=
  ⟨{.index, .array, .element, .counter, .flag}, by intro name; cases name <;> simp⟩

abbrev Alphabet (_name : TapeName) := Symbol

/-- `arrayLeft` is the logical prefix before the array head, in forward order. -/
def frame (index arrayLeft arrayRight element counter : List Bool) (flag : Bool) : Tapes Alphabet
  | .index => Binary.tape [3] (word index ++ [0]) ()
  | .array => Binary.tape (word arrayLeft.reverse ++ [3]) (word arrayRight ++ [0]) ()
  | .element => Binary.tape [3] (word element ++ [0]) ()
  | .counter => Binary.tape [3] (word counter ++ [0]) ()
  | .flag => Binary.tape [] [data flag] ()

noncomputable def guard : Machine Alphabet (Bool × Fin 3) :=
  wire (twoTapes TapeName.counter .flag (by decide)) BinaryGuard.machine

noncomputable def decrement : Machine Alphabet (Fin 3) :=
  wire (oneTape TapeName.counter) Binary.machine

noncomputable def advance (width : ℕ) : Machine Alphabet (Fin (width + 1)) :=
  wire (oneTape TapeName.array) (Move.machine width .right)

noncomputable def body (width : ℕ) : Machine Alphabet (Sum (Fin 3) (Fin (width + 1))) :=
  sequence decrement (advance width) (Fin.last width)

def result (symbols : Symbols Alphabet) : Bool := decide (symbols .flag = 2)

noncomputable def loop (width : ℕ) : Machine Alphabet
    (Sum (Bool × Fin 3) (Sum (Fin 3) (Fin (width + 1)))) :=
  whileMachine guard (body width) (false, 0) (.inl 0) result

noncomputable def prepare : Machine Alphabet (Fin 3) :=
  wire (twoTapes TapeName.index .counter (by decide)) TerminatedCopy.machine

noncomputable def transfer (width : ℕ) (write : Bool) : Machine Alphabet (Copy.State width) :=
  if write then wire (twoTapes TapeName.element .array (by decide)) (Copy.machine width)
  else wire (twoTapes TapeName.array .element (by decide)) (Copy.machine width)

noncomputable def returnArray : Machine Alphabet (Fin 2) :=
  wire (oneTape TapeName.array) BoundaryReturn.machine

abbrev SeekState (width : ℕ) :=
  Sum (Sum (Bool × Fin 3) (Sum (Fin 3) (Fin (width + 1)))) Unit

abbrev AccessState (width : ℕ) :=
  Sum (Sum (Sum (Fin 3) (SeekState width)) (Copy.State width)) (Fin 2)

/-- Copy the index, seek, transfer one element, then restore the array head. -/
noncomputable def access (width : ℕ) (write : Bool) : Machine Alphabet (AccessState width) :=
  sequence (sequence (sequence prepare (withExit (loop width)) (.inl (.inl (false, 0))))
    (transfer width write) (false, Fin.last width)) returnArray 0

@[simp] theorem access_halt (width : ℕ) (write : Bool) (symbols : Symbols Alphabet) :
    access width write (.inr 1) symbols = none := by
  simp [access, MultiTape.sequence, returnArray, wire, BoundaryReturn.machine]

/-- A mathematical array and argument values represented by a prepared frame. -/
def Represents (width : ℕ) (index element counter : List Bool) (flag : Bool)
    (blocks : List (List Bool)) (tapes : Tapes Alphabet) : Prop :=
  (∀ block ∈ blocks, block.length = width) ∧ element.length = width ∧
    counter.length = index.length ∧ tapes = frame index [] blocks.flatten element counter flag

theorem prepare_steps (index arrayLeft arrayRight element counter : List Bool) (flag : Bool)
    (sameLength : counter.length = index.length) :
    Steps prepare (2 * index.length + 3)
      (0, frame index arrayLeft arrayRight element counter flag)
      (2, frame index arrayLeft arrayRight element index flag) := by
  let wiring := twoTapes TapeName.index .counter (by decide)
  have localTrace := TerminatedCopy.steps index (word counter) (by simpa [word] using sameLength) [] [] [] []
  have trace := wire_steps wiring TerminatedCopy.machine localTrace
    (frame index arrayLeft arrayRight element counter flag) (by intro name; cases name <;> rfl)
  have restored : install wiring (Copy.frame [3] (word index ++ [0]) [3] (word index ++ [0]))
      (frame index arrayLeft arrayRight element counter flag) = frame index arrayLeft arrayRight element index flag := by
    funext name
    cases name <;> simp [wiring, frame, Copy.frame, Binary.tape, Function.update]
  simpa only [prepare, wiring, restored] using trace

theorem transfer_steps (width : ℕ) (write : Bool) (block element : List Bool)
    (blockLength : block.length = width) (elementLength : element.length = width)
    (index arrayLeft arrayRight counter : List Bool) (flag : Bool) :
    let chosen := if write then element else block
    Steps (transfer width write) (2 * width + 1)
      ((false, Fin.last width), frame index arrayLeft (block ++ arrayRight) element counter flag)
      ((true, 0), frame index arrayLeft (chosen ++ arrayRight) chosen counter flag) := by
  cases write with
  | false =>
    let wiring := twoTapes TapeName.array .element (by decide)
    have localTrace := Copy.steps width (word block) (word element)
      (by simpa [word] using blockLength) (by simpa [word] using elementLength)
      (word arrayLeft.reverse ++ [3]) (word arrayRight ++ [0]) [3] [0]
    have trace := wire_steps wiring (Copy.machine width) localTrace
      (frame index arrayLeft (block ++ arrayRight) element counter flag)
      (by intro name; cases name <;> simp [wiring, frame, Copy.frame, Binary.tape, word, List.map_append, List.append_assoc])
    have restored : install wiring
        (Copy.frame (word arrayLeft.reverse ++ [3]) (word block ++ (word arrayRight ++ [0])) [3] (word block ++ [0]))
        (frame index arrayLeft (block ++ arrayRight) element counter flag) =
        frame index arrayLeft (block ++ arrayRight) block counter flag := by
      funext name
      cases name <;> simp [wiring, frame, Copy.frame, Binary.tape, Function.update, word, List.map_append, List.append_assoc]
    simpa only [transfer, Bool.false_eq_true, ite_false, wiring, restored] using trace
  | true =>
    let wiring := twoTapes TapeName.element .array (by decide)
    have localTrace := Copy.steps width (word element) (word block)
      (by simpa [word] using elementLength) (by simpa [word] using blockLength)
      [3] [0] (word arrayLeft.reverse ++ [3]) (word arrayRight ++ [0])
    have trace := wire_steps wiring (Copy.machine width) localTrace
      (frame index arrayLeft (block ++ arrayRight) element counter flag)
      (by intro name; cases name <;> simp [wiring, frame, Copy.frame, Binary.tape, word, List.map_append, List.append_assoc])
    have restored : install wiring
        (Copy.frame [3] (word element ++ [0]) (word arrayLeft.reverse ++ [3]) (word element ++ (word arrayRight ++ [0])))
        (frame index arrayLeft (block ++ arrayRight) element counter flag) =
        frame index arrayLeft (element ++ arrayRight) element counter flag := by
      funext name
      cases name <;> simp [wiring, frame, Copy.frame, Binary.tape, Function.update, word, List.map_append, List.append_assoc]
    simpa only [transfer, eq_self, ite_true, wiring, restored] using trace

theorem returnArray_steps (index arrayLeft arrayRight element counter : List Bool) (flag : Bool) :
    Steps returnArray (arrayLeft.length + 2)
      (0, frame index arrayLeft arrayRight element counter flag)
      (1, frame index [] (arrayLeft ++ arrayRight) element counter flag) := by
  have localTrace : Steps BoundaryReturn.machine (arrayLeft.length + 2)
      (0, Binary.tape (word arrayLeft.reverse ++ [3]) (word arrayRight ++ [0]))
      (1, Binary.tape [3] (word (arrayLeft ++ arrayRight) ++ [0])) := by
    cases arrayRight with
    | nil =>
      simpa [word, List.map_reverse, List.reverse_reverse] using
        BoundaryReturn.steps arrayLeft.reverse 0 (by decide) [] []
    | cons bit bits =>
      have notMarker : data bit ≠ 3 := by cases bit <;> decide
      simpa [word, List.map_reverse, List.reverse_reverse, List.map_append, List.append_assoc] using
        BoundaryReturn.steps arrayLeft.reverse (data bit) notMarker [] (word bits ++ [0])
  have trace := wire_steps (oneTape TapeName.array) BoundaryReturn.machine localTrace
    (frame index arrayLeft arrayRight element counter flag) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.array) (Binary.tape [3] (word (arrayLeft ++ arrayRight) ++ [0]))
      (frame index arrayLeft arrayRight element counter flag) =
      frame index [] (arrayLeft ++ arrayRight) element counter flag := by
    funext name
    cases name <;> simp [frame, Binary.tape, Function.update, word]
  simpa only [returnArray, restored] using trace

theorem guard_steps (index arrayLeft arrayRight element counter : List Bool) (flag : Bool) :
    Steps guard (2 * counter.length + 3)
      ((false, 0), frame index arrayLeft arrayRight element counter flag)
      ((false, 2), frame index arrayLeft arrayRight element counter (counter.any id)) := by
  let wiring := twoTapes TapeName.counter .flag (by decide)
  have localTrace := BinaryGuard.steps counter [] [] [] [] (data flag)
  have trace := wire_steps wiring BinaryGuard.machine localTrace
    (frame index arrayLeft arrayRight element counter flag) (by intro name; cases name <;> rfl)
  have restored : install wiring
      (Copy.frame [3] (word counter ++ [0]) [] [data (counter.any id)])
      (frame index arrayLeft arrayRight element counter flag) =
      frame index arrayLeft arrayRight element counter (counter.any id) := by
    funext name
    cases name <;> simp [wiring, install_two, frame, Copy.frame, Binary.tape, Function.update]
  simpa only [guard, wiring, restored] using trace

theorem decrement_steps (index arrayLeft arrayRight element counter : List Bool) (flag : Bool)
    (positive : 0 < Binary.value counter) :
    ∃ ticks, ticks ≤ 2 * counter.length + 3 ∧ Steps decrement ticks
      (0, frame index arrayLeft arrayRight element counter flag)
      (2, frame index arrayLeft arrayRight element (Binary.decrement counter) flag) := by
  obtain ⟨ticks, cost, localTrace⟩ := Binary.steps counter positive [] [0]
  have trace := wire_steps (oneTape TapeName.counter) Binary.machine localTrace
    (frame index arrayLeft arrayRight element counter flag) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.counter)
      (Binary.tape [3] (word (Binary.decrement counter) ++ [0]))
      (frame index arrayLeft arrayRight element counter flag) =
      frame index arrayLeft arrayRight element (Binary.decrement counter) flag := by
    funext name
    cases name <;> simp [frame, Binary.tape, Function.update]
  exact ⟨ticks, cost, by simpa only [decrement, restored] using trace⟩

theorem advance_steps (width : ℕ) (block : List Bool) (blockLength : block.length = width)
    (index arrayLeft arrayRight element counter : List Bool) (flag : Bool) :
    Steps (advance width) width
      (Fin.last width, frame index arrayLeft (block ++ arrayRight) element counter flag)
      (0, frame index (arrayLeft ++ block) arrayRight element counter flag) := by
  let initial := Binary.tape (word arrayLeft.reverse ++ [3]) (word (block ++ arrayRight) ++ [0])
  let final := Binary.tape (word (arrayLeft ++ block).reverse ++ [3]) (word arrayRight ++ [0])
  have moved : (fun name : Unit => (Turing.Tape.move .right)^[width] (initial name)) = final := by
    funext name
    have movement := Move.right_list (word block) (word arrayLeft.reverse ++ [3]) (word arrayRight ++ [0])
    simpa [initial, final, Binary.tape, word, blockLength, List.map_append, List.reverse_append,
      List.map_reverse, List.append_assoc] using movement
  have localTrace := Move.steps width .right initial
  rw [moved] at localTrace
  have trace := wire_steps (oneTape TapeName.array) (Move.machine width .right) localTrace
    (frame index arrayLeft (block ++ arrayRight) element counter flag) (by intro name; cases name; rfl)
  have restored : install (oneTape TapeName.array) final
      (frame index arrayLeft (block ++ arrayRight) element counter flag) =
      frame index (arrayLeft ++ block) arrayRight element counter flag := by
    funext name
    cases name <;> simp [final, frame, Binary.tape, Function.update]
  simpa only [advance, restored] using trace

theorem body_steps (width : ℕ) (block : List Bool) (blockLength : block.length = width)
    (index arrayLeft arrayRight element counter : List Bool) (flag : Bool)
    (positive : 0 < Binary.value counter) :
    ∃ ticks, ticks ≤ 2 * counter.length + width + 4 ∧ Steps (body width) ticks
      (.inl 0, frame index arrayLeft (block ++ arrayRight) element counter flag)
      (.inr 0, frame index (arrayLeft ++ block) arrayRight element (Binary.decrement counter) flag) := by
  obtain ⟨ticks, cost, decremented⟩ := decrement_steps index arrayLeft (block ++ arrayRight) element counter flag positive
  have moved := advance_steps width block blockLength index arrayLeft arrayRight element (Binary.decrement counter) flag
  have halt (symbols : Symbols Alphabet) : decrement 2 symbols = none := by simp [decrement, wire, Binary.machine]
  exact ⟨ticks + width + 1, by omega, sequence_steps decrement (advance width) (Fin.last width) decremented halt moved⟩

private theorem loop_zero_steps (width : ℕ) (index arrayLeft arrayRight element counter : List Bool)
    (flag : Bool) (zero : Binary.value counter = 0) :
    Steps (loop width) (2 * counter.length + 3)
      (.inl (false, 0), frame index arrayLeft arrayRight element counter flag)
      (.inl (false, 2), frame index arrayLeft arrayRight element (List.replicate counter.length false) false) := by
  have trace := (guard_steps index arrayLeft arrayRight element counter flag).rename Sum.inl
    (target := loop width)
    (by intro state symbols next actions transition; simp [loop, whileMachine, transition])
  have digits := Binary.eq_zero_digits counter zero
  have stopped : counter.any id = false := by
    cases tested : counter.any id with
    | false => rfl
    | true => have positive := (BinaryGuard.any_iff_positive counter).mp tested; omega
  simpa only [stopped, ← digits] using trace

/-- The binary counter advances over exactly its numeric value in array blocks.
The input index and element tapes are untouched. Zero-width blocks are allowed. -/
theorem loop_steps (width : ℕ) (index element : List Bool) (blocks : List (List Bool))
    (blockWidths : ∀ block ∈ blocks, block.length = width)
    (arrayLeft counter : List Bool) (flag : Bool) (bounded : Binary.value counter ≤ blocks.length) :
    ∃ ticks, ticks ≤ (Binary.value counter + 1) * (4 * counter.length + width + 12) ∧
      Steps (loop width) ticks
        (.inl (false, 0), frame index arrayLeft blocks.flatten element counter flag)
        (.inl (false, 2), frame index (arrayLeft ++ (blocks.take (Binary.value counter)).flatten)
          (blocks.drop (Binary.value counter)).flatten element (List.replicate counter.length false) false) := by
  induction blocks generalizing arrayLeft counter flag with
  | nil =>
    have zero : Binary.value counter = 0 := by simpa using bounded
    refine ⟨2 * counter.length + 3, ?_, ?_⟩
    · simp only [zero, zero_add, one_mul]; omega
    · simpa [zero] using loop_zero_steps width index arrayLeft [] element counter flag zero
  | cons block blocks hypothesis =>
    by_cases zero : Binary.value counter = 0
    · refine ⟨2 * counter.length + 3, ?_, ?_⟩
      · simp only [zero, zero_add, one_mul]; omega
      · simpa [zero] using loop_zero_steps width index arrayLeft (block :: blocks).flatten element counter flag zero
    · have positive : 0 < Binary.value counter := by omega
      have active : counter.any id = true := (BinaryGuard.any_iff_positive counter).mpr positive
      have currentWidth : block.length = width := blockWidths block (by simp)
      have remainingWidths : ∀ next ∈ blocks, next.length = width := by
        intro next member; exact blockWidths next (by simp [member])
      have progress := Binary.decrement_value counter positive
      have smaller : Binary.value (Binary.decrement counter) ≤ blocks.length := by simp at bounded; omega
      obtain ⟨restTicks, restCost, restTrace⟩ :=
        hypothesis remainingWidths (arrayLeft ++ block) (Binary.decrement counter) true smaller
      have guardTrace := (guard_steps index arrayLeft (block :: blocks).flatten element counter flag).rename Sum.inl
        (target := loop width)
        (by intro state symbols next actions transition; simp [loop, whileMachine, transition])
      rw [active] at guardTrace
      obtain ⟨bodyTicks, bodyCost, bodyTrace⟩ :=
        body_steps width block currentWidth index arrayLeft blocks.flatten element counter true positive
      have liftedBody := bodyTrace.rename Sum.inr (target := loop width)
        (by intro state symbols next actions transition; simp [loop, whileMachine, transition])
      have toBody : step (loop width)
          (.inl (false, 2), frame index arrayLeft (block :: blocks).flatten element counter true) =
          some (.inr (.inl 0), frame index arrayLeft (block :: blocks).flatten element counter true) := by
        simp [step, loop, whileMachine, guard, wire, BinaryGuard.machine, result, MultiTape.read, frame, Binary.tape, data]
      have toGuard : step (loop width)
          (.inr (.inr 0), frame index (arrayLeft ++ block) blocks.flatten element (Binary.decrement counter) true) =
          some (.inl (false, 0), frame index (arrayLeft ++ block) blocks.flatten element (Binary.decrement counter) true) := by
        simp [step, loop, whileMachine, body, MultiTape.sequence, advance, wire, Move.machine]
      have trace := guardTrace.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      refine ⟨2 * counter.length + 3 + (bodyTicks + (restTicks + 1) + 1), ?_, ?_⟩
      · simp only [Binary.decrement_length, progress] at restCost
        calc
          2 * counter.length + 3 + (bodyTicks + (restTicks + 1) + 1) ≤
              (4 * counter.length + width + 12) + Binary.value counter * (4 * counter.length + width + 12) := by omega
          _ = (Binary.value counter + 1) * (4 * counter.length + width + 12) := by ring
      · have count : Binary.value counter = Binary.value (Binary.decrement counter) + 1 := progress.symm
        simpa only [count, List.take_succ_cons, List.drop_succ_cons, List.flatten_cons,
          Binary.decrement_length, List.append_assoc] using trace

theorem blocks_length (width : ℕ) (blocks : List (List Bool))
    (widths : ∀ block ∈ blocks, block.length = width) : blocks.flatten.length = blocks.length * width := by
  induction blocks with
  | nil => simp
  | cons block blocks hypothesis =>
    have current := widths block (by simp)
    have remaining := hypothesis (by intro next member; exact widths next (by simp [member]))
    simp [List.flatten_cons, current, remaining, Nat.add_mul, Nat.add_comm]

/-- Complete access, preserving the index and restoring all argument heads.
Read mode returns the selected block; write mode replaces just that block. -/
theorem access_steps (width : ℕ) (write : Bool) (index element counter : List Bool) (flag : Bool)
    (before after : List (List Bool)) (block : List Bool)
    (widths : ∀ entry ∈ before ++ block :: after, entry.length = width)
    (elementLength : element.length = width) (counterLength : counter.length = index.length)
    (indexValue : Binary.value index = before.length) :
    let chosen := if write then element else block
    ∃ ticks,
      ticks ≤ (Binary.value index + 1) * (4 * index.length + width + 12) +
        Binary.value index * width + 2 * index.length + 2 * width + 10 ∧
      Steps (access width write) ticks
        (.inl (.inl (.inl 0)), frame index [] (before ++ block :: after).flatten element counter flag)
        (.inr 1, frame index [] (before ++ chosen :: after).flatten chosen (List.replicate index.length false) false) := by
  dsimp only
  let chosen := if write then element else block
  have currentWidth : block.length = width := widths block (by simp)
  have beforeWidths : ∀ entry ∈ before, entry.length = width := by
    intro entry member; exact widths entry (by simp [member])
  have prefixLength := blocks_length width before beforeWidths
  have prepared := prepare_steps index [] (before ++ block :: after).flatten element counter flag counterLength
  obtain ⟨loopTicks, loopCost, traversed⟩ := loop_steps width index element (before ++ block :: after)
    widths [] index flag (by simp [indexValue])
  have traversed' : Steps (loop width) loopTicks
      (.inl (false, 0), frame index [] (before ++ block :: after).flatten element index flag)
      (.inl (false, 2), frame index before.flatten (block ++ after.flatten) element (List.replicate index.length false) false) := by
    simpa [indexValue] using traversed
  have loopHalt : step (loop width)
      (.inl (false, 2), frame index before.flatten (block ++ after.flatten) element (List.replicate index.length false) false) = none := by
    simp [step, loop, whileMachine, guard, wire, BinaryGuard.machine, result, MultiTape.read, frame, Binary.tape, data]
  have sought := withExit_steps (loop width) traversed' loopHalt
  have prepareHalt (symbols : Symbols Alphabet) : prepare 2 symbols = none := by
    simp [prepare, wire, TerminatedCopy.machine]
  have first := sequence_steps prepare (withExit (loop width)) (.inl (.inl (false, 0))) prepared prepareHalt sought
  have transferred := transfer_steps width write block element currentWidth elementLength
    index before.flatten after.flatten (List.replicate index.length false) false
  have firstHalt (symbols : Symbols Alphabet) :
      sequence prepare (withExit (loop width)) (.inl (.inl (false, 0))) (.inr (.inr ())) symbols = none := by
    simp [MultiTape.sequence, withExit]
  have second := sequence_steps (sequence prepare (withExit (loop width)) (.inl (.inl (false, 0))))
    (transfer width write) (false, Fin.last width) first firstHalt transferred
  have restored := returnArray_steps index before.flatten (chosen ++ after.flatten) chosen (List.replicate index.length false) false
  have secondHalt (symbols : Symbols Alphabet) :
      sequence (sequence prepare (withExit (loop width)) (.inl (.inl (false, 0))))
        (transfer width write) (false, Fin.last width) (.inr (true, 0)) symbols = none := by
    cases write <;> simp [MultiTape.sequence, transfer, wire, Copy.machine]
  have computation := sequence_steps _ returnArray 0 second secondHalt restored
  refine ⟨((2 * index.length + 3 + (loopTicks + 1) + 1) + (2 * width + 1) + 1) + (before.flatten.length + 2) + 1, ?_, ?_⟩
  · rw [prefixLength, ← indexValue]
    omega
  · simpa only [access, List.flatten_append, List.flatten_cons, List.append_assoc] using computation

theorem lookup_steps (width : ℕ) (index element counter : List Bool) (flag : Bool)
    (blocks : List (List Bool)) (widths : ∀ block ∈ blocks, block.length = width)
    (valid : Binary.value index < blocks.length)
    (elementLength : element.length = width) (counterLength : counter.length = index.length) :
    ∃ ticks, ticks ≤ (Binary.value index + 1) * (4 * index.length + width + 12) +
      Binary.value index * width + 2 * index.length + 2 * width + 10 ∧
      Steps (access width false) ticks
        (.inl (.inl (.inl 0)), frame index [] blocks.flatten element counter flag)
        (.inr 1, frame index [] blocks.flatten blocks[Binary.value index] (List.replicate index.length false) false) := by
  have split : blocks.take (Binary.value index) ++ blocks[Binary.value index] :: blocks.drop (Binary.value index + 1) = blocks := by
    rw [← List.drop_eq_getElem_cons valid, List.take_append_drop]
  have trace := access_steps width false index element counter flag
    (blocks.take (Binary.value index)) (blocks.drop (Binary.value index + 1)) blocks[Binary.value index]
    (by simpa only [split] using widths) elementLength counterLength (by simp [Nat.min_eq_left valid.le])
  simpa only [Bool.false_eq_true, ite_false, split] using trace

theorem update_steps (width : ℕ) (index element counter : List Bool) (flag : Bool)
    (blocks : List (List Bool)) (widths : ∀ block ∈ blocks, block.length = width)
    (valid : Binary.value index < blocks.length)
    (elementLength : element.length = width) (counterLength : counter.length = index.length) :
    ∃ ticks, ticks ≤ (Binary.value index + 1) * (4 * index.length + width + 12) +
      Binary.value index * width + 2 * index.length + 2 * width + 10 ∧
      Steps (access width true) ticks
        (.inl (.inl (.inl 0)), frame index [] blocks.flatten element counter flag)
        (.inr 1, frame index [] (blocks.set (Binary.value index) element).flatten element (List.replicate index.length false) false) := by
  have split : blocks.take (Binary.value index) ++ blocks[Binary.value index] :: blocks.drop (Binary.value index + 1) = blocks := by
    rw [← List.drop_eq_getElem_cons valid, List.take_append_drop]
  have replaced : blocks.take (Binary.value index) ++ element :: blocks.drop (Binary.value index + 1) =
      blocks.set (Binary.value index) element := by
    simpa only [valid, ite_true] using
      (List.set_eq_take_append_cons_drop (l := blocks) (i := Binary.value index) (a := element)).symm
  have trace := access_steps width true index element counter flag
    (blocks.take (Binary.value index)) (blocks.drop (Binary.value index + 1)) blocks[Binary.value index]
    (by simpa only [split] using widths) elementLength counterLength (by simp [Nat.min_eq_left valid.le])
  simpa only [eq_self, ite_true, split, replaced] using trace

-- parameterLevel: size names bounding the number of array entries and index digits.
universe parameterLevel

/-- One controller and polynomial work for every runtime array and valid binary index.
The read/write mode and element width are fixed before all runtime data. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    (width : ℕ) (write : Bool) (arrayCapacity digitCapacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment index element counter flag (blocks : List (List Bool)),
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity →
        index.length ≤ MvPolynomial.eval assignment digitCapacity →
        (∀ block ∈ blocks, block.length = width) →
        ∀ valid : Binary.value index < blocks.length,
          element.length = width → counter.length = index.length →
          ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
            Steps (access width write) ticks
              (.inl (.inl (.inl 0)), frame index [] blocks.flatten element counter flag)
              (.inr 1, frame index []
                (if write then blocks.set (Binary.value index) element else blocks).flatten
                (if write then element else blocks[Binary.value index]) (List.replicate index.length false) false) := by
  refine ⟨(arrayCapacity + 1) * (4 * digitCapacity + MvPolynomial.C (width + 12)) +
    MvPolynomial.C width * arrayCapacity + 2 * digitCapacity + MvPolynomial.C (2 * width + 10), ?_⟩
  intro assignment index element counter flag blocks arrayBound digitBound widths valid elementLength counterLength
  have indexBound : Binary.value index ≤ MvPolynomial.eval assignment arrayCapacity := valid.le.trans arrayBound
  have workBound : 4 * index.length + width + 12 ≤
      4 * MvPolynomial.eval assignment digitCapacity + (width + 12) := by omega
  have loopBound := Nat.mul_le_mul (Nat.add_le_add_right indexBound 1) workBound
  have addressBound : Binary.value index * width ≤ width * MvPolynomial.eval assignment arrayCapacity := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right width indexBound
  have run : ∃ ticks, ticks ≤ (Binary.value index + 1) * (4 * index.length + width + 12) +
      Binary.value index * width + 2 * index.length + 2 * width + 10 ∧
      Steps (access width write) ticks
        (.inl (.inl (.inl 0)), frame index [] blocks.flatten element counter flag)
        (.inr 1, frame index []
          (if write then blocks.set (Binary.value index) element else blocks).flatten
          (if write then element else blocks[Binary.value index]) (List.replicate index.length false) false) := by
    cases write with
    | false => simpa using lookup_steps width index element counter flag blocks widths valid elementLength counterLength
    | true => simpa using update_steps width index element counter flag blocks widths valid elementLength counterLength
  obtain ⟨ticks, cost, trace⟩ := run
  refine ⟨ticks, ?_, trace⟩
  simp only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_C]
  omega

/-- Certified lookup/update with a contract for every represented mathematical input.
The universal postcondition avoids relying on a chosen decomposition of the bits. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (width : ℕ) (write : Bool) (arrayCapacity digitCapacity : MvPolynomial Parameter ℕ) :
    Realizes (access width write) (.inl (.inl (.inl 0))) (.inr 1)
      (fun assignment initial => ∃ index element counter flag blocks,
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity ∧
          index.length ≤ MvPolynomial.eval assignment digitCapacity ∧
          Represents width index element counter flag blocks initial ∧ Binary.value index < blocks.length)
      (fun _ initial final => ∀ index element counter flag blocks,
        Represents width index element counter flag blocks initial →
          ∀ valid : Binary.value index < blocks.length,
            final = frame index []
              (if write then blocks.set (Binary.value index) element else blocks).flatten
              (if write then element else blocks[Binary.value index]) (List.replicate index.length false) false) := by
  obtain ⟨bound, runs⟩ := polynomial_time width write arrayCapacity digitCapacity
  refine ⟨access_halt width write, bound, ?_⟩
  intro assignment initial valid
  obtain ⟨index, element, counter, flag, blocks, arrayBound, digitBound,
    ⟨widths, elementLength, counterLength, rfl⟩, selected⟩ := valid
  obtain ⟨ticks, cost, trace⟩ := runs assignment index element counter flag blocks
    arrayBound digitBound widths selected elementLength counterLength
  refine ⟨ticks, _, cost, trace, ?_⟩
  intro otherIndex otherElement otherCounter otherFlag otherBlocks otherRepresentation otherSelected
  obtain ⟨otherWidths, otherElementLength, otherCounterLength, agreement⟩ := otherRepresentation
  have otherRun : ∃ otherTicks, Steps (access width write) otherTicks
      (.inl (.inl (.inl 0)), frame otherIndex [] otherBlocks.flatten otherElement otherCounter otherFlag)
      (.inr 1, frame otherIndex []
        (if write then otherBlocks.set (Binary.value otherIndex) otherElement else otherBlocks).flatten
        (if write then otherElement else otherBlocks[Binary.value otherIndex]) (List.replicate otherIndex.length false) false) := by
    cases write with
    | false =>
      obtain ⟨count, _, computation⟩ := lookup_steps width otherIndex otherElement otherCounter otherFlag
        otherBlocks otherWidths otherSelected otherElementLength otherCounterLength
      exact ⟨count, by simpa using computation⟩
    | true =>
      obtain ⟨count, _, computation⟩ := update_steps width otherIndex otherElement otherCounter otherFlag
        otherBlocks otherWidths otherSelected otherElementLength otherCounterLength
      exact ⟨count, by simpa using computation⟩
  obtain ⟨otherTicks, otherTrace⟩ := otherRun
  have otherTrace' : Steps (access width write) otherTicks
      (.inl (.inl (.inl 0)), frame index [] blocks.flatten element counter flag)
      (.inr 1, frame otherIndex []
        (if write then otherBlocks.set (Binary.value otherIndex) otherElement else otherBlocks).flatten
        (if write then otherElement else otherBlocks[Binary.value otherIndex]) (List.replicate otherIndex.length false) false) := by
    rw [agreement]
    exact otherTrace
  exact congrArg Prod.snd (trace.final_eq otherTrace' (by simp [step]) (by simp [step]))

end Polytime2.Array
