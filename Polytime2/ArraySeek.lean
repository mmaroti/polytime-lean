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

import Polytime2.ArrayCounter
import Polytime2.StandardBinaryGuard
import Polytime2.StandardTapeCommands
import Polytime2.StandardHead

/-! # Shared binary-indexed array navigation

A certified block-advance command supplies the element width. The counter loop,
guard, cleanup, and execution proof are shared by static and runtime widths.
Additional immutable tapes belong to the block-advance command.
-/

namespace Polytime2.ArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)


variable {tapeCount : ℕ} [Fact (4 ≤ tapeCount)] {AdvanceState : Type}

private instance tapeCount_neZero : NeZero tapeCount := by
  have minimum : 4 ≤ tapeCount := Fact.out
  exact ⟨by omega⟩

abbrev Alphabet (tapeCount : ℕ) := CallingConvention.Alphabet (Fin tapeCount)

@[simp] private theorem small_mod (value : ℕ) (small : value < 4) :
    value % tapeCount = value := Nat.mod_eq_of_lt (by have minimum : 4 ≤ tapeCount := Fact.out; omega)

/-- Counter, decrement scratch, guard bit, and array cursor. -/
def frame (context : Tapes (Alphabet tapeCount)) (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) : Tapes (Alphabet tapeCount) := fun name =>
  if name = 0 then buffer (word counter)
  else if name = 1 then buffer scratch
  else if name = 2 then buffer [flag]
  else if name = 3 then array else context name

def widths (extraWidths : Fin tapeCount → ℕ) (digits arrayWidth : ℕ) (name : Fin tapeCount) : ℕ :=
  if name = 3 then arrayWidth else if name = 2 then 1
  else if name = 0 ∨ name = 1 then digits else extraWidths name

def readOnly (name : Fin tapeCount) : Bool := decide (3 ≤ name.val)

def position (offset : ℤ) (name : Fin tapeCount) : ℤ := if name = 3 then offset else 0

def counterWiring : Fin 2 ↪ Fin tapeCount :=
  ⟨(fun name => ⟨name.val, by have minimum : 4 ≤ tapeCount := Fact.out; omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin tapeCount => name.val) equal)⟩

def guardWiring : Bool ↪ Fin tapeCount :=
  ⟨(fun name => if name then 2 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all [Fin.ext_iff, -Fin.val_eq_zero_iff]⟩

@[simp] theorem counterWiring_apply (name : Fin 2) : counterWiring (tapeCount := tapeCount) name = ⟨name.val, by have minimum : 4 ≤ tapeCount := Fact.out; omega⟩ := rfl
@[simp] theorem guardWiring_apply (name : Bool) : guardWiring (tapeCount := tapeCount) name = (if name then 2 else 0) := rfl

@[simp] private theorem counterWiring_val (name : Fin 2) :
    (counterWiring (tapeCount := tapeCount) name).val = name.val := rfl
@[simp] private theorem counterWiring_zero : counterWiring (tapeCount := tapeCount) 0 = 0 := rfl
@[simp] private theorem counterWiring_one : counterWiring (tapeCount := tapeCount) 1 = 1 := by
  apply Fin.ext
  rw [counterWiring_val]
  change 1 = 1 % tapeCount
  simp

noncomputable def counter : Machine (Alphabet tapeCount) ArrayCounter.State := MultiTape.wire counterWiring ArrayCounter.machine
abbrev BodyState (AdvanceState : Type) := Sum ArrayCounter.State AdvanceState

noncomputable def body (advance : Machine (Alphabet tapeCount) AdvanceState) (advanceEntry : AdvanceState) :
    Machine (Alphabet tapeCount) (BodyState AdvanceState) :=
  MultiTape.sequence counter advance advanceEntry

def bodyEntry (AdvanceState : Type) : BodyState AdvanceState := .inl ArrayCounter.entry
def bodyExit (advanceExit : AdvanceState) : BodyState AdvanceState := .inr advanceExit

variable (context : Tapes (Alphabet tapeCount)) (extraWidths : Fin tapeCount → ℕ)

private theorem counter_positions (offset : ℤ) :
    install counterWiring (fun _ : Fin 2 => (0 : ℤ)) (position offset) = position (tapeCount := tapeCount) offset := by
  funext name
  by_cases first : name = 0
  · subst name
    change install counterWiring _ _ (counterWiring 0) = _
    rw [install_at]
    simp [position, Fin.ext_iff, -Fin.val_eq_zero_iff]
  by_cases second : name = 1
  · subst name
    rw [← counterWiring_one, install_at]
    simp [position, Fin.ext_iff, -Fin.val_eq_zero_iff]
  apply install_outside
  rintro ⟨localName, equal⟩
  fin_cases localName
  all_goals
    first
    | exact first (equal.symm.trans counterWiring_zero)
    | exact second (equal.symm.trans counterWiring_one)

private theorem counter_install (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (oldCounter : List Bool) (oldScratch : List Symbol) :
    install counterWiring (ArrayCounter.frame counter scratch) (frame context oldCounter oldScratch flag array) =
      frame context counter scratch flag array := by
  funext name
  by_cases first : name = 0
  · subst name
    change install counterWiring _ _ (counterWiring 0) = _
    rw [install_at]
    simp [frame, ArrayCounter.frame, -Fin.val_eq_zero_iff]
  by_cases second : name = 1
  · subst name
    rw [← counterWiring_one, install_at]
    simp [frame, ArrayCounter.frame, Fin.ext_iff, -Fin.val_eq_zero_iff]
  rw [install_outside _ _ _ _ (by
    rintro ⟨localName, equal⟩
    fin_cases localName
    all_goals
      first
      | exact first (equal.symm.trans counterWiring_zero)
      | exact second (equal.symm.trans counterWiring_one))]
  simp only [frame, first, second, ↓reduceIte]

variable (advance : Machine (Alphabet tapeCount) AdvanceState) (advanceEntry advanceExit : AdvanceState)
variable (elementWidth advanceTicks : ℕ)
variable (advanceRuns : ∀ (bits : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ),
  Runs (widths extraWidths bits.length arrayWidth) readOnly advance advanceTicks
    advanceEntry (position offset) (frame context bits scratch flag array)
    advanceExit (position (offset + elementWidth))
    (frame context bits scratch flag ((Turing.Tape.move .right)^[elementWidth] array)))
variable (advanceHalt : ∀ symbols, advance advanceExit symbols = none)

/- Decrement private storage, then advance the immutable array by one element. -/
include advanceRuns in
theorem body_runs (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths extraWidths bits.length arrayWidth) readOnly (body advance advanceEntry)
      (4 * bits.length + advanceTicks + 7)
      (bodyEntry AdvanceState) (position offset) (frame context bits scratch flag array)
      (bodyExit advanceExit) (position (offset + elementWidth))
      (frame context (Binary.decrement bits) (word (Binary.decrement bits)) flag
        ((Turing.Tape.move .right)^[elementWidth] array)) := by
  have decremented := (ArrayCounter.runs bits scratch sameLength).wire counterWiring
    (widths extraWidths bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> simp only [counterWiring_apply, widths, Fin.ext_iff, Fin.val_zero] <;> norm_num)
    (by intro name premise; fin_cases name <;> simp only [readOnly, counterWiring_val] at premise <;> norm_num at premise)
    (frame context bits scratch flag array) (position offset)
  rw [counter_positions, counter_install, counter_install] at decremented
  have moved := advanceRuns (Binary.decrement bits) (word (Binary.decrement bits)) flag array arrayWidth offset
  simp only [Binary.decrement_length] at moved
  have complete := decremented.sequence advance advanceEntry
    (by intro symbols; simp [MultiTape.wire, ArrayCounter.machine, ArrayCounter.exit, MultiTape.sequence,
      ArrayCounter.copyBack, StandardTapeCommands.copy, StandardTerminatedCopy.machine]) moved
  convert complete using 1 <;> first | rfl | omega


noncomputable def guard : Machine (Alphabet tapeCount) StandardBinaryGuard.State :=
  MultiTape.wire guardWiring StandardBinaryGuard.machine

def result (symbols : Symbols (Alphabet tapeCount)) : Bool := symbols 2 == 2

abbrev LoopState (AdvanceState : Type) := Sum StandardBinaryGuard.State (BodyState AdvanceState)

noncomputable def loop (advance : Machine (Alphabet tapeCount) AdvanceState) (advanceEntry : AdvanceState) :
    Machine (Alphabet tapeCount) (LoopState AdvanceState) :=
  MultiTape.whileMachine guard (body advance advanceEntry) (false, 0) (bodyEntry AdvanceState) result

private theorem guard_positions (offset : ℤ) :
    install guardWiring (fun _ : Bool => (0 : ℤ)) (position offset) = position (tapeCount := tapeCount) offset := by
  funext name
  by_cases first : name = 0
  · subst name
    change install guardWiring _ _ (guardWiring false) = _
    rw [install_at]
    simp [position, Fin.ext_iff, -Fin.val_eq_zero_iff]
  by_cases flag : name = 2
  · subst name
    change install guardWiring _ _ (guardWiring true) = _
    rw [install_at]
    simp [position, Fin.ext_iff, -Fin.val_eq_zero_iff]
  apply install_outside
  rintro ⟨localName, equal⟩
  change (if localName then 2 else 0) = name at equal
  cases localName <;> simp_all

private theorem guard_install (bits : List Bool) (scratch : List Symbol) (flag newFlag : Symbol)
    (array : Turing.Tape Symbol) :
    install guardWiring (Copy.frame [0] (word bits ++ [0]) [0] [newFlag, 0])
      (frame context bits scratch flag array) = frame context bits scratch newFlag array := by
  funext name
  by_cases first : name = 0
  · subst name
    change install guardWiring _ _ (guardWiring false) = _
    rw [install_at]
    simpa [frame, Copy.frame] using (buffer_padding (word bits))
  by_cases selected : name = 2
  · subst name
    change install guardWiring _ _ (guardWiring true) = _
    rw [install_at]
    simpa [frame, Copy.frame, Fin.ext_iff, -Fin.val_eq_zero_iff] using (buffer_padding [newFlag])
  rw [install_outside _ _ _ _ (by
    rintro ⟨localName, equal⟩
    change (if localName then 2 else 0) = name at equal
    cases localName <;> simp_all)]
  simp [frame, first, selected]

theorem guard_runs (bits : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths extraWidths bits.length arrayWidth) readOnly guard (2 * bits.length + 2)
      (false, 0) (position offset) (frame context bits scratch flag array)
      (false, 2) (position offset) (frame context bits scratch (data (bits.any id)) array) := by
  have trace := (StandardBinaryGuard.runs bits flag).wire guardWiring
    (widths extraWidths bits.length arrayWidth) readOnly
    (by intro name; cases name <;> simp only [guardWiring_apply, Bool.false_eq_true, ↓reduceIte, widths, Fin.ext_iff, Fin.val_zero, StandardBinaryGuard.widths] <;> norm_num)
    (by intro name premise; cases name <;> simp only [readOnly, guardWiring_apply, Bool.false_eq_true, ↓reduceIte, Fin.val_zero] at premise <;> norm_num at premise)
    (frame context bits scratch flag array) (position offset)
  rw [guard_positions, guard_install, guard_install] at trace
  exact trace

/- Until the enclosing transfer, the array cursor moves forward by exactly
`elementWidth * index` cells. Only private counter and guard tapes are written. -/
include advanceRuns advanceHalt in
private theorem raw_loop_runs (rank : ℕ) (bits : List Bool)
    (indexValue : value bits = rank) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    ∃ finalScratch,
      finalScratch.length = bits.length ∧
      Runs (widths extraWidths bits.length arrayWidth) readOnly (loop advance advanceEntry)
        (rank * (6 * bits.length + advanceTicks + 11) + 2 * bits.length + 2)
        (.inl (false, 0)) (position offset) (frame context bits scratch flag array)
        (.inl (false, 2)) (position (offset + rank * elementWidth))
        (frame context (List.replicate bits.length false) finalScratch (data false)
          ((Turing.Tape.move .right)^[rank * elementWidth] array)) := by
  induction rank generalizing bits scratch flag array offset with
  | zero =>
    have zero : bits = List.replicate bits.length false := Binary.eq_zero_digits bits indexValue
    have noBits : bits.any id = false := by
      rw [zero]
      simp
    have trace := (guard_runs context extraWidths bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop advance advanceEntry)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    rw [noBits] at trace
    refine ⟨scratch, sameLength, ?_⟩
    simpa only [Nat.cast_zero, zero_mul, zero_add, add_zero, Function.iterate_zero, id_eq, ← zero] using trace
  | succ rank hypothesis =>
    have positive : 0 < value bits := by omega
    have hasBits : bits.any id = true := (Binary.any_iff_positive bits).mpr positive
    have nextValue : value (Binary.decrement bits) = rank := by
      have decremented := Binary.decrement_value bits positive
      omega
    have guarded := (guard_runs context extraWidths bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop advance advanceEntry)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    rw [hasBits] at guarded
    let guardedTapes := frame context bits scratch (data true) array
    have launch : Runs (widths extraWidths bits.length arrayWidth) readOnly (loop advance advanceEntry) 1
        (.inl (false, 2)) (position offset) guardedTapes
        (.inr (bodyEntry AdvanceState)) (position offset) guardedTapes := by
      apply Runs.next (nextState := Sum.inr (bodyEntry AdvanceState))
        (actions := stationary (MultiTape.read guardedTapes))
        (by simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
          result, MultiTape.read, guardedTapes, frame, data, buffer, Fin.ext_iff, -Fin.val_eq_zero_iff]
            rfl) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop advance advanceEntry) (.inr (bodyEntry AdvanceState)) (position offset) guardedTapes)
    have advanced := (body_runs context extraWidths advance advanceEntry advanceExit elementWidth advanceTicks advanceRuns bits scratch sameLength (data true) array arrayWidth offset).rename Sum.inr
      (target := loop advance advanceEntry)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    let nextArray := (Turing.Tape.move .right)^[elementWidth] array
    let advancedTapes := frame context (Binary.decrement bits) (word (Binary.decrement bits)) (data true) nextArray
    have restart : Runs (widths extraWidths bits.length arrayWidth) readOnly (loop advance advanceEntry) 1
        (.inr (bodyExit advanceExit)) (position (offset + elementWidth)) advancedTapes
        (.inl (false, 0)) (position (offset + elementWidth)) advancedTapes := by
      apply Runs.next (nextState := Sum.inl (false, 0))
        (actions := stationary (MultiTape.read advancedTapes))
        (by simp [loop, MultiTape.whileMachine, body, bodyExit, MultiTape.sequence, advanceHalt]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop advance advanceEntry) (.inl (false, 0))
          (position (offset + elementWidth)) advancedTapes)
    obtain ⟨finalScratch, finalLength, rest⟩ := hypothesis (Binary.decrement bits) nextValue
      (word (Binary.decrement bits)) (by simp [word]) (data true) nextArray (offset + elementWidth)
    simp only [Binary.decrement_length] at rest finalLength
    have complete := guarded.trans (launch.trans (advanced.trans (restart.trans rest)))
    refine ⟨finalScratch, finalLength, ?_⟩
    convert complete using 1
    · ring
    · congr 1
      push_cast
      ring
    · rw [Nat.succ_mul, Function.iterate_add_apply]


noncomputable def cleanup : Machine (Alphabet tapeCount) (StandardBinaryScan.State Unit) :=
  MultiTape.wire counterWiring ArrayCounter.clear

abbrev State (AdvanceState : Type) := Sum (Sum (LoopState AdvanceState) Unit) (StandardBinaryScan.State Unit)

noncomputable def machine (advance : Machine (Alphabet tapeCount) AdvanceState) (advanceEntry : AdvanceState) :
    Machine (Alphabet tapeCount) (State AdvanceState) :=
  MultiTape.sequence (MultiTape.withExit (loop advance advanceEntry)) cleanup (.inl ())

def entry (AdvanceState : Type) : State AdvanceState := .inl (.inl (.inl (false, 0)))
def exit (AdvanceState : Type) : State AdvanceState := .inr (.inr ((), true))

/- The enclosing access computation continues at the selected element.
All private counter and guard regions are canonical, including for index zero. -/
include advanceRuns advanceHalt in
theorem runs (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths extraWidths bits.length arrayWidth) readOnly (machine advance advanceEntry)
      (value bits * (6 * bits.length + advanceTicks + 11) + 4 * bits.length + 6)
      (entry AdvanceState) (position offset) (frame context bits scratch flag array)
      (exit AdvanceState) (position (offset + value bits * elementWidth))
      (frame context (List.replicate bits.length false) (word (List.replicate bits.length false)) (data false)
        ((Turing.Tape.move .right)^[value bits * elementWidth] array)) := by
  obtain ⟨finalScratch, scratchLength, loopTrace⟩ :=
    raw_loop_runs context extraWidths advance advanceEntry advanceExit elementWidth advanceTicks advanceRuns advanceHalt (value bits) bits rfl scratch sameLength flag array arrayWidth offset
  let finalArray := (Turing.Tape.move .right)^[value bits * elementWidth] array
  let finalOffset : ℤ := offset + value bits * elementWidth
  have common := loopTrace.withExit_at (by
    simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
      result, MultiTape.read, frame, data, buffer, Fin.ext_iff, -Fin.val_eq_zero_iff]
    norm_num [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'])
  have cleared := (ArrayCounter.clear_runs (List.replicate bits.length false) finalScratch
    (by simpa only [List.length_replicate] using scratchLength)).wire
    counterWiring (widths extraWidths bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> simp only [counterWiring_apply, widths, Fin.ext_iff, Fin.val_zero] <;> norm_num)
    (by intro name premise; fin_cases name <;> simp only [readOnly, counterWiring_val] at premise <;> norm_num at premise)
    (frame context (List.replicate bits.length false) finalScratch (data false) finalArray) (position finalOffset)
  rw [counter_positions, counter_install, counter_install] at cleared
  simp only [List.length_replicate] at cleared
  have complete := common.sequence cleanup (.inl ()) (by intro symbols; rfl) cleared
  convert complete using 1 <;> first | rfl | ring

end Polytime2.ArraySeek
