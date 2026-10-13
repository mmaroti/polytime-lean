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

import Polytime2.StandardBinaryDecrement
import Polytime2.StandardBinaryGuard
import Polytime2.StandardTapeCommands
import Polytime2.StandardHead

/-! # Binary-indexed navigation with fixed private counters

The original index is copied by the enclosing access routine. Navigation uses
private fixed-width counter and decrement tapes, a one-bit guard, and an
immutable array cursor. All writes respect the declared data regions.
-/

namespace Polytime2.StandardArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)

namespace Counter

abbrev Alphabet := CallingConvention.Alphabet (Fin 2)
abbrev State := Sum StandardBinaryDecrement.State (Fin 3)

def frame (bits : List Bool) (scratch : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word bits) else buffer scratch

def decrementWiring : Bool ↪ Fin 2 :=
  ⟨(fun name => if name then 1 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem decrementWiring_apply (name : Bool) : decrementWiring name = (if name then 1 else 0) := rfl

noncomputable def decrement : Machine Alphabet StandardBinaryDecrement.State :=
  MultiTape.wire decrementWiring StandardBinaryDecrement.machine

noncomputable def copyBack : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 1 0 (by decide)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence decrement copyBack 0

def entry : State := .inl StandardBinaryDecrement.entry
def exit : State := .inr 2

/-- Only private storage is overwritten; both fixed-width heads are restored. -/
theorem runs (bits : List Bool) (scratch : List Symbol) (sameLength : scratch.length = bits.length) :
    Runs (fun _ : Fin 2 => bits.length) (fun _ => false) machine (4 * bits.length + 6)
      entry (fun _ => 0) (frame bits scratch) exit (fun _ => 0)
      (frame (Binary.decrement bits) (word (Binary.decrement bits))) := by
  have first := (StandardBinaryDecrement.runs bits scratch sameLength).wire_of_eq
    decrementWiring (fun _ : Fin 2 => bits.length) (fun _ => false)
    (by intro name; rfl) (by intro name premise; cases premise)
    (frame bits scratch) (frame bits (word (Binary.decrement bits)))
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨false, rfl⟩)
      · exact False.elim (outside ⟨true, rfl⟩))
  have second := StandardTapeCommands.copy_runs (1 : Fin 2) 0 (by decide)
    (fun _ : Fin 2 => bits.length) (fun _ => false) rfl (Binary.decrement bits) (word bits)
    (Binary.decrement_length bits).symm (Binary.decrement_length bits).symm
    (by simp [word]) (frame bits (word (Binary.decrement bits))) rfl rfl
  have copied : Function.update (frame bits (word (Binary.decrement bits))) 0
      (buffer (word (Binary.decrement bits))) = frame (Binary.decrement bits) (word (Binary.decrement bits)) := by
    funext name
    fin_cases name <;> simp [frame]
  rw [copied] at second
  have complete := first.sequence copyBack 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryDecrement.machine, StandardBinaryDecrement.exit, MultiTape.withExit]) second
  simp only [Binary.decrement_length] at complete
  convert complete using 1 <;> first | rfl | omega

noncomputable def clear : Machine Alphabet (StandardBinaryScan.State Unit) :=
  MultiTape.wire decrementWiring (StandardBinaryScan.machine BinaryScan.clear)

theorem clear_runs (bits : List Bool) (scratch : List Symbol) (sameLength : scratch.length = bits.length) :
    Runs (fun _ : Fin 2 => bits.length) (fun _ => false) clear (2 * bits.length + 2)
      (.inl ()) (fun _ => 0) (frame bits scratch) (.inr ((), true)) (fun _ => 0)
      (frame bits (word (List.replicate bits.length false))) := by
  have trace := StandardBinaryScan.runs BinaryScan.clear () bits scratch sameLength
  simp only [StandardBinaryScan.run, BinaryScan.clear_run] at trace
  exact trace.wire_of_eq decrementWiring (fun _ : Fin 2 => bits.length) (fun _ => false)
    (by intro name; rfl) (by intro name premise; cases premise)
    (frame bits scratch) (frame bits (word (List.replicate bits.length false)))
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨false, rfl⟩)
      · exact False.elim (outside ⟨true, rfl⟩))

end Counter

abbrev Alphabet := CallingConvention.Alphabet (Fin 4)

/-- Counter, decrement scratch, guard bit, and array cursor. -/
def frame (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word counter)
  else if name = 1 then buffer scratch
  else if name = 2 then buffer [flag]
  else array

def widths (digits arrayWidth : ℕ) (name : Fin 4) : ℕ :=
  if name = 3 then arrayWidth else if name = 2 then 1 else digits

def readOnly (name : Fin 4) : Bool := decide (name = 3)

def position (offset : ℤ) (name : Fin 4) : ℤ := if name = 3 then offset else 0

def counterWiring : Fin 2 ↪ Fin 4 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 4 => name.val) equal)⟩

def guardWiring : Bool ↪ Fin 4 :=
  ⟨(fun name => if name then 2 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem counterWiring_apply (name : Fin 2) : counterWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem guardWiring_apply (name : Bool) : guardWiring name = (if name then 2 else 0) := rfl

noncomputable def counter : Machine Alphabet Counter.State := MultiTape.wire counterWiring Counter.machine
noncomputable def advance (elementWidth : ℕ) : Machine Alphabet (Fin (elementWidth + 1)) :=
  MultiTape.wire (oneTape (3 : Fin 4)) (Move.machine elementWidth .right)

abbrev BodyState (elementWidth : ℕ) := Sum Counter.State (Fin (elementWidth + 1))

noncomputable def body (elementWidth : ℕ) : Machine Alphabet (BodyState elementWidth) :=
  MultiTape.sequence counter (advance elementWidth) (Fin.last elementWidth)

def bodyEntry (elementWidth : ℕ) : BodyState elementWidth := .inl Counter.entry
def bodyExit (elementWidth : ℕ) : BodyState elementWidth := .inr 0

private theorem counter_positions (offset : ℤ) :
    install counterWiring (fun _ : Fin 2 => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  · change install counterWiring _ _ (counterWiring 0) = _
    rw [install_at]; rfl
  · change install counterWiring _ _ (counterWiring 1) = _
    rw [install_at]; rfl
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    have values := congrArg (fun name : Fin 4 => name.val) equal
    have bounded := localName.isLt
    simp only [counterWiring_apply] at values
    omega

private theorem counter_install (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (oldCounter : List Bool) (oldScratch : List Symbol) :
    install counterWiring (Counter.frame counter scratch) (frame oldCounter oldScratch flag array) =
      frame counter scratch flag array := by
  funext name
  fin_cases name
  · change install counterWiring _ _ (counterWiring 0) = _
    rw [install_at]; rfl
  · change install counterWiring _ _ (counterWiring 1) = _
    rw [install_at]; rfl
  all_goals
    rw [install_outside _ _ _ _ (by
      rintro ⟨localName, equal⟩
      have values := congrArg (fun name : Fin 4 => name.val) equal
      have bounded := localName.isLt
      simp only [counterWiring_apply] at values
      omega)]
    rfl

/-- Decrement private storage, then advance the immutable array by one element. -/
theorem body_runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths bits.length arrayWidth) readOnly (body elementWidth)
      (4 * bits.length + elementWidth + 7)
      (bodyEntry elementWidth) (position offset) (frame bits scratch flag array)
      (bodyExit elementWidth) (position (offset + elementWidth))
      (frame (Binary.decrement bits) (word (Binary.decrement bits)) flag
        ((Turing.Tape.move .right)^[elementWidth] array)) := by
  have decremented := (Counter.runs bits scratch sameLength).wire counterWiring
    (widths bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise)
    (frame bits scratch flag array) (position offset)
  rw [counter_positions, counter_install, counter_install] at decremented
  have moved := (StandardHead.move_runs elementWidth .right (fun _ : Unit => arrayWidth)
    (fun _ : Unit => true) (fun _ : Unit => offset) (fun _ : Unit => array)).wire
    (oneTape (3 : Fin 4)) (widths bits.length arrayWidth) readOnly
    (by intro name; cases name; rfl) (by intro name premise; cases name; rfl)
    (frame (Binary.decrement bits) (word (Binary.decrement bits)) flag array) (position offset)
  have startPositions : install (oneTape (3 : Fin 4)) (fun _ : Unit => offset) (position offset) = position offset := by
    exact install_self (oneTape (3 : Fin 4)) (position offset)
  have finalPositions : install (oneTape (3 : Fin 4))
      (fun name : Unit => offset + elementWidth * displacement (some Turing.Dir.right)) (position offset) =
      position (offset + elementWidth) := by
    funext name
    fin_cases name <;> simp [position, install_one, displacement]
  have startTapes : install (oneTape (3 : Fin 4)) (fun _ : Unit => array)
      (frame (Binary.decrement bits) (word (Binary.decrement bits)) flag array) =
      frame (Binary.decrement bits) (word (Binary.decrement bits)) flag array := by
    exact install_self (oneTape (3 : Fin 4)) _
  have finalTapes : install (oneTape (3 : Fin 4))
      (fun name : Unit => (Turing.Tape.move .right)^[elementWidth] array)
      (frame (Binary.decrement bits) (word (Binary.decrement bits)) flag array) =
      frame (Binary.decrement bits) (word (Binary.decrement bits)) flag
        ((Turing.Tape.move .right)^[elementWidth] array) := by
    funext name
    fin_cases name <;> simp [frame, install_one]
  rw [startPositions, finalPositions, startTapes, finalTapes] at moved
  have complete := decremented.sequence (advance elementWidth) (Fin.last elementWidth)
    (by intro symbols; simp [MultiTape.wire, Counter.machine, Counter.exit, MultiTape.sequence,
      Counter.copyBack, StandardTapeCommands.copy, StandardTerminatedCopy.machine]) moved
  convert complete using 1 <;> first | rfl | omega


noncomputable def guard : Machine Alphabet StandardBinaryGuard.State :=
  MultiTape.wire guardWiring StandardBinaryGuard.machine

def result (symbols : Symbols Alphabet) : Bool := symbols 2 == 2

abbrev LoopState (elementWidth : ℕ) := Sum StandardBinaryGuard.State (BodyState elementWidth)

noncomputable def loop (elementWidth : ℕ) : Machine Alphabet (LoopState elementWidth) :=
  MultiTape.whileMachine guard (body elementWidth) (false, 0) (bodyEntry elementWidth) result

private theorem guard_positions (offset : ℤ) :
    install guardWiring (fun _ : Bool => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  · change install guardWiring _ _ (guardWiring false) = _
    rw [install_at]; rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal
  · change install guardWiring _ _ (guardWiring true) = _
    rw [install_at]; rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal

private theorem guard_install (bits : List Bool) (scratch : List Symbol) (flag newFlag : Symbol)
    (array : Turing.Tape Symbol) :
    install guardWiring (Copy.frame [0] (word bits ++ [0]) [0] [newFlag, 0])
      (frame bits scratch flag array) = frame bits scratch newFlag array := by
  funext name
  fin_cases name
  · change install guardWiring _ _ (guardWiring false) = _
    rw [install_at]
    exact buffer_padding _
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal
  · change install guardWiring _ _ (guardWiring true) = _
    rw [install_at]
    change Turing.Tape.mk' (Turing.ListBlank.mk [0])
      (Turing.ListBlank.mk ([newFlag] ++ [0])) = buffer [newFlag]
    exact buffer_padding _
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal

theorem guard_runs (bits : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths bits.length arrayWidth) readOnly guard (2 * bits.length + 2)
      (false, 0) (position offset) (frame bits scratch flag array)
      (false, 2) (position offset) (frame bits scratch (data (bits.any id)) array) := by
  have trace := (StandardBinaryGuard.runs bits flag).wire guardWiring
    (widths bits.length arrayWidth) readOnly
    (by intro name; cases name <;> rfl)
    (by intro name premise; cases name <;> simp [readOnly] at premise)
    (frame bits scratch flag array) (position offset)
  rw [guard_positions, guard_install, guard_install] at trace
  exact trace

/-- Until the enclosing transfer, the array cursor moves forward by exactly
`elementWidth * index` cells. Only private counter and guard tapes are written. -/
private theorem raw_loop_runs (elementWidth : ℕ) (rank : ℕ) (bits : List Bool)
    (indexValue : value bits = rank) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    ∃ finalScratch,
      finalScratch.length = bits.length ∧
      Runs (widths bits.length arrayWidth) readOnly (loop elementWidth)
        (rank * (6 * bits.length + elementWidth + 11) + 2 * bits.length + 2)
        (.inl (false, 0)) (position offset) (frame bits scratch flag array)
        (.inl (false, 2)) (position (offset + rank * elementWidth))
        (frame (List.replicate bits.length false) finalScratch (data false)
          ((Turing.Tape.move .right)^[rank * elementWidth] array)) := by
  induction rank generalizing bits scratch flag array offset with
  | zero =>
    have zero : bits = List.replicate bits.length false := Binary.eq_zero_digits bits indexValue
    have noBits : bits.any id = false := by
      rw [zero]
      simp
    have trace := (guard_runs bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop elementWidth)
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
    have guarded := (guard_runs bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop elementWidth)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    rw [hasBits] at guarded
    let guardedTapes := frame bits scratch (data true) array
    have launch : Runs (widths bits.length arrayWidth) readOnly (loop elementWidth) 1
        (.inl (false, 2)) (position offset) guardedTapes
        (.inr (bodyEntry elementWidth)) (position offset) guardedTapes := by
      apply Runs.next (nextState := Sum.inr (bodyEntry elementWidth))
        (actions := stationary (MultiTape.read guardedTapes))
        (by simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
          result, MultiTape.read, guardedTapes, frame, data, buffer]
            rfl) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop elementWidth) (.inr (bodyEntry elementWidth)) (position offset) guardedTapes)
    have advanced := (body_runs elementWidth bits scratch sameLength (data true) array arrayWidth offset).rename Sum.inr
      (target := loop elementWidth)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    let nextArray := (Turing.Tape.move .right)^[elementWidth] array
    let advancedTapes := frame (Binary.decrement bits) (word (Binary.decrement bits)) (data true) nextArray
    have restart : Runs (widths bits.length arrayWidth) readOnly (loop elementWidth) 1
        (.inr (bodyExit elementWidth)) (position (offset + elementWidth)) advancedTapes
        (.inl (false, 0)) (position (offset + elementWidth)) advancedTapes := by
      apply Runs.next (nextState := Sum.inl (false, 0))
        (actions := stationary (MultiTape.read advancedTapes))
        (by simp [loop, MultiTape.whileMachine, body, bodyExit, MultiTape.sequence, advance,
          MultiTape.wire, Move.machine]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop elementWidth) (.inl (false, 0))
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


noncomputable def cleanup : Machine Alphabet (StandardBinaryScan.State Unit) :=
  MultiTape.wire counterWiring Counter.clear

abbrev State (elementWidth : ℕ) := Sum (Sum (LoopState elementWidth) Unit) (StandardBinaryScan.State Unit)

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  MultiTape.sequence (MultiTape.withExit (loop elementWidth)) cleanup (.inl ())

def entry (elementWidth : ℕ) : State elementWidth := .inl (.inl (.inl (false, 0)))
def exit (elementWidth : ℕ) : State elementWidth := .inr (.inr ((), true))

/-- The enclosing access computation continues at the selected element.
All private counter and guard regions are canonical, including for index zero. -/
theorem runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths bits.length arrayWidth) readOnly (machine elementWidth)
      (value bits * (6 * bits.length + elementWidth + 11) + 4 * bits.length + 6)
      (entry elementWidth) (position offset) (frame bits scratch flag array)
      (exit elementWidth) (position (offset + value bits * elementWidth))
      (frame (List.replicate bits.length false) (word (List.replicate bits.length false)) (data false)
        ((Turing.Tape.move .right)^[value bits * elementWidth] array)) := by
  obtain ⟨finalScratch, scratchLength, loopTrace⟩ :=
    raw_loop_runs elementWidth (value bits) bits rfl scratch sameLength flag array arrayWidth offset
  let finalArray := (Turing.Tape.move .right)^[value bits * elementWidth] array
  let finalOffset : ℤ := offset + value bits * elementWidth
  have common := loopTrace.withExit_at (by
    simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
      result, MultiTape.read, frame, data, buffer]
    decide)
  have cleared := (Counter.clear_runs (List.replicate bits.length false) finalScratch
    (by simpa only [List.length_replicate] using scratchLength)).wire
    counterWiring (widths bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> simp [widths])
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise)
    (frame (List.replicate bits.length false) finalScratch (data false) finalArray) (position finalOffset)
  rw [counter_positions, counter_install, counter_install] at cleared
  simp only [List.length_replicate] at cleared
  have complete := common.sequence cleanup (.inl ()) (by intro symbols; rfl) cleared
  convert complete using 1 <;> first | rfl | ring

end Polytime2.StandardArraySeek
