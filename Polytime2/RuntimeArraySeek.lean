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

import Polytime2.StandardArraySeek
import Polytime2.UnaryMove

/-! # Array seeking with a runtime unary element width -/

namespace Polytime2.RuntimeArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)
open StandardArraySeek

abbrev Alphabet := CallingConvention.Alphabet (Fin 5)

/-- Counter, decrement scratch, guard bit, array cursor, and unary element width. -/
def frame (elementWidth : ℕ) (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word counter)
  else if name = 1 then buffer scratch
  else if name = 2 then buffer [flag]
  else if name = 3 then array else unary elementWidth

def widths (elementWidth digits arrayWidth : ℕ) (name : Fin 5) : ℕ :=
  if name = 3 then arrayWidth else if name = 4 then elementWidth else if name = 2 then 1 else digits

def readOnly (name : Fin 5) : Bool := decide (name = 3 ∨ name = 4)

def position (offset : ℤ) (name : Fin 5) : ℤ := if name = 3 then offset else 0

def counterWiring : Fin 2 ↪ Fin 5 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 5 => name.val) equal)⟩

def guardWiring : Bool ↪ Fin 5 :=
  ⟨(fun name => if name then 2 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem counterWiring_apply (name : Fin 2) : counterWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem guardWiring_apply (name : Bool) : guardWiring name = (if name then 2 else 0) := rfl

noncomputable def counter : Machine Alphabet Counter.State := MultiTape.wire counterWiring Counter.machine
def advanceWiring : Bool ↪ Fin 5 := twoTapes 4 3 (by decide)

noncomputable def advance : Machine Alphabet (Bool ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.wire advanceWiring UnaryMove.machine

abbrev BodyState := Sum Counter.State (Bool ⊕ (Fin 2 ⊕ Fin 3))

noncomputable def body : Machine Alphabet BodyState :=
  MultiTape.sequence counter advance (.inl false)

def bodyEntry : BodyState := .inl Counter.entry
def bodyExit : BodyState := .inr (.inr (.inr 2))

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
    have values := congrArg (fun name : Fin 5 => name.val) equal
    have bounded := localName.isLt
    simp only [counterWiring_apply] at values
    omega

private theorem counter_install (elementWidth : ℕ) (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (oldCounter : List Bool) (oldScratch : List Symbol) :
    install counterWiring (Counter.frame counter scratch) (frame elementWidth oldCounter oldScratch flag array) =
      frame elementWidth counter scratch flag array := by
  funext name
  fin_cases name
  · change install counterWiring _ _ (counterWiring 0) = _
    rw [install_at]; rfl
  · change install counterWiring _ _ (counterWiring 1) = _
    rw [install_at]; rfl
  all_goals
    rw [install_outside _ _ _ _ (by
      rintro ⟨localName, equal⟩
      have values := congrArg (fun name : Fin 5 => name.val) equal
      have bounded := localName.isLt
      simp only [counterWiring_apply] at values
      omega)]
    rfl

/-- Decrement private storage, then advance the immutable array by one element. -/
theorem body_runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths elementWidth bits.length arrayWidth) readOnly body
      (4 * bits.length + 2 * elementWidth + 12)
      bodyEntry (position offset) (frame elementWidth bits scratch flag array)
      bodyExit (position (offset + elementWidth))
      (frame elementWidth (Binary.decrement bits) (word (Binary.decrement bits)) flag
        ((Turing.Tape.move .right)^[elementWidth] array)) := by
  have decremented := (Counter.runs bits scratch sameLength).wire counterWiring
    (widths elementWidth bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise)
    (frame elementWidth bits scratch flag array) (position offset)
  rw [counter_positions, counter_install, counter_install] at decremented
  let tapes := frame elementWidth (Binary.decrement bits) (word (Binary.decrement bits)) flag array
  have moved := (UnaryMove.runs elementWidth array
    (fun name => if name then arrayWidth else elementWidth) (fun _ => true)
    (fun name => if name then offset else 0)).wire advanceWiring
      (widths elementWidth bits.length arrayWidth) readOnly
      (by intro name; cases name <;> rfl)
      (by intro name premise; rfl) tapes (position offset)
  have startPositions : install advanceWiring
      (fun name => if name then offset else (0 : ℤ)) (position offset) = position offset := by
    funext name
    fin_cases name <;> simp [install_two, advanceWiring, position]
  have finalPositions : install advanceWiring
      (fun name => if name then offset + elementWidth else (0 : ℤ)) (position offset) =
      position (offset + elementWidth) := by
    funext name
    fin_cases name <;> simp [install_two, advanceWiring, position]
  have startTapes : install advanceWiring
      (fun name => if name then array else unary elementWidth) tapes = tapes := by
    funext name
    fin_cases name
    all_goals first
      | (change install advanceWiring _ _ (advanceWiring false) = _; rw [install_at]; rfl)
      | (change install advanceWiring _ _ (advanceWiring true) = _; rw [install_at]; rfl)
      | (rw [install_outside _ _ _ _ (by
          rintro ⟨localName, equal⟩
          cases localName <;>
            simp only [advanceWiring, twoTapes_false, twoTapes_true] at equal <;>
            norm_num at equal)])
  have finalTapes : install advanceWiring
      (fun name => if name then (Turing.Tape.move .right)^[elementWidth] array else unary elementWidth) tapes =
      frame elementWidth (Binary.decrement bits) (word (Binary.decrement bits)) flag
        ((Turing.Tape.move .right)^[elementWidth] array) := by
    funext name
    fin_cases name
    all_goals first
      | (change install advanceWiring _ _ (advanceWiring false) = _; rw [install_at]; rfl)
      | (change install advanceWiring _ _ (advanceWiring true) = _; rw [install_at]; rfl)
      | (rw [install_outside _ _ _ _ (by
          rintro ⟨localName, equal⟩
          cases localName <;>
            simp only [advanceWiring, twoTapes_false, twoTapes_true] at equal <;>
            norm_num at equal)]; rfl)
  have movedPosition : (fun name : Bool =>
      if name then (if name then offset else (0 : ℤ)) + elementWidth
      else if name then offset else 0) = fun name => if name then offset + elementWidth else 0 := by
    funext name; cases name <;> rfl
  rw [movedPosition, startPositions, finalPositions, startTapes, finalTapes] at moved
  have complete := decremented.sequence advance (.inl false)
    (by intro symbols; simp [MultiTape.wire, Counter.machine, Counter.exit, MultiTape.sequence,
      Counter.copyBack, StandardTapeCommands.copy, StandardTerminatedCopy.machine]) moved
  convert complete using 1 <;> first | rfl | omega

noncomputable def guard : Machine Alphabet StandardBinaryGuard.State :=
  MultiTape.wire guardWiring StandardBinaryGuard.machine

def result (symbols : Symbols Alphabet) : Bool := symbols 2 == 2

abbrev LoopState := Sum StandardBinaryGuard.State BodyState

noncomputable def loop : Machine Alphabet LoopState :=
  MultiTape.whileMachine guard body (false, 0) bodyEntry result

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
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal

private theorem guard_install (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol) (flag newFlag : Symbol)
    (array : Turing.Tape Symbol) :
    install guardWiring (Copy.frame [0] (word bits ++ [0]) [0] [newFlag, 0])
      (frame elementWidth bits scratch flag array) = frame elementWidth bits scratch newFlag array := by
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
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [guardWiring_apply] at equal

theorem guard_runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths elementWidth bits.length arrayWidth) readOnly guard (2 * bits.length + 2)
      (false, 0) (position offset) (frame elementWidth bits scratch flag array)
      (false, 2) (position offset) (frame elementWidth bits scratch (data (bits.any id)) array) := by
  have trace := (StandardBinaryGuard.runs bits flag).wire guardWiring
    (widths elementWidth bits.length arrayWidth) readOnly
    (by intro name; cases name <;> rfl)
    (by intro name premise; cases name <;> simp [readOnly] at premise)
    (frame elementWidth bits scratch flag array) (position offset)
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
      Runs (widths elementWidth bits.length arrayWidth) readOnly loop
        (rank * (6 * bits.length + 2 * elementWidth + 16) + 2 * bits.length + 2)
        (.inl (false, 0)) (position offset) (frame elementWidth bits scratch flag array)
        (.inl (false, 2)) (position (offset + rank * elementWidth))
        (frame elementWidth (List.replicate bits.length false) finalScratch (data false)
          ((Turing.Tape.move .right)^[rank * elementWidth] array)) := by
  induction rank generalizing bits scratch flag array offset with
  | zero =>
    have zero : bits = List.replicate bits.length false := Binary.eq_zero_digits bits indexValue
    have noBits : bits.any id = false := by
      rw [zero]
      simp
    have trace := (guard_runs elementWidth bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop)
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
    have guarded := (guard_runs elementWidth bits scratch flag array arrayWidth offset).rename Sum.inl
      (target := loop)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    rw [hasBits] at guarded
    let guardedTapes := frame elementWidth bits scratch (data true) array
    have launch : Runs (widths elementWidth bits.length arrayWidth) readOnly loop 1
        (.inl (false, 2)) (position offset) guardedTapes
        (.inr bodyEntry) (position offset) guardedTapes := by
      apply Runs.next (nextState := Sum.inr bodyEntry)
        (actions := stationary (MultiTape.read guardedTapes))
        (by simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
          result, MultiTape.read, guardedTapes, frame, data, buffer]
            rfl) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop) (.inr bodyEntry) (position offset) guardedTapes)
    have advanced := (body_runs elementWidth bits scratch sameLength (data true) array arrayWidth offset).rename Sum.inr
      (target := loop)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    let nextArray := (Turing.Tape.move .right)^[elementWidth] array
    let advancedTapes := frame elementWidth (Binary.decrement bits) (word (Binary.decrement bits)) (data true) nextArray
    have restart : Runs (widths elementWidth bits.length arrayWidth) readOnly loop 1
        (.inr bodyExit) (position (offset + elementWidth)) advancedTapes
        (.inl (false, 0)) (position (offset + elementWidth)) advancedTapes := by
      apply Runs.next (nextState := Sum.inl (false, 0))
        (actions := stationary (MultiTape.read advancedTapes))
        (by simp [loop, MultiTape.whileMachine, body, bodyExit, MultiTape.sequence, advance,
          MultiTape.wire, UnaryMove.halt]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop) (.inl (false, 0))
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

abbrev State := Sum (Sum LoopState Unit) (StandardBinaryScan.State Unit)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence (MultiTape.withExit loop) cleanup (.inl ())

def entry : State := .inl (.inl (.inl (false, 0)))
def exit : State := .inr (.inr ((), true))

/-- The enclosing access computation continues at the selected element.
All private counter and guard regions are canonical, including for index zero. -/
theorem runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths elementWidth bits.length arrayWidth) readOnly machine
      (value bits * (6 * bits.length + 2 * elementWidth + 16) + 4 * bits.length + 6)
      entry (position offset) (frame elementWidth bits scratch flag array)
      exit (position (offset + value bits * elementWidth))
      (frame elementWidth (List.replicate bits.length false) (word (List.replicate bits.length false)) (data false)
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
    counterWiring (widths elementWidth bits.length arrayWidth) readOnly
    (by intro name; fin_cases name <;> simp [widths])
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise)
    (frame elementWidth (List.replicate bits.length false) finalScratch (data false) finalArray) (position finalOffset)
  rw [counter_positions, counter_install, counter_install] at cleared
  simp only [List.length_replicate] at cleared
  have complete := common.sequence cleanup (.inl ()) (by intro symbols; rfl) cleared
  convert complete using 1 <;> first | rfl | ring

end Polytime2.RuntimeArraySeek
