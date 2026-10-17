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

import Polytime2.ArraySeek
import Polytime2.StandardBinaryGuard
import Polytime2.UnaryMove

/-! # Runtime-width specialization of shared array navigation -/

namespace Polytime2.RuntimeArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)

private instance : Fact (4 ≤ 5) := ⟨by decide⟩

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

def advanceWiring : Bool ↪ Fin 5 := twoTapes 4 3 (by decide)

noncomputable def advance : Machine Alphabet (Bool ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.wire advanceWiring UnaryMove.machine

abbrev State := ArraySeek.State (Bool ⊕ (Fin 2 ⊕ Fin 3))

noncomputable def machine : Machine Alphabet State := ArraySeek.machine (tapeCount := 5) advance (.inl false)
def entry : State := ArraySeek.entry _
def exit : State := ArraySeek.exit _

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, ArraySeek.machine, ArraySeek.exit, MultiTape.sequence,
    ArraySeek.cleanup, MultiTape.wire, ArrayCounter.clear, StandardBinaryScan.machine]

private theorem advance_runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (flag : Symbol) (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths elementWidth bits.length arrayWidth) readOnly advance (2 * elementWidth + 5)
      (.inl false) (position offset) (frame elementWidth bits scratch flag array)
      (.inr (.inr 2)) (position (offset + elementWidth))
      (frame elementWidth bits scratch flag ((Turing.Tape.move .right)^[elementWidth] array)) := by
  let tapes := frame elementWidth bits scratch flag array
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
      frame elementWidth bits scratch flag
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
  exact moved

/-- A unary-width movement command instantiates the shared binary counter loop. -/
theorem runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths elementWidth bits.length arrayWidth) readOnly machine
      (value bits * (6 * bits.length + 2 * elementWidth + 16) + 4 * bits.length + 6)
      entry (position offset) (frame elementWidth bits scratch flag array)
      exit (position (offset + value bits * elementWidth))
      (frame elementWidth (List.replicate bits.length false) (word (List.replicate bits.length false)) (data false)
        ((Turing.Tape.move .right)^[value bits * elementWidth] array)) := by
  have widthsEqual (digits arrayWidth : ℕ) : ArraySeek.widths (tapeCount := 5) (fun _ : Fin 5 => elementWidth) digits arrayWidth = widths elementWidth digits arrayWidth := by
    funext name
    fin_cases name <;> rfl
  have readonlyEqual : ArraySeek.readOnly (tapeCount := 5) = readOnly := by
    funext name
    fin_cases name <;> rfl
  have positionEqual (offset : ℤ) : ArraySeek.position (tapeCount := 5) offset = position offset := rfl
  have frameEqual (bits : List Bool) (scratch : List Symbol) (flag : Symbol) (array : Turing.Tape Symbol) :
      ArraySeek.frame (tapeCount := 5) (fun _ : Fin 5 => unary elementWidth) bits scratch flag array = frame elementWidth bits scratch flag array := by
    funext name
    fin_cases name <;> rfl
  have trace := ArraySeek.runs (tapeCount := 5) (fun _ : Fin 5 => unary elementWidth) (fun _ => elementWidth) advance
    (.inl false) (.inr (.inr 2)) elementWidth (2 * elementWidth + 5)
    (by
      intro bits scratch flag array arrayWidth offset
      simpa only [widthsEqual, readonlyEqual, frameEqual, positionEqual, machine, entry, exit] using
        advance_runs elementWidth bits scratch flag array arrayWidth offset)
    (by intro symbols; simp [advance, MultiTape.wire])
    bits scratch sameLength flag array arrayWidth offset
  simp only [widthsEqual, readonlyEqual, frameEqual, positionEqual] at trace
  convert trace using 1 <;> rfl

end Polytime2.RuntimeArraySeek
