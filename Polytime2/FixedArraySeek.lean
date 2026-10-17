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
import Polytime2.StandardTapeCommands
import Polytime2.StandardHead

/-! # Fixed-width specialization of shared array navigation -/

namespace Polytime2.FixedArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)

private instance : Fact (4 ≤ 4) := ⟨by decide⟩

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

noncomputable def advance (elementWidth : ℕ) : Machine Alphabet (Fin (elementWidth + 1)) :=
  MultiTape.wire (oneTape (3 : Fin 4)) (Move.machine elementWidth .right)

abbrev State (elementWidth : ℕ) := ArraySeek.State (Fin (elementWidth + 1))

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  ArraySeek.machine (tapeCount := 4) (advance elementWidth) (Fin.last elementWidth)

def entry (elementWidth : ℕ) : State elementWidth := ArraySeek.entry _
def exit (elementWidth : ℕ) : State elementWidth := ArraySeek.exit _

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit, ArraySeek.machine, ArraySeek.exit, MultiTape.sequence,
    ArraySeek.cleanup, MultiTape.wire, ArrayCounter.clear, StandardBinaryScan.machine]

private theorem advance_runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (flag : Symbol) (array : Turing.Tape Symbol) (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths bits.length arrayWidth) readOnly (advance elementWidth) elementWidth
      (Fin.last elementWidth) (position offset) (frame bits scratch flag array)
      0 (position (offset + elementWidth))
      (frame bits scratch flag ((Turing.Tape.move .right)^[elementWidth] array)) := by
  have moved := (StandardHead.move_runs elementWidth .right (fun _ : Unit => arrayWidth)
    (fun _ : Unit => true) (fun _ : Unit => offset) (fun _ : Unit => array)).wire
    (oneTape (3 : Fin 4)) (widths bits.length arrayWidth) readOnly
    (by intro name; cases name; rfl) (by intro name premise; cases name; rfl)
    (frame bits scratch flag array) (position offset)
  have startPositions : install (oneTape (3 : Fin 4)) (fun _ : Unit => offset) (position offset) = position offset := by
    exact install_self (oneTape (3 : Fin 4)) (position offset)
  have finalPositions : install (oneTape (3 : Fin 4))
      (fun name : Unit => offset + elementWidth * displacement (some Turing.Dir.right)) (position offset) =
      position (offset + elementWidth) := by
    funext name
    fin_cases name <;> simp [position, install_one, displacement]
  have startTapes : install (oneTape (3 : Fin 4)) (fun _ : Unit => array)
      (frame bits scratch flag array) =
      frame bits scratch flag array := by
    exact install_self (oneTape (3 : Fin 4)) _
  have finalTapes : install (oneTape (3 : Fin 4))
      (fun name : Unit => (Turing.Tape.move .right)^[elementWidth] array)
      (frame bits scratch flag array) =
      frame bits scratch flag
        ((Turing.Tape.move .right)^[elementWidth] array) := by
    funext name
    fin_cases name <;> simp [frame, install_one]
  rw [startPositions, finalPositions, startTapes, finalTapes] at moved
  exact moved

/-- Fixed-width movement instantiates the shared counter loop without size tapes. -/
theorem runs (elementWidth : ℕ) (bits : List Bool) (scratch : List Symbol)
    (sameLength : scratch.length = bits.length) (flag : Symbol) (array : Turing.Tape Symbol)
    (arrayWidth : ℕ) (offset : ℤ) :
    Runs (widths bits.length arrayWidth) readOnly (machine elementWidth)
      (value bits * (6 * bits.length + elementWidth + 11) + 4 * bits.length + 6)
      (entry elementWidth) (position offset) (frame bits scratch flag array)
      (exit elementWidth) (position (offset + value bits * elementWidth))
      (frame (List.replicate bits.length false) (word (List.replicate bits.length false)) (data false)
        ((Turing.Tape.move .right)^[value bits * elementWidth] array)) := by
  have widthsEqual (digits arrayWidth : ℕ) : ArraySeek.widths (tapeCount := 4) (fun _ : Fin 4 => 0) digits arrayWidth = widths digits arrayWidth := by
    funext name
    fin_cases name <;> rfl
  have readonlyEqual : ArraySeek.readOnly (tapeCount := 4) = readOnly := by
    funext name
    fin_cases name <;> rfl
  have positionEqual (offset : ℤ) : ArraySeek.position (tapeCount := 4) offset = position offset := rfl
  have frameEqual (bits : List Bool) (scratch : List Symbol) (flag : Symbol) (array : Turing.Tape Symbol) :
      ArraySeek.frame (tapeCount := 4) (fun _ : Fin 4 => default) bits scratch flag array = frame bits scratch flag array := by
    funext name
    fin_cases name <;> rfl
  have trace := ArraySeek.runs (tapeCount := 4) (fun _ : Fin 4 => default) (fun _ => 0) (advance elementWidth)
    (Fin.last elementWidth) 0 elementWidth elementWidth
    (by
      intro bits scratch flag array arrayWidth offset
      simpa only [widthsEqual, readonlyEqual, frameEqual, positionEqual, machine, entry, exit] using
        advance_runs elementWidth bits scratch flag array arrayWidth offset)
    (by intro symbols; simp [advance, MultiTape.wire, Move.machine])
    bits scratch sameLength flag array arrayWidth offset
  simpa only [widthsEqual, readonlyEqual, frameEqual, positionEqual, machine, entry, exit] using trace

end Polytime2.FixedArraySeek
