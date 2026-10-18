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

/-- The width-specific command uses the common navigation layout. -/
def frame (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) : Tapes Alphabet :=
  ArraySeek.frame (fun _ => default) counter scratch flag array

def widths (digits arrayWidth : ℕ) : Fin 4 → ℕ :=
  ArraySeek.widths (fun _ => 0) digits arrayWidth

def readOnly : Fin 4 → Bool := ArraySeek.readOnly
abbrev position := ArraySeek.position (tapeCount := 4)

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
    (fun _ : Unit => true) (fun _ : Unit => offset) (fun _ : Unit => array)).wire_at_of_eq
      (oneTape (3 : Fin 4)) (widths bits.length arrayWidth) readOnly
      (by intro name; cases name; rfl) (by intro name premise; cases name; rfl)
      (position offset) (position (offset + elementWidth))
      (frame bits scratch flag array)
      (frame bits scratch flag ((Turing.Tape.move .right)^[elementWidth] array))
      (by intro name; cases name; rfl) (by intro name; cases name; simp [position, ArraySeek.position, displacement])
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))
      (by intro name; cases name; rfl) (by intro name; cases name; rfl)
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))
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
  exact ArraySeek.runs (tapeCount := 4) (fun _ => default) (fun _ => 0) (advance elementWidth)
    (Fin.last elementWidth) 0 elementWidth elementWidth (advance_runs elementWidth)
    (by intro symbols; simp [advance, MultiTape.wire, Move.machine])
    bits scratch sameLength flag array arrayWidth offset

end Polytime2.FixedArraySeek
