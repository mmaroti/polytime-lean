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

import Polytime2.Arrays.Seek
import Polytime2.Arithmetic.BinaryGuard
import Polytime2.Primitives.UnaryMove

/-! # Runtime-width specialization of shared array navigation -/

namespace Polytime2.RuntimeArraySeek

open MultiTape CallingConvention
open Binary (Symbol data word value)

private instance : Fact (4 ≤ 5) := ⟨by decide⟩

abbrev Alphabet := CallingConvention.Alphabet (Fin 5)

/-- The width-specific command uses the common navigation layout. -/
def frame (elementWidth : ℕ) (counter : List Bool) (scratch : List Symbol) (flag : Symbol)
    (array : Turing.Tape Symbol) : Tapes Alphabet :=
  ArraySeek.frame (fun _ => unary elementWidth) counter scratch flag array

def widths (elementWidth : ℕ) (digits arrayWidth : ℕ) : Fin 5 → ℕ :=
  ArraySeek.widths (fun _ => elementWidth) digits arrayWidth

def readOnly : Fin 5 → Bool := ArraySeek.readOnly
abbrev position := ArraySeek.position (tapeCount := 5)

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
  have moved := (UnaryMove.runs elementWidth array
    (fun name => if name then arrayWidth else elementWidth) (fun _ => true)
    (fun name => if name then offset else 0)).wire_at_of_eq advanceWiring
      (widths elementWidth bits.length arrayWidth) readOnly
      (by intro name; cases name <;> rfl) (by intro name premise; rfl)
      (position offset) (position (offset + elementWidth))
      (frame elementWidth bits scratch flag array)
      (frame elementWidth bits scratch flag ((Turing.Tape.move .right)^[elementWidth] array))
      (by intro name; cases name <;> rfl) (by intro name; cases name <;> rfl)
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨false, rfl⟩) | exact False.elim (outside ⟨true, rfl⟩))
      (by intro name; cases name <;> rfl) (by intro name; cases name <;> rfl)
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨false, rfl⟩) | exact False.elim (outside ⟨true, rfl⟩))
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
  exact ArraySeek.runs (tapeCount := 5) (fun _ => unary elementWidth) (fun _ => elementWidth) advance
    (.inl false) (.inr (.inr 2)) elementWidth (2 * elementWidth + 5)
    (advance_runs elementWidth) (by intro symbols; simp [advance, MultiTape.wire])
    bits scratch sameLength flag array arrayWidth offset

end Polytime2.RuntimeArraySeek
