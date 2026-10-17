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

import Polytime2.ArrayBlockCopy
import Polytime2.RuntimeArraySeek
import Polytime2.UnaryCopy

/-! # Unary-width commands for shared indexed block copying -/

namespace Polytime2.RuntimeArrayBlockCopy

open MultiTape CallingConvention
open Binary (Symbol data word value)

private instance : Fact (6 ≤ 7) := ⟨by decide⟩

abbrev Alphabet := CallingConvention.Alphabet (Fin 7)
abbrev State := ArrayBlockCopy.State RuntimeArraySeek.State (Fin 4)

def frame (elementWidth : ℕ) (index : List Bool) (array : Turing.Tape Symbol) (scalar : List Symbol)
    (counter : List Bool) (scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  ArrayBlockCopy.frame (fun _ : Fin 7 => unary elementWidth) index array scalar counter scratch flag

def widths (elementWidth digits arrayWidth : ℕ) : Fin 7 → ℕ :=
  ArrayBlockCopy.widths (fun _ : Fin 7 => elementWidth) elementWidth digits arrayWidth

def readOnly (sourceIsArray : Bool) : Fin 7 → Bool := ArrayBlockCopy.readOnly sourceIsArray
def position (offset : ℤ) : Fin 7 → ℤ := ArrayBlockCopy.position offset

def seekWiring : Fin 5 ↪ Fin 7 :=
  ⟨(fun name => match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 1 | _ => 6), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def transferWiring (sourceIsArray : Bool) : Fin 3 ↪ Fin 7 :=
  ⟨(fun name => if name = 0 then 6 else if decide (name = 1) = sourceIsArray then 1 else 2), by
    intro first second equal
    cases sourceIsArray <;> fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 5) : seekWiring name =
    (match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 1 | _ => 6) := rfl
@[simp] theorem transferWiring_apply (sourceIsArray : Bool) (name : Fin 3) :
    transferWiring sourceIsArray name = (if name = 0 then 6 else if decide (name = 1) = sourceIsArray then 1 else 2) := rfl

noncomputable def seek : Machine Alphabet RuntimeArraySeek.State := MultiTape.wire seekWiring RuntimeArraySeek.machine
noncomputable def transfer (sourceIsArray : Bool) : Machine Alphabet (Fin 4) :=
  MultiTape.wire (transferWiring sourceIsArray) UnaryCopy.machine
noncomputable def machine (sourceIsArray : Bool) : Machine Alphabet State :=
  ArrayBlockCopy.machine seek RuntimeArraySeek.entry (transfer sourceIsArray) 0

def entry : State := ArrayBlockCopy.entry _ _
def exit : State := ArrayBlockCopy.exit _ _

def initialFrame (elementWidth : ℕ) (index array : List Bool) (scalar counter scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  ArrayBlockCopy.initialFrame (fun _ : Fin 7 => unary elementWidth) index array scalar counter scratch flag

@[simp] theorem halt (sourceIsArray : Bool) (symbols : Symbols Alphabet) : machine sourceIsArray exit symbols = none := by
  simp [machine, exit]

private theorem seek_runs (sourceIsArray : Bool) (elementWidth : ℕ)
    (index : List Bool) (scratch : List Symbol) (sameLength : scratch.length = index.length)
    (flag : Symbol) (array : Turing.Tape Symbol) (scalar : List Symbol) (arrayWidth : ℕ) :
    Runs (widths elementWidth index.length arrayWidth) (readOnly sourceIsArray) seek
      (value index * (6 * index.length + 2 * elementWidth + 16) + 4 * index.length + 6)
      RuntimeArraySeek.entry (position 0) (frame elementWidth index array scalar index scratch flag)
      RuntimeArraySeek.exit (position (value index * elementWidth))
      (frame elementWidth index ((Turing.Tape.move .right)^[value index * elementWidth] array) scalar
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  have trace := (RuntimeArraySeek.runs elementWidth index scratch sameLength flag array arrayWidth 0).wire_at_of_eq
    seekWiring (widths elementWidth index.length arrayWidth) (readOnly sourceIsArray)
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> first | rfl | simp [readOnly, ArrayBlockCopy.readOnly, seekWiring_apply] at premise)
    (position 0) (position (value index * elementWidth))
    (frame elementWidth index array scalar index scratch flag)
    (frame elementWidth index ((Turing.Tape.move .right)^[value index * elementWidth] array) scalar
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> simp [position, ArrayBlockCopy.position, RuntimeArraySeek.position, seekWiring_apply])
    (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨0, rfl⟩) | exact False.elim (outside ⟨1, rfl⟩) | exact False.elim (outside ⟨2, rfl⟩) | exact False.elim (outside ⟨3, rfl⟩))
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨0, rfl⟩) | exact False.elim (outside ⟨1, rfl⟩) | exact False.elim (outside ⟨2, rfl⟩) | exact False.elim (outside ⟨3, rfl⟩))
  simpa only [zero_add, ← Nat.cast_mul, seek] using trace

private theorem transfer_runs (sourceIsArray : Bool) (elementWidth : ℕ)
    (index before block after replacement : List Bool) (scalar : List Symbol)
    (blockLength : block.length = elementWidth) (replacementLength : replacement.length = elementWidth)
    (scalarLength : scalar.length = elementWidth) (scalarInput : sourceIsArray = false → scalar = word replacement) :
    Runs (widths elementWidth index.length (before ++ block ++ after).length) (readOnly sourceIsArray)
      (transfer sourceIsArray) (3 * elementWidth + 3)
      0 (position before.length)
      (frame elementWidth index (ArrayBlockCopy.selectedArray before block after) scalar
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
      3 (position before.length)
      (frame elementWidth index (ArrayBlockCopy.selectedArray before (if sourceIsArray then block else replacement) after)
        (if sourceIsArray then word block else scalar)
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  let initial := frame elementWidth index (ArrayBlockCopy.selectedArray before block after) scalar
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  let final := frame elementWidth index (ArrayBlockCopy.selectedArray before (if sourceIsArray then block else replacement) after)
    (if sourceIsArray then word block else scalar)
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  let localWidth := fun name => widths elementWidth index.length (before ++ block ++ after).length (transferWiring sourceIsArray name)
  let localPosition := fun name => position before.length (transferWiring sourceIsArray name)
  cases sourceIsArray with
  | true =>
    have trace := (UnaryCopy.runs (word block) scalar (by simpa [word, blockLength] using scalarLength)
      (word before.reverse ++ [0]) (word after ++ [0]) [0] [0]
      localWidth localPosition (by simp [localWidth, localPosition, widths, ArrayBlockCopy.widths,
        position, ArrayBlockCopy.position, transferWiring_apply, word, blockLength])).wire_at_of_eq
        (transferWiring true) (widths elementWidth index.length (before ++ block ++ after).length) (readOnly true)
        (by intro name; rfl)
        (by intro name premise; fin_cases name <;> first | rfl | contradiction)
        (position before.length) (position before.length) initial final
        (by intro name; rfl) (by intro name; rfl) (by intro name outside; rfl)
        (by intro name; fin_cases name <;> simp [initial, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, UnaryCopy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, unary, CallingConvention.tape, buffer, blockLength])
        (by intro name; fin_cases name <;> simp [final, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, UnaryCopy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, unary, CallingConvention.tape, buffer, blockLength])
        (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨0, rfl⟩) | exact False.elim (outside ⟨1, rfl⟩) | exact False.elim (outside ⟨2, rfl⟩))
    simpa only [initial, final, transfer, word, List.length_map, blockLength, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] using trace
  | false =>
    obtain rfl := scalarInput rfl
    have trace := (UnaryCopy.runs (word replacement) (word block) (by simp [word, blockLength, replacementLength])
      [0] [0] (word before.reverse ++ [0]) (word after ++ [0])
      localWidth localPosition (by simp [localWidth, localPosition, widths, ArrayBlockCopy.widths,
        position, ArrayBlockCopy.position, transferWiring_apply, word, blockLength, replacementLength])).wire_at_of_eq
        (transferWiring false) (widths elementWidth index.length (before ++ block ++ after).length) (readOnly false)
        (by intro name; rfl)
        (by intro name premise; fin_cases name <;> first | rfl | contradiction)
        (position before.length) (position before.length) initial final
        (by intro name; rfl) (by intro name; rfl) (by intro name outside; rfl)
        (by intro name; fin_cases name <;> simp [initial, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, UnaryCopy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, unary, CallingConvention.tape, buffer, replacementLength])
        (by intro name; fin_cases name <;> simp [final, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, UnaryCopy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, unary, CallingConvention.tape, buffer, replacementLength])
        (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨0, rfl⟩) | exact False.elim (outside ⟨1, rfl⟩) | exact False.elim (outside ⟨2, rfl⟩))
    simpa only [initial, final, transfer, word, List.length_map, replacementLength, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] using trace

theorem runs (sourceIsArray : Bool) (elementWidth : ℕ) (index before block after replacement : List Bool)
    (prefixLength : before.length = value index * elementWidth)
    (blockLength : block.length = elementWidth) (replacementLength : replacement.length = elementWidth)
    (scalar oldCounter scratch : List Symbol) (scalarLength : scalar.length = elementWidth)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) (scalarInput : sourceIsArray = false → scalar = word replacement) :
    ∃ ticks, ticks ≤ value index * (6 * index.length + 3 * elementWidth + 16) + 6 * index.length + 3 * elementWidth + 17 ∧
      Runs (widths elementWidth index.length (before ++ block ++ after).length) (readOnly sourceIsArray)
        (machine sourceIsArray) ticks entry (fun _ => 0)
        (initialFrame elementWidth index (before ++ block ++ after) scalar oldCounter scratch flag)
        exit (fun _ => 0)
        (frame elementWidth index (buffer (word (before ++ (if sourceIsArray then block else replacement) ++ after)))
          (if sourceIsArray then word block else scalar)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨ticks, cost, trace⟩ := ArrayBlockCopy.runs (fun _ : Fin 7 => unary elementWidth) (fun _ => elementWidth)
    sourceIsArray elementWidth (3 * elementWidth + 3) (fun digits => 6 * digits + 2 * elementWidth + 16)
    seek RuntimeArraySeek.entry RuntimeArraySeek.exit
    (transfer sourceIsArray) 0 3
    (by intro symbols; simp [seek, MultiTape.wire]) (by intro symbols; simp [transfer, MultiTape.wire, UnaryCopy.machine])
    (seek_runs sourceIsArray elementWidth) (transfer_runs sourceIsArray elementWidth)
    index before block after replacement prefixLength blockLength replacementLength scalar oldCounter scratch
    scalarLength counterLength scratchLength flag scalarInput
  exact ⟨ticks, by nlinarith [cost], trace⟩

end Polytime2.RuntimeArrayBlockCopy
