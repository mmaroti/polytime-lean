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

import Polytime2.Arrays.BlockCopy
import Polytime2.Arrays.FixedSeek
import Polytime2.Primitives.Copy

/-! # Fixed-width commands for shared indexed block copying -/

namespace Polytime2.FixedArrayBlockCopy

open MultiTape CallingConvention
open Binary (Symbol data word value)

private instance : Fact (6 ≤ 6) := ⟨by decide⟩

abbrev Alphabet := CallingConvention.Alphabet (Fin 6)
abbrev State (elementWidth : ℕ) := ArrayBlockCopy.State (FixedArraySeek.State elementWidth) (Copy.State elementWidth)

def frame (index : List Bool) (array : Turing.Tape Symbol) (scalar : List Symbol)
    (counter : List Bool) (scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  ArrayBlockCopy.frame (fun _ : Fin 6 => default) index array scalar counter scratch flag

def widths (elementWidth digits arrayWidth : ℕ) : Fin 6 → ℕ :=
  ArrayBlockCopy.widths (fun _ : Fin 6 => 0) elementWidth digits arrayWidth

def readOnly (sourceIsArray : Bool) : Fin 6 → Bool := ArrayBlockCopy.readOnly sourceIsArray
def position (offset : ℤ) : Fin 6 → ℤ := ArrayBlockCopy.position offset

def seekWiring : Fin 4 ↪ Fin 6 :=
  ⟨(fun name => match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | _ => 1), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def transferWiring (sourceIsArray : Bool) : Bool ↪ Fin 6 :=
  ⟨(fun name => if name = sourceIsArray then 2 else 1), by
    intro first second equal
    cases sourceIsArray <;> cases first <;> cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 4) : seekWiring name =
    (match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | _ => 1) := rfl
@[simp] theorem transferWiring_apply (sourceIsArray name : Bool) :
    transferWiring sourceIsArray name = (if name = sourceIsArray then 2 else 1) := rfl

noncomputable def seek (elementWidth : ℕ) : Machine Alphabet (FixedArraySeek.State elementWidth) :=
  MultiTape.wire seekWiring (FixedArraySeek.machine elementWidth)

noncomputable def transfer (sourceIsArray : Bool) (elementWidth : ℕ) : Machine Alphabet (Copy.State elementWidth) :=
  MultiTape.wire (transferWiring sourceIsArray) (Copy.machine elementWidth)

noncomputable def machine (sourceIsArray : Bool) (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  ArrayBlockCopy.machine (seek elementWidth) (FixedArraySeek.entry elementWidth)
    (transfer sourceIsArray elementWidth) (false, Fin.last elementWidth)

def entry (elementWidth : ℕ) : State elementWidth := ArrayBlockCopy.entry _ _
def exit (elementWidth : ℕ) : State elementWidth := ArrayBlockCopy.exit _ _

def initialFrame (index array : List Bool) (scalar counter scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  ArrayBlockCopy.initialFrame (fun _ : Fin 6 => default) index array scalar counter scratch flag

@[simp] theorem halt (sourceIsArray : Bool) (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine sourceIsArray elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit]

private theorem seek_runs (sourceIsArray : Bool) (elementWidth : ℕ)
    (index : List Bool) (scratch : List Symbol) (sameLength : scratch.length = index.length)
    (flag : Symbol) (array : Turing.Tape Symbol) (scalar : List Symbol) (arrayWidth : ℕ) :
    Runs (widths elementWidth index.length arrayWidth) (readOnly sourceIsArray) (seek elementWidth)
      (value index * (6 * index.length + elementWidth + 11) + 4 * index.length + 6)
      (FixedArraySeek.entry elementWidth) (position 0) (frame index array scalar index scratch flag)
      (FixedArraySeek.exit elementWidth) (position (value index * elementWidth))
      (frame index ((Turing.Tape.move .right)^[value index * elementWidth] array) scalar
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  have trace := (FixedArraySeek.runs elementWidth index scratch sameLength flag array arrayWidth 0).wire_at_of_eq
    seekWiring (widths elementWidth index.length arrayWidth) (readOnly sourceIsArray)
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> first | rfl | simp [readOnly, ArrayBlockCopy.readOnly, seekWiring_apply] at premise)
    (position 0) (position (value index * elementWidth))
    (frame index array scalar index scratch flag)
    (frame index ((Turing.Tape.move .right)^[value index * elementWidth] array) scalar
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> simp [position, ArrayBlockCopy.position, ArraySeek.position, FixedArraySeek.position, seekWiring_apply])
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
      (transfer sourceIsArray elementWidth) (2 * elementWidth + 1)
      (false, Fin.last elementWidth) (position before.length)
      (frame index (ArrayBlockCopy.selectedArray before block after) scalar
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
      (true, 0) (position before.length)
      (frame index (ArrayBlockCopy.selectedArray before (if sourceIsArray then block else replacement) after)
        (if sourceIsArray then word block else scalar)
        (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  let initial := frame index (ArrayBlockCopy.selectedArray before block after) scalar
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  let final := frame index (ArrayBlockCopy.selectedArray before (if sourceIsArray then block else replacement) after)
    (if sourceIsArray then word block else scalar)
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  let source := if sourceIsArray then block else replacement
  let target := if sourceIsArray then scalar else word block
  have sourceLength : source.length = elementWidth := by cases sourceIsArray <;> assumption
  have targetLength : target.length = elementWidth := by
    cases sourceIsArray <;> simp_all [target, word]
  let localWidth := fun name => widths elementWidth index.length (before ++ block ++ after).length (transferWiring sourceIsArray name)
  let localPosition := fun name => position before.length (transferWiring sourceIsArray name)
  have trace := (StandardCopy.slice_runs elementWidth source target sourceLength targetLength
    (if sourceIsArray then word before.reverse ++ [0] else [0])
    (if sourceIsArray then word after ++ [0] else [0])
    (if sourceIsArray then [0] else word before.reverse ++ [0])
    (if sourceIsArray then [0] else word after ++ [0])
    localWidth localPosition (by
      cases sourceIsArray <;> simp [localWidth, localPosition, widths, ArrayBlockCopy.widths,
        position, ArrayBlockCopy.position, transferWiring_apply, blockLength])).wire_at_of_eq
      (transferWiring sourceIsArray) (widths elementWidth index.length (before ++ block ++ after).length) (readOnly sourceIsArray)
      (by intro name; rfl)
      (by intro name premise; cases sourceIsArray <;> cases name <;> first | rfl | contradiction)
      (position before.length) (position before.length) initial final
      (by intro name; rfl) (by intro name; rfl) (by intro name outside; rfl)
      (by
        intro name
        cases sourceIsArray <;> cases name <;>
          simp [source, target, initial, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, Copy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, scalarInput])
      (by
        intro name
        cases sourceIsArray <;> cases name <;>
          simp [source, final, frame, ArrayBlockCopy.frame, ArrayBlockCopy.selectedArray, transferWiring_apply, Copy.frame, Binary.tape, word, List.map_append, List.append_assoc, buffer_padding, scalarInput])
      (by intro name outside; cases sourceIsArray <;> fin_cases name <;> first | rfl | exact False.elim (outside ⟨false, rfl⟩) | exact False.elim (outside ⟨true, rfl⟩))
  simpa only [initial, final, transfer] using trace

theorem runs (sourceIsArray : Bool) (elementWidth : ℕ) (index before block after replacement : List Bool)
    (prefixLength : before.length = value index * elementWidth)
    (blockLength : block.length = elementWidth) (replacementLength : replacement.length = elementWidth)
    (scalar oldCounter scratch : List Symbol) (scalarLength : scalar.length = elementWidth)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) (scalarInput : sourceIsArray = false → scalar = word replacement) :
    ∃ ticks, ticks ≤ value index * (6 * index.length + 2 * elementWidth + 11) + 6 * index.length + 2 * elementWidth + 15 ∧
      Runs (widths elementWidth index.length (before ++ block ++ after).length) (readOnly sourceIsArray)
        (machine sourceIsArray elementWidth) ticks (entry elementWidth) (fun _ => 0)
        (initialFrame index (before ++ block ++ after) scalar oldCounter scratch flag)
        (exit elementWidth) (fun _ => 0)
        (frame index (buffer (word (before ++ (if sourceIsArray then block else replacement) ++ after)))
          (if sourceIsArray then word block else scalar)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨ticks, cost, trace⟩ := ArrayBlockCopy.runs (fun _ : Fin 6 => default) (fun _ => 0)
    sourceIsArray elementWidth (2 * elementWidth + 1) (fun digits => 6 * digits + elementWidth + 11)
    (seek elementWidth) (FixedArraySeek.entry elementWidth) (FixedArraySeek.exit elementWidth)
    (transfer sourceIsArray elementWidth) (false, Fin.last elementWidth) (true, 0)
    (by intro symbols; simp [seek, MultiTape.wire]) (by intro symbols; simp [transfer, MultiTape.wire, Copy.machine])
    (seek_runs sourceIsArray elementWidth) (transfer_runs sourceIsArray elementWidth)
    index before block after replacement prefixLength blockLength replacementLength scalar oldCounter scratch
    scalarLength counterLength scratchLength flag scalarInput
  exact ⟨ticks, by nlinarith [cost], trace⟩

end Polytime2.FixedArrayBlockCopy
