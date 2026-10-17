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

import Polytime2.RuntimeArrayBlockCopy
import Polytime2.StandardTapeCommands
import Polytime2.EncodedArray

/-! # Separate-output update through shared unary-width block copying -/

namespace Polytime2.RuntimeArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)

/-- Index, source array, replacement, result array, counter, decrement scratch,
and a one-bit guard. -/
def frame (elementWidth : ℕ) (index : List Bool) (array : Turing.Tape Symbol) (element : List Symbol)
    (result : Turing.Tape Symbol) (counter : List Bool) (scratch : List Symbol)
    (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word index)
  else if name = 1 then array
  else if name = 2 then buffer element
  else if name = 3 then result
  else if name = 4 then buffer (word counter)
  else if name = 5 then buffer scratch
  else if name = 6 then buffer [flag] else unary elementWidth

def widths (elementWidth digits arrayWidth : ℕ) (name : Fin 8) : ℕ :=
  if name = 1 ∨ name = 3 then arrayWidth
  else if name = 2 ∨ name = 7 then elementWidth
  else if name = 6 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 0 ∨ name = 1 ∨ name = 2 ∨ name = 7)


def blockWiring : Fin 7 ↪ Fin 8 :=
  ⟨(fun name => match name.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 6 | _ => 7), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem blockWiring_apply (name : Fin 7) : blockWiring name =
    (match name.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 5 | 5 => 6 | _ => 7) := rfl

noncomputable def copyArray : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 1 3 (by decide)
noncomputable def access : Machine Alphabet RuntimeArrayBlockCopy.State :=
  MultiTape.wire blockWiring (RuntimeArrayBlockCopy.machine false)

abbrev State := Sum (Fin 3) RuntimeArrayBlockCopy.State

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence copyArray access RuntimeArrayBlockCopy.entry

def entry : State := .inl 0
def exit : State := .inr RuntimeArrayBlockCopy.exit

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, access, MultiTape.sequence, MultiTape.wire]

def initialFrame (elementWidth : ℕ) (index array : List Bool) (element : List Symbol) (result : List Symbol)
    (counter scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  Function.update
    (frame elementWidth index (buffer (word array)) element (buffer result) [] scratch flag)
    4 (buffer counter)

theorem runs (elementWidth : ℕ) (index before block after replacement : List Bool)
    (prefixLength : before.length = value index * elementWidth)
    (blockLength : block.length = elementWidth)
    (replacementLength : replacement.length = elementWidth)
    (oldOutput oldCounter scratch : List Symbol)
    (outputLength : oldOutput.length = (before ++ block ++ after).length)
    (counterLength : oldCounter.length = index.length)
    (scratchLength : scratch.length = index.length) (flag : Symbol) :
    ∃ ticks,
      ticks ≤ 2 * index.length + 2 + 2 * (before ++ block ++ after).length + 2 +
        value index * (6 * index.length + 2 * elementWidth + 16) + 4 * index.length + 6 +
        3 * elementWidth + 3 + before.length + 3 + 4 ∧
      Runs (widths elementWidth index.length (before ++ block ++ after).length) readOnly
        machine ticks entry (fun _ => 0)
        (initialFrame elementWidth index (before ++ block ++ after) (word replacement) oldOutput
          oldCounter scratch flag)
        exit (fun _ => 0)
        (frame elementWidth index (buffer (word (before ++ block ++ after))) (word replacement)
          (buffer (word (before ++ replacement ++ after)))
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) := by
  let arrayBits := before ++ block ++ after
  let width := widths elementWidth index.length arrayBits.length
  let initial := initialFrame elementWidth index arrayBits (word replacement) oldOutput oldCounter scratch flag
  let middle := Function.update initial 3 (buffer (word arrayBits))
  let final := frame elementWidth index (buffer (word arrayBits)) (word replacement)
    (buffer (word (before ++ replacement ++ after)))
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  have copied := StandardTapeCommands.copy_runs (1 : Fin 8) 3 (by decide) width readOnly rfl
    arrayBits oldOutput rfl rfl outputLength initial rfl rfl
  obtain ⟨ticks, cost, trace⟩ := RuntimeArrayBlockCopy.runs false elementWidth index before block after replacement
    prefixLength blockLength replacementLength (word replacement) oldCounter scratch
    (by simp [word, replacementLength]) counterLength scratchLength flag (by intro premise; rfl)
  have patched := trace.wire_of_eq blockWiring width readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
    middle final
    (by
      intro name
      fin_cases name <;> simp [middle, initial, initialFrame, frame, RuntimeArrayBlockCopy.initialFrame,
        ArrayBlockCopy.initialFrame, ArrayBlockCopy.frame, blockWiring_apply, arrayBits] <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by
      intro name outside
      fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
        | exact False.elim (outside ⟨3, rfl⟩)
        | exact False.elim (outside ⟨4, rfl⟩)
        | exact False.elim (outside ⟨5, rfl⟩))
  have complete := copied.sequence _ RuntimeArrayBlockCopy.entry
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) patched
  refine ⟨_, ?_, complete⟩
  nlinarith [cost]

-- parameterLevel: names of the immutable unary size arguments.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

theorem encoded_runsOfLength (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : List Bool) (within : value index < MvPolynomial.eval sizes length)
    (array : (element.arrayOfLength length).Carrier sizes) (replacement : element.Carrier sizes)
    (oldOutput oldCounter scratch : List Symbol)
    (outputLength : oldOutput.length = (element.arrayOfLength length).width sizes)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) : ∃ ticks,
      ticks ≤ MvPolynomial.eval sizes length * (6 * index.length + 5 * element.width sizes + 16) +
        6 * index.length + 3 * element.width sizes + 20 ∧
      Runs (widths (element.width sizes) index.length ((element.arrayOfLength length).width sizes))
        readOnly machine ticks entry (fun _ => 0)
        (initialFrame (element.width sizes) index
          (EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array))
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          oldOutput oldCounter scratch flag)
        exit (fun _ => 0)
        (frame (element.width sizes) index (encoded (element.arrayOfLength length) sizes array)
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          (encoded (element.arrayOfLength length) sizes (Function.update array ⟨value index, within⟩ replacement))
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨before, after, decomposition, prefixLength, updatedDecomposition⟩ :=
    EncodedDomain.ArrayEncoding.split_encode_update (element.encode sizes)
      (MvPolynomial.eval sizes length) array ⟨value index, within⟩ replacement
  let block := EncodedDomain.ArrayEncoding.bits (element.encode sizes (array ⟨value index, within⟩))
  let replacementBits := EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)
  have wholeLength : (before ++ block ++ after).length = (element.arrayOfLength length).width sizes := by
    rw [← decomposition]
    simp [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits]
  obtain ⟨ticks, cost, trace⟩ := runs (element.width sizes) index before block after replacementBits
    prefixLength List.length_ofFn List.length_ofFn oldOutput oldCounter scratch
    (outputLength.trans wholeLength.symm) counterLength scratchLength flag
  refine ⟨ticks, cost.trans ?_, ?_⟩
  · have indexBound : value index ≤ MvPolynomial.eval sizes length := Nat.le_of_lt within
    have bound := Nat.mul_le_mul_right (6 * index.length + 3 * element.width sizes + 16) indexBound
    have widthEq : (before ++ block ++ after).length = MvPolynomial.eval sizes length * element.width sizes :=
      by simpa [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec] using wholeLength
    nlinarith [prefixLength]
  · rw [wholeLength] at trace
    have arrayBitsEq : EncodedDomain.ArrayEncoding.bits
        ((element.arrayOfLength length).encode sizes array) = before ++ block ++ after := by
      simpa only [EncodedDomain.arrayOfLength_encode_bits] using decomposition
    have updatedBitsEq : EncodedDomain.ArrayEncoding.bits
        ((element.arrayOfLength length).encode sizes (Function.update array ⟨value index, within⟩ replacement)) =
        before ++ replacementBits ++ after := by
      simpa only [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits_cast] using updatedDecomposition
    have sourceEq : buffer (word (before ++ block ++ after)) =
        encoded (element.arrayOfLength length) sizes array :=
      congrArg (fun bits => buffer (word bits)) arrayBitsEq.symm
    have outputEq : buffer (word (before ++ replacementBits ++ after)) =
        encoded (element.arrayOfLength length) sizes (Function.update array ⟨value index, within⟩ replacement) :=
      congrArg (fun bits => buffer (word bits)) updatedBitsEq.symm
    rw [sourceEq, outputEq, ← arrayBitsEq] at trace
    exact trace


end Polytime2.RuntimeArrayUpdate
