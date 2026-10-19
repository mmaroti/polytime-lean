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

import Polytime2.Arrays.RuntimeBlockCopy
import Polytime2.Arrays.Update
import Polytime2.Encoding.EncodedArray

/-! # Separate-output update through shared unary-width block copying -/

namespace Polytime2.RuntimeArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)

/-- Update shares the separate-result layout and controller for both width modes. -/
def frame (elementWidth : ℕ) (index : List Bool) (array : Turing.Tape Symbol) (element : List Symbol)
    (result : Turing.Tape Symbol) (counter : List Bool) (scratch : List Symbol)
    (flag : Symbol) : Tapes Alphabet :=
  ArrayUpdate.frame (extra := 1) (fun _ => unary elementWidth) index array element result counter scratch flag

def widths (elementWidth digits arrayWidth : ℕ) : Fin 8 → ℕ :=
  ArrayUpdate.widths (extra := 1) (fun _ => elementWidth) elementWidth digits arrayWidth

def readOnly : Fin 8 → Bool := ArrayUpdate.readOnly (extra := 1)

abbrev State := Sum (Fin 3) (RuntimeArrayBlockCopy.State)

noncomputable def machine : Machine Alphabet (State) :=
  ArrayUpdate.machine (extra := 1) (RuntimeArrayBlockCopy.machine false) (RuntimeArrayBlockCopy.entry)

def entry : State := .inl 0
def exit : State := .inr (RuntimeArrayBlockCopy.exit)

@[simp] theorem halt (symbols : Symbols Alphabet) :
    machine (exit) symbols = none := by
  simp [machine, exit, ArrayUpdate.machine, ArrayUpdate.access, MultiTape.sequence, MultiTape.wire]

def initialFrame (elementWidth : ℕ) (index array : List Bool) (element result counter scratch : List Symbol)
    (flag : Symbol) : Tapes Alphabet :=
  ArrayUpdate.initialFrame (extra := 1) (fun _ => unary elementWidth) index array element result counter scratch flag

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
  obtain ⟨ticks, cost, trace⟩ := ArrayUpdate.runs (extra := 1) (fun _ => unary elementWidth)
    (fun _ => elementWidth) elementWidth (6 * index.length + 3 * elementWidth + 16) (6 * index.length + 3 * elementWidth + 17)
    (RuntimeArrayBlockCopy.machine false) (RuntimeArrayBlockCopy.entry) (RuntimeArrayBlockCopy.exit)
    index before block after replacement oldOutput oldCounter scratch flag outputLength
    (by
      simpa only [Nat.add_assoc, Bool.false_eq_true, ↓reduceIte, RuntimeArrayBlockCopy.widths,
        RuntimeArrayBlockCopy.readOnly, RuntimeArrayBlockCopy.initialFrame, RuntimeArrayBlockCopy.frame] using
        RuntimeArrayBlockCopy.runs false elementWidth index before block after replacement
        prefixLength blockLength replacementLength (word replacement) oldCounter scratch
        (by simp [word, replacementLength]) counterLength scratchLength flag (by intro premise; rfl))
  exact ⟨ticks, by nlinarith [cost, prefixLength], trace⟩

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
  let replacementBits := EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)
  have lifted := EncodedDomain.array_update_of_blocks element length sizes (value index) within array replacement
    (6 * index.length + 3 * (element.width sizes) + 16) (6 * index.length + 3 * (element.width sizes) + 20)
    (fun ticks arrayWidth arrayBits updatedBits =>
      Runs (widths (element.width sizes) index.length arrayWidth) readOnly machine ticks
        entry (fun _ => 0) (initialFrame (element.width sizes) index arrayBits (word replacementBits)
          oldOutput oldCounter scratch flag) exit (fun _ => 0)
        (frame (element.width sizes) index (buffer (word arrayBits)) (word replacementBits) (buffer (word updatedBits))
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)))
    (by
      intro before block after prefixLength blockLength wholeLength
      obtain ⟨ticks, cost, trace⟩ := runs (element.width sizes) index before block after replacementBits
        prefixLength blockLength List.length_ofFn oldOutput oldCounter scratch
        (outputLength.trans wholeLength.symm) counterLength scratchLength flag
      exact ⟨ticks, by nlinarith [cost, prefixLength], trace⟩)
  have unitEq : 6 * index.length + 3 * (element.width sizes) + 16 + 2 * (element.width sizes) =
      6 * index.length + 5 * (element.width sizes) + 16 := by omega
  rw [unitEq] at lifted
  simpa only [Nat.add_assoc, replacementBits, encoded, tape, buffer] using lifted

end Polytime2.RuntimeArrayUpdate
