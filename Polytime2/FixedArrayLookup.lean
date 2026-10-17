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

import Polytime2.FixedArrayBlockCopy
import Polytime2.EncodedArray

/-! # Lookup specialization of shared fixed-width block copying -/

namespace Polytime2.FixedArrayLookup

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 6)

/-- Original index, immutable array, result element, private counter, private
decrement word, and guard bit. -/
def frame (index : List Bool) (array : Turing.Tape Symbol) (element : List Symbol)
    (counter : List Bool) (scratch : List Symbol) (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word index)
  else if name = 1 then array
  else if name = 2 then buffer element
  else if name = 3 then buffer (word counter)
  else if name = 4 then buffer scratch
  else buffer [flag]

def widths (elementWidth digits arrayWidth : ℕ) (name : Fin 6) : ℕ :=
  if name = 1 then arrayWidth else if name = 2 then elementWidth else if name = 5 then 1 else digits

def readOnly (name : Fin 6) : Bool := decide (name = 0 ∨ name = 1)


abbrev State (elementWidth : ℕ) := FixedArrayBlockCopy.State elementWidth

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  FixedArrayBlockCopy.machine true elementWidth

def entry (elementWidth : ℕ) : State elementWidth := FixedArrayBlockCopy.entry elementWidth
def exit (elementWidth : ℕ) : State elementWidth := FixedArrayBlockCopy.exit elementWidth

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by simp [machine, exit]

def initialFrame (index array : List Bool) (element counter scratch : List Symbol) (flag : Symbol) :
    Tapes Alphabet := Function.update
      (frame index (buffer (word array)) element (List.replicate index.length false) scratch flag) 3 (buffer counter)

theorem runs (elementWidth : ℕ) (index beforeBits block afterBits : List Bool)
    (prefixLength : beforeBits.length = value index * elementWidth) (blockLength : block.length = elementWidth)
    (element oldCounter scratch : List Symbol) (elementLength : element.length = elementWidth)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) :
    ∃ ticks, ticks ≤ value index * (6 * index.length + 2 * elementWidth + 11) + 6 * index.length + 2 * elementWidth + 15 ∧
      Runs (widths elementWidth index.length (beforeBits ++ block ++ afterBits).length) readOnly (machine elementWidth)
        ticks (entry elementWidth) (fun _ => 0)
        (initialFrame index (beforeBits ++ block ++ afterBits) element oldCounter scratch flag)
        (exit elementWidth) (fun _ => 0)
        (frame index (buffer (word (beforeBits ++ block ++ afterBits))) (word block)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  have widthsEqual : FixedArrayBlockCopy.widths elementWidth index.length (beforeBits ++ block ++ afterBits).length =
      widths elementWidth index.length (beforeBits ++ block ++ afterBits).length := by
    funext name
    fin_cases name <;> rfl
  have readonlyEqual : FixedArrayBlockCopy.readOnly true = readOnly := by
    funext name
    fin_cases name <;> rfl
  have frameEqual (array : Turing.Tape Symbol) (element : List Symbol) (counter : List Bool)
      (scratch : List Symbol) (flag : Symbol) :
      FixedArrayBlockCopy.frame index array element counter scratch flag = frame index array element counter scratch flag := by
    funext name
    fin_cases name <;> rfl
  have initialEqual : FixedArrayBlockCopy.initialFrame index (beforeBits ++ block ++ afterBits)
      element oldCounter scratch flag = initialFrame index (beforeBits ++ block ++ afterBits) element oldCounter scratch flag := by
    funext name
    fin_cases name <;> simp [FixedArrayBlockCopy.initialFrame, ArrayBlockCopy.initialFrame,
      initialFrame, frame, ArrayBlockCopy.frame]
  obtain ⟨ticks, cost, trace⟩ := FixedArrayBlockCopy.runs true elementWidth index beforeBits block afterBits block
    prefixLength blockLength blockLength element oldCounter scratch elementLength counterLength scratchLength flag
    (by intro impossible; cases impossible)
  refine ⟨ticks, cost, ?_⟩
  simpa only [widthsEqual, readonlyEqual, frameEqual, initialEqual, ↓reduceIte, machine, entry, exit] using trace

-- parameterLevel: size names; carrierLevel: mathematical element types.
universe parameterLevel carrierLevel

/-- Mathematical arrays use the same lookup controller for every element
presentation. Only the fixed block width is visible to the controller. -/
theorem encoded_runsOfLength {Parameter : Type parameterLevel} [Fintype Parameter]
    (elementDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (length : MvPolynomial Parameter ℕ) (assignment : Parameter → ℕ)
    (index : List Bool) (within : value index < MvPolynomial.eval assignment length)
    (array : (EncodedDomain.arrayOfLength elementDomain length).Carrier assignment)
    (oldElement oldCounter scratch : List Symbol)
    (elementLength : oldElement.length = elementDomain.width assignment)
    (counterLength : oldCounter.length = index.length)
    (scratchLength : scratch.length = index.length) (flag : Symbol) :
    ∃ ticks,
      ticks ≤ MvPolynomial.eval assignment length *
        (6 * index.length + 2 * elementDomain.width assignment + 11) +
        6 * index.length + 2 * elementDomain.width assignment + 15 ∧
      Runs (widths (elementDomain.width assignment) index.length
          ((EncodedDomain.arrayOfLength elementDomain length).width assignment))
        readOnly (machine (elementDomain.width assignment)) ticks
        (entry (elementDomain.width assignment)) (fun _ => 0)
        (initialFrame index
          (EncodedDomain.ArrayEncoding.bits
            ((EncodedDomain.arrayOfLength elementDomain length).encode assignment array))
          oldElement oldCounter scratch flag)
        (exit (elementDomain.width assignment)) (fun _ => 0)
        (frame index
          (CallingConvention.encoded (EncodedDomain.arrayOfLength elementDomain length) assignment array)
          (word (EncodedDomain.ArrayEncoding.bits
            (elementDomain.encode assignment (array ⟨value index, within⟩))))
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨beforeBits, afterBits, decomposition, prefixLength⟩ :=
    EncodedDomain.ArrayEncoding.split_encode (elementDomain.encode assignment)
      (MvPolynomial.eval assignment length) array ⟨value index, within⟩
  let block := EncodedDomain.ArrayEncoding.bits
    (elementDomain.encode assignment (array ⟨value index, within⟩))
  have blockLength : block.length = elementDomain.width assignment := List.length_ofFn
  obtain ⟨ticks, cost, trace⟩ := runs (elementDomain.width assignment) index
    beforeBits block afterBits prefixLength blockLength oldElement oldCounter scratch
    elementLength counterLength scratchLength flag
  refine ⟨ticks, cost.trans ?_, ?_⟩
  · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.le_of_lt within)) _) _) _
  · have encodedLength : (beforeBits ++ block ++ afterBits).length =
        (EncodedDomain.arrayOfLength elementDomain length).width assignment := by
      rw [← decomposition]
      simp [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits]
    rw [encodedLength] at trace
    have whole : EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.arrayOfLength elementDomain length).encode assignment array) =
        beforeBits ++ block ++ afterBits := by
      simpa only [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.array_encode_bits] using decomposition
    simp only [← whole] at trace
    exact trace

end Polytime2.FixedArrayLookup
