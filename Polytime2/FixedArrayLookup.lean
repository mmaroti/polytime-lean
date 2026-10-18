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

/-- Lookup reuses the indexed block-copy tape layout. -/
abbrev frame := FixedArrayBlockCopy.frame
abbrev widths := FixedArrayBlockCopy.widths
def readOnly : Fin 6 → Bool := FixedArrayBlockCopy.readOnly true

abbrev State (elementWidth : ℕ) := FixedArrayBlockCopy.State elementWidth

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  FixedArrayBlockCopy.machine true elementWidth

def entry (elementWidth : ℕ) : State elementWidth := FixedArrayBlockCopy.entry elementWidth
def exit (elementWidth : ℕ) : State elementWidth := FixedArrayBlockCopy.exit elementWidth

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by simp [machine, exit]

abbrev initialFrame := FixedArrayBlockCopy.initialFrame

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
  obtain ⟨ticks, cost, trace⟩ := FixedArrayBlockCopy.runs true elementWidth index beforeBits block afterBits block
    prefixLength blockLength blockLength element oldCounter scratch elementLength counterLength scratchLength flag
    (by intro impossible; cases impossible)
  exact ⟨ticks, cost, by simpa [machine, entry, exit, readOnly] using trace⟩

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
  have lifted := EncodedDomain.array_lookup_of_blocks elementDomain length assignment (value index) within array
    (6 * index.length + 2 * (elementDomain.width assignment) + 11) (6 * index.length + 2 * (elementDomain.width assignment) + 15)
    (fun ticks arrayWidth arrayBits elementBits =>
      Runs (widths (elementDomain.width assignment) index.length arrayWidth) readOnly (machine (elementDomain.width assignment)) ticks
        (entry (elementDomain.width assignment)) (fun _ => 0) (initialFrame index arrayBits oldElement oldCounter scratch flag)
        (exit (elementDomain.width assignment)) (fun _ => 0) (frame index (buffer (word arrayBits)) (word elementBits)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)))
    (by
      intro before block after prefixLength blockLength
      simpa only [Nat.add_assoc] using runs (elementDomain.width assignment) index before block after prefixLength blockLength oldElement oldCounter scratch
        elementLength counterLength scratchLength flag)
  simpa only [Nat.add_assoc, encoded, tape, buffer] using lifted

end Polytime2.FixedArrayLookup
