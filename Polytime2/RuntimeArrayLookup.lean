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

/-! # Lookup specialization of shared unary-width block copying -/

namespace Polytime2.RuntimeArrayLookup

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 7)

/-- Lookup reuses the indexed block-copy tape layout. -/
abbrev frame := RuntimeArrayBlockCopy.frame
abbrev widths := RuntimeArrayBlockCopy.widths
def readOnly : Fin 7 → Bool := RuntimeArrayBlockCopy.readOnly true

abbrev State := RuntimeArrayBlockCopy.State

noncomputable def machine : Machine Alphabet State := RuntimeArrayBlockCopy.machine true

def entry : State := RuntimeArrayBlockCopy.entry
def exit : State := RuntimeArrayBlockCopy.exit

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by simp [machine, exit]

abbrev initialFrame := RuntimeArrayBlockCopy.initialFrame

theorem runs (elementWidth : ℕ) (index beforeBits block afterBits : List Bool)
    (prefixLength : beforeBits.length = value index * elementWidth) (blockLength : block.length = elementWidth)
    (element oldCounter scratch : List Symbol) (elementLength : element.length = elementWidth)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) :
    ∃ ticks, ticks ≤ value index * (6 * index.length + 3 * elementWidth + 16) + 6 * index.length + 3 * elementWidth + 17 ∧
      Runs (widths elementWidth index.length (beforeBits ++ block ++ afterBits).length) readOnly machine
        ticks entry (fun _ => 0)
        (initialFrame elementWidth index (beforeBits ++ block ++ afterBits) element oldCounter scratch flag)
        exit (fun _ => 0)
        (frame elementWidth index (buffer (word (beforeBits ++ block ++ afterBits))) (word block)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨ticks, cost, trace⟩ := RuntimeArrayBlockCopy.runs true elementWidth index beforeBits block afterBits block
    prefixLength blockLength blockLength element oldCounter scratch elementLength counterLength scratchLength flag
    (by intro impossible; cases impossible)
  exact ⟨ticks, cost, by simpa [machine, entry, exit, readOnly] using trace⟩

-- parameterLevel: size names; carrierLevel: mathematical element types.
universe parameterLevel carrierLevel

/-- Mathematical arrays use the same lookup controller for every element
presentation. The block width is supplied on an immutable unary tape. -/
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
        (6 * index.length + 3 * elementDomain.width assignment + 16) +
        6 * index.length + 3 * elementDomain.width assignment + 17 ∧
      Runs (widths (elementDomain.width assignment) index.length
          ((EncodedDomain.arrayOfLength elementDomain length).width assignment))
        readOnly machine ticks
        entry (fun _ => 0)
        (initialFrame (elementDomain.width assignment) index
          (EncodedDomain.ArrayEncoding.bits
            ((EncodedDomain.arrayOfLength elementDomain length).encode assignment array))
          oldElement oldCounter scratch flag)
        exit (fun _ => 0)
        (frame (elementDomain.width assignment) index
          (CallingConvention.encoded (EncodedDomain.arrayOfLength elementDomain length) assignment array)
          (word (EncodedDomain.ArrayEncoding.bits
            (elementDomain.encode assignment (array ⟨value index, within⟩))))
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) := by
  have lifted := EncodedDomain.array_lookup_of_blocks elementDomain length assignment (value index) within array
    (6 * index.length + 3 * (elementDomain.width assignment) + 16) (6 * index.length + 3 * (elementDomain.width assignment) + 17)
    (fun ticks arrayWidth arrayBits elementBits =>
      Runs (widths (elementDomain.width assignment) index.length arrayWidth) readOnly machine ticks
        entry (fun _ => 0) (initialFrame (elementDomain.width assignment) index arrayBits oldElement oldCounter scratch flag)
        exit (fun _ => 0) (frame (elementDomain.width assignment) index (buffer (word arrayBits)) (word elementBits)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)))
    (by
      intro before block after prefixLength blockLength
      simpa only [Nat.add_assoc] using runs (elementDomain.width assignment) index before block after prefixLength blockLength oldElement oldCounter scratch
        elementLength counterLength scratchLength flag)
  simpa only [Nat.add_assoc, encoded, tape, buffer] using lifted

end Polytime2.RuntimeArrayLookup
