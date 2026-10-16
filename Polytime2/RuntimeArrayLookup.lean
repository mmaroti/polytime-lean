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

import Polytime2.RuntimeArraySeek
import Polytime2.UnaryCopy
import Polytime2.StandardTapeCommands
import Polytime2.EncodedArray

/-! # Binary-indexed lookup with immutable input arrays

Copy the index into private storage, seek with binary counters, copy one
runtime-width element, and return the array head using its left blank.
The output element and every private tape may start arbitrarily.
-/

namespace Polytime2.RuntimeArrayLookup

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 7)

/-- Original index, immutable array, result element, private counter, private
decrement word, and guard bit. -/
def frame (elementWidth : ℕ) (index : List Bool) (array : Turing.Tape Symbol) (element : List Symbol)
    (counter : List Bool) (scratch : List Symbol) (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word index)
  else if name = 1 then array
  else if name = 2 then buffer element
  else if name = 3 then buffer (word counter)
  else if name = 4 then buffer scratch
  else if name = 5 then buffer [flag] else unary elementWidth

def widths (elementWidth digits arrayWidth : ℕ) (name : Fin 7) : ℕ :=
  if name = 1 then arrayWidth else if name = 2 ∨ name = 6 then elementWidth else if name = 5 then 1 else digits

def readOnly (name : Fin 7) : Bool := decide (name = 0 ∨ name = 1 ∨ name = 6)

def position (offset : ℤ) (name : Fin 7) : ℤ := if name = 1 then offset else 0

def seekWiring : Fin 5 ↪ Fin 7 :=
  ⟨(fun name => match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 1 | _ => 6), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def transferWiring : Fin 3 ↪ Fin 7 :=
  ⟨(fun name => match name.val with | 0 => 6 | 1 => 1 | _ => 2), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 5) :
    seekWiring name = (match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 1 | _ => 6) := rfl
@[simp] theorem transferWiring_apply (name : Fin 3) :
    transferWiring name = (match name.val with | 0 => 6 | 1 => 1 | _ => 2) := rfl

noncomputable def prepare : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 0 3 (by decide)
noncomputable def seek : Machine Alphabet RuntimeArraySeek.State :=
  MultiTape.wire seekWiring RuntimeArraySeek.machine
noncomputable def transfer : Machine Alphabet (Fin 4) :=
  MultiTape.wire transferWiring UnaryCopy.machine
noncomputable def restore : Machine Alphabet (Fin 3) :=
  MultiTape.wire (oneTape (1 : Fin 7)) StandardHead.BlankReturn.machine

abbrev State :=
  Sum (Fin 3) (Sum RuntimeArraySeek.State (Sum (Fin 4) (Fin 3)))

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence prepare
    (MultiTape.sequence seek
      (MultiTape.sequence transfer restore 0) (.inl 0))
    (Sum.inl RuntimeArraySeek.entry)

def entry : State := .inl 0
def exit : State := .inr (.inr (.inr 2))

@[simp] theorem halt (symbols : Symbols Alphabet) :
    machine exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, MultiTape.wire, oneTape,
    StandardHead.BlankReturn.machine]

def initialFrame (elementWidth : ℕ) (index array : List Bool) (element counter scratch : List Symbol) (flag : Symbol) :
    Tapes Alphabet := Function.update
      (frame elementWidth index (buffer (word array)) element (List.replicate index.length false) scratch flag) 3 (buffer counter)

private theorem seek_positions (localOffset enclosingOffset : ℤ) :
    install seekWiring (RuntimeArraySeek.position localOffset) (position enclosingOffset) = position localOffset := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · change install seekWiring _ _ (seekWiring 3) = _
    rw [install_at]; rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · change install seekWiring _ _ (seekWiring 0) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 1) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 2) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 4) = _
    rw [install_at]; rfl

private theorem seek_install (elementWidth : ℕ) (index counter oldCounter : List Bool) (array oldArray : Turing.Tape Symbol)
    (element scratch oldScratch : List Symbol) (flag oldFlag : Symbol) :
    install seekWiring (RuntimeArraySeek.frame elementWidth counter scratch flag array)
      (frame elementWidth index oldArray element oldCounter oldScratch oldFlag) = frame elementWidth index array element counter scratch flag := by
  funext name
  fin_cases name
  · rw [install_outside _ _ _ _ (by
      rintro ⟨localName, equal⟩
      fin_cases localName <;> simp [seekWiring_apply] at equal)]
    rfl
  · change install seekWiring _ _ (seekWiring 3) = _
    rw [install_at]; rfl
  · rw [install_outside _ _ _ _ (by
      rintro ⟨localName, equal⟩
      fin_cases localName <;> simp [seekWiring_apply] at equal)]
    rfl
  · change install seekWiring _ _ (seekWiring 0) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 1) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 2) = _
    rw [install_at]; rfl
  · change install seekWiring _ _ (seekWiring 4) = _
    rw [install_at]; rfl

private theorem transfer_install (elementWidth : ℕ)
    (index counter beforeBits block afterBits : List Bool)
    (blockLength : block.length = elementWidth)
    (element oldElement scratch : List Symbol) (flag : Symbol) :
    install transferWiring
      (UnaryCopy.frame [0] (List.replicate (word block).length (data true) ++ [0])
        (word beforeBits.reverse ++ [0]) (word block ++ (word afterBits ++ [0]))
        [0] (element ++ [0]))
      (frame elementWidth index
        (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) ())
        oldElement counter scratch flag) =
      frame elementWidth index
        (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) ())
        element counter scratch flag := by
  funext name
  fin_cases name
  all_goals first
    | (change install transferWiring _ _ (transferWiring 0) = _; rw [install_at]
       simp [UnaryCopy.frame, frame, word, blockLength, unary, CallingConvention.tape]
       exact buffer_padding _)
    | (change install transferWiring _ _ (transferWiring 1) = _; rw [install_at]
       simp [UnaryCopy.frame, Binary.tape, frame, word, List.map_append, List.append_assoc])
    | (change install transferWiring _ _ (transferWiring 2) = _; rw [install_at]
       exact buffer_padding _)
    | (rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩
        fin_cases localName <;> simp [transferWiring_apply] at equal)]; rfl)

/-- Lookup reads the block after a prefix of exactly `index * elementWidth`
bits. All original inputs and all surrounding blanks are preserved. -/
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
  let array := beforeBits ++ block ++ afterBits
  let width := widths elementWidth index.length array.length
  have copied := StandardTapeCommands.copy_runs (0 : Fin 7) 3 (by decide) width readOnly rfl
    index oldCounter rfl rfl counterLength (initialFrame elementWidth index array element oldCounter scratch flag)
    rfl (Function.update_self _ _ _)
  have prepared : Function.update (initialFrame elementWidth index array element oldCounter scratch flag) 3
      (buffer (word index)) = frame elementWidth index (buffer (word array)) element index scratch flag := by
    funext name
    fin_cases name <;> simp [initialFrame, frame]
  rw [prepared] at copied
  have sought := (RuntimeArraySeek.runs elementWidth index scratch scratchLength flag
    (buffer (word array)) array.length 0).wire seekWiring width readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp_all [readOnly, RuntimeArraySeek.readOnly])
    (frame elementWidth index (buffer (word array)) element index scratch flag) (position 0)
  rw [seek_positions, seek_positions, seek_install, seek_install] at sought
  have zero : position 0 = fun _ : Fin 7 => (0 : ℤ) := by funext name; simp [position]
  simp only [zero_add, ← Nat.cast_mul, ← prefixLength] at sought
  rw [zero] at sought
  have arraySplit : (Turing.Tape.move .right)^[beforeBits.length] (buffer (word array)) =
      Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) () := by
    rw [← buffer_padding (word array)]
    dsimp only [Binary.tape]
    have moved := Move.right_list (word beforeBits) [0] (word (block ++ afterBits) ++ [0])
    simpa [word, array, List.map_append, List.append_assoc] using moved
  rw [arraySplit] at sought
  let selectedArray := Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) ()
  have transferred := (UnaryCopy.runs (word block) element (by simpa [word, blockLength] using elementLength)
    (word beforeBits.reverse ++ [0]) (word afterBits ++ [0]) [0] [0]
    (fun name => width (transferWiring name))
    (fun name => position beforeBits.length (transferWiring name)) (by
      simp [width, widths, position, transferWiring_apply, word, blockLength])).wire
    transferWiring width readOnly (by intro name; rfl)
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise ⊢)
    (frame elementWidth index selectedArray element (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) (position beforeBits.length)
  rw [install_self, transfer_install _ _ _ _ _ _ blockLength, transfer_install _ _ _ _ _ _ blockLength] at transferred
  have wordLength : (word block).length = elementWidth := by simp [word, blockLength]
  simp only [wordLength] at transferred
  obtain ⟨returnTicks, returnCost, returned⟩ := StandardHead.BlankReturn.runs beforeBits (block ++ afterBits) (by
    intro empty
    have blockEmpty : block = [] := (List.append_eq_nil_iff.mp empty).1
    have zeroWidth : elementWidth = 0 := by simpa only [blockEmpty, List.length_nil] using blockLength.symm
    apply List.eq_nil_of_length_eq_zero
    rw [prefixLength, zeroWidth, Nat.mul_zero])
  have restored := returned.wire (oneTape (1 : Fin 7)) width readOnly
    (by intro name; cases name; simp [width, widths, array, List.length_append])
    (by intro name premise; cases name; rfl)
    (frame elementWidth index selectedArray (word block) (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) (position beforeBits.length)
  have returnStart : install (oneTape (1 : Fin 7)) (fun _ : Unit => (beforeBits.length : ℤ))
      (position beforeBits.length) = position beforeBits.length := install_self (oneTape (1 : Fin 7)) _
  have returnEnd : install (oneTape (1 : Fin 7)) (fun _ : Unit => (0 : ℤ))
      (position beforeBits.length) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [install_one, position]
  have startTapes : install (oneTape (1 : Fin 7))
      (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]))
      (frame elementWidth index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame elementWidth index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := install_self (oneTape (1 : Fin 7)) _
  have endTapes : install (oneTape (1 : Fin 7)) (fun _ : Unit => buffer (word (beforeBits ++ (block ++ afterBits))))
      (frame elementWidth index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame elementWidth index (buffer (word array)) (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name <;> simp [install_one, frame, array, List.append_assoc]
  rw [returnStart, returnEnd, startTapes, endTapes] at restored
  have last := transferred.sequence restore 0 (by intro symbols; simp [MultiTape.wire]) restored
  have middle := sought.sequence (MultiTape.sequence transfer restore 0)
    (.inl 0)
    (by intro symbols; simp [MultiTape.wire, RuntimeArraySeek.machine, RuntimeArraySeek.exit, MultiTape.sequence,
      RuntimeArraySeek.cleanup, StandardArraySeek.Counter.clear, StandardBinaryScan.machine]) last
  have complete := copied.sequence _ (Sum.inl RuntimeArraySeek.entry)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) middle
  refine ⟨2 * index.length + 2 +
    (value index * (6 * index.length + 2 * elementWidth + 16) + 4 * index.length + 6 +
      (3 * elementWidth + 3 + returnTicks + 1) + 1) + 1, ?_, complete⟩
  nlinarith [returnCost]

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


end Polytime2.RuntimeArrayLookup
