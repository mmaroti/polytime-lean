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

import Polytime2.StandardArraySeek
import Polytime2.StandardCopy
import Polytime2.EncodedArray

/-! # Binary-indexed lookup with immutable input arrays

Copy the index into private storage, seek with fixed-width counters, copy one
specialization-width element, and return the array head using its left blank.
The output element and every private tape may start arbitrarily.
-/

namespace Polytime2.StandardArrayLookup

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

def position (offset : ℤ) (name : Fin 6) : ℤ := if name = 1 then offset else 0

def seekWiring : Fin 4 ↪ Fin 6 :=
  ⟨(fun name => match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | _ => 1), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def transferWiring : Bool ↪ Fin 6 :=
  ⟨(fun name => if name then 2 else 1), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 4) :
    seekWiring name = (match name.val with | 0 => 3 | 1 => 4 | 2 => 5 | _ => 1) := rfl
@[simp] theorem transferWiring_apply (name : Bool) : transferWiring name = (if name then 2 else 1) := rfl

noncomputable def prepare : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 0 3 (by decide)
noncomputable def seek (elementWidth : ℕ) : Machine Alphabet (StandardArraySeek.State elementWidth) :=
  MultiTape.wire seekWiring (StandardArraySeek.machine elementWidth)
noncomputable def transfer (elementWidth : ℕ) : Machine Alphabet (Copy.State elementWidth) :=
  MultiTape.wire transferWiring (Copy.machine elementWidth)
noncomputable def restore : Machine Alphabet (Fin 3) :=
  MultiTape.wire (oneTape (1 : Fin 6)) StandardHead.BlankReturn.machine

abbrev State (elementWidth : ℕ) :=
  Sum (Fin 3) (Sum (StandardArraySeek.State elementWidth) (Sum (Copy.State elementWidth) (Fin 3)))

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  MultiTape.sequence prepare
    (MultiTape.sequence (seek elementWidth)
      (MultiTape.sequence (transfer elementWidth) restore 0) (Sum.inl (false, Fin.last elementWidth)))
    (Sum.inl (StandardArraySeek.entry elementWidth))

def entry (elementWidth : ℕ) : State elementWidth := .inl 0
def exit (elementWidth : ℕ) : State elementWidth := .inr (.inr (.inr 2))

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, MultiTape.wire, oneTape,
    StandardHead.BlankReturn.machine]

def initialFrame (index array : List Bool) (element counter scratch : List Symbol) (flag : Symbol) :
    Tapes Alphabet := Function.update
      (frame index (buffer (word array)) element (List.replicate index.length false) scratch flag) 3 (buffer counter)

private theorem seek_positions (localOffset enclosingOffset : ℤ) :
    install seekWiring (StandardArraySeek.position localOffset) (position enclosingOffset) = position localOffset := by
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

private theorem seek_install (index counter oldCounter : List Bool) (array oldArray : Turing.Tape Symbol)
    (element scratch oldScratch : List Symbol) (flag oldFlag : Symbol) :
    install seekWiring (StandardArraySeek.frame counter scratch flag array)
      (frame index oldArray element oldCounter oldScratch oldFlag) = frame index array element counter scratch flag := by
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

private theorem transfer_positions (offset : ℤ) :
    install transferWiring (fun name => if name then (0 : ℤ) else offset) (position offset) = position offset := by
  funext name
  fin_cases name
  all_goals first
    | (change install transferWiring _ _ (transferWiring false) = _; rw [install_at]; rfl)
    | (change install transferWiring _ _ (transferWiring true) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        cases localName <;> simp [transferWiring_apply] at equal)

private theorem transfer_install (index counter beforeBits block afterBits : List Bool)
    (element oldElement scratch : List Symbol) (flag : Symbol) :
    install transferWiring
      (Copy.frame (word beforeBits.reverse ++ [0]) (word block ++ (word afterBits ++ [0])) [0] (element ++ [0]))
      (frame index (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) ())
        oldElement counter scratch flag) =
      frame index (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]) ())
        element counter scratch flag := by
  funext name
  fin_cases name
  all_goals first
    | (change install transferWiring _ _ (transferWiring false) = _; rw [install_at]; simp [Copy.frame, Binary.tape, frame, word, List.map_append, List.append_assoc])
    | (change install transferWiring _ _ (transferWiring true) = _; rw [install_at]; exact buffer_padding _)
    | (rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩
        cases localName <;> simp [transferWiring_apply] at equal)]; rfl)

/-- Lookup reads the block after a prefix of exactly `index * elementWidth`
bits. All original inputs and all surrounding blanks are preserved. -/
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
  let array := beforeBits ++ block ++ afterBits
  let width := widths elementWidth index.length array.length
  have copied := StandardTapeCommands.copy_runs (0 : Fin 6) 3 (by decide) width readOnly rfl
    index oldCounter rfl rfl counterLength (initialFrame index array element oldCounter scratch flag)
    rfl (Function.update_self _ _ _)
  have prepared : Function.update (initialFrame index array element oldCounter scratch flag) 3
      (buffer (word index)) = frame index (buffer (word array)) element index scratch flag := by
    funext name
    fin_cases name <;> simp [initialFrame, frame]
  rw [prepared] at copied
  have sought := (StandardArraySeek.runs elementWidth index scratch scratchLength flag
    (buffer (word array)) array.length 0).wire seekWiring width readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp_all [readOnly, StandardArraySeek.readOnly])
    (frame index (buffer (word array)) element index scratch flag) (position 0)
  rw [seek_positions, seek_positions, seek_install, seek_install] at sought
  have zero : position 0 = fun _ : Fin 6 => (0 : ℤ) := by funext name; simp [position]
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
  have transferred := (StandardCopy.slice_runs elementWidth block element blockLength elementLength
    (word beforeBits.reverse ++ [0]) (word afterBits ++ [0]) [0] [0]
    (fun name => if name then elementWidth else array.length)
    (fun name => if name then (0 : ℤ) else beforeBits.length) (by simp)).wire
    transferWiring width readOnly
    (by intro name; cases name <;> rfl)
    (by intro name premise; cases name <;> simp [readOnly, StandardCopy.readOnly] at premise ⊢)
    (frame index selectedArray element (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) (position beforeBits.length)
  rw [transfer_positions, transfer_install, transfer_install] at transferred
  obtain ⟨returnTicks, returnCost, returned⟩ := StandardHead.BlankReturn.runs beforeBits (block ++ afterBits) (by
    intro empty
    have blockEmpty : block = [] := (List.append_eq_nil_iff.mp empty).1
    have zeroWidth : elementWidth = 0 := by simpa only [blockEmpty, List.length_nil] using blockLength.symm
    apply List.eq_nil_of_length_eq_zero
    rw [prefixLength, zeroWidth, Nat.mul_zero])
  have restored := returned.wire (oneTape (1 : Fin 6)) width readOnly
    (by intro name; cases name; simp [width, widths, array, List.length_append])
    (by intro name premise; cases name; rfl)
    (frame index selectedArray (word block) (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) (position beforeBits.length)
  have returnStart : install (oneTape (1 : Fin 6)) (fun _ : Unit => (beforeBits.length : ℤ))
      (position beforeBits.length) = position beforeBits.length := install_self (oneTape (1 : Fin 6)) _
  have returnEnd : install (oneTape (1 : Fin 6)) (fun _ : Unit => (0 : ℤ))
      (position beforeBits.length) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [install_one, position]
  have startTapes : install (oneTape (1 : Fin 6))
      (Binary.tape (word beforeBits.reverse ++ [0]) (word (block ++ afterBits) ++ [0]))
      (frame index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := install_self (oneTape (1 : Fin 6)) _
  have endTapes : install (oneTape (1 : Fin 6)) (fun _ : Unit => buffer (word (beforeBits ++ (block ++ afterBits))))
      (frame index selectedArray (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame index (buffer (word array)) (word block) (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name <;> simp [install_one, frame, array, List.append_assoc]
  rw [returnStart, returnEnd, startTapes, endTapes] at restored
  have last := transferred.sequence restore 0 (by intro symbols; simp [MultiTape.wire, Copy.machine]) restored
  have middle := sought.sequence (MultiTape.sequence (transfer elementWidth) restore 0)
    (Sum.inl (false, Fin.last elementWidth))
    (by intro symbols; simp [MultiTape.wire, StandardArraySeek.machine, StandardArraySeek.exit, MultiTape.sequence,
      StandardArraySeek.cleanup, StandardArraySeek.Counter.clear, StandardBinaryScan.machine]) last
  have complete := copied.sequence _ (Sum.inl (StandardArraySeek.entry elementWidth))
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) middle
  refine ⟨2 * index.length + 2 +
    (value index * (6 * index.length + elementWidth + 11) + 4 * index.length + 6 +
      (2 * elementWidth + 1 + returnTicks + 1) + 1) + 1, ?_, complete⟩
  nlinarith [returnCost]

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


theorem encoded_runs {Parameter : Type parameterLevel} [Fintype Parameter]
    (elementDomain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (lengthParameter : Parameter) (assignment : Parameter → ℕ)
    (index : List Bool) (within : value index < assignment lengthParameter)
    (array : (EncodedDomain.array elementDomain lengthParameter).Carrier assignment)
    (oldElement oldCounter scratch : List Symbol)
    (elementLength : oldElement.length = elementDomain.width assignment)
    (counterLength : oldCounter.length = index.length)
    (scratchLength : scratch.length = index.length) (flag : Symbol) :
    ∃ ticks,
      ticks ≤ assignment lengthParameter *
        (6 * index.length + 2 * elementDomain.width assignment + 11) +
        6 * index.length + 2 * elementDomain.width assignment + 15 ∧
      Runs (widths (elementDomain.width assignment) index.length
          ((EncodedDomain.array elementDomain lengthParameter).width assignment))
        readOnly (machine (elementDomain.width assignment)) ticks
        (entry (elementDomain.width assignment)) (fun _ => 0)
        (initialFrame index
          (EncodedDomain.ArrayEncoding.bits
            ((EncodedDomain.array elementDomain lengthParameter).encode assignment array))
          oldElement oldCounter scratch flag)
        (exit (elementDomain.width assignment)) (fun _ => 0)
        (frame index
          (CallingConvention.encoded (EncodedDomain.array elementDomain lengthParameter) assignment array)
          (word (EncodedDomain.ArrayEncoding.bits
            (elementDomain.encode assignment (array ⟨value index, within⟩))))
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨beforeBits, afterBits, decomposition, prefixLength⟩ :=
    EncodedDomain.ArrayEncoding.split_encode (elementDomain.encode assignment)
      (assignment lengthParameter) array ⟨value index, within⟩
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
        (EncodedDomain.array elementDomain lengthParameter).width assignment := by
      rw [← decomposition]
      simp [EncodedDomain.array, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits]
    rw [encodedLength] at trace
    have whole : EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.array elementDomain lengthParameter).encode assignment array) =
        beforeBits ++ block ++ afterBits := by
      simpa only [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.array_encode_bits] using decomposition
    simp only [← whole] at trace
    exact trace

end Polytime2.StandardArrayLookup
