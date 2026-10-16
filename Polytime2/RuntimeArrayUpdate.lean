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

/-! # Separate-output binary-indexed array update

The source array, index, and replacement element are immutable arguments. The
array is first copied to its output tape, then one runtime-width block is replaced
there. All scratch regions are returned to canonical zero values.
-/

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

def position (offset : ℤ) (name : Fin 8) : ℤ := if name = 3 then offset else 0

def seekWiring : Fin 5 ↪ Fin 8 :=
  ⟨(fun name => match name.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 3 | _ => 7), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def patchWiring : Fin 3 ↪ Fin 8 :=
  ⟨(fun name => match name.val with | 0 => 7 | 1 => 2 | _ => 3), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 5) :
    seekWiring name = (match name.val with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 3 | _ => 7) := rfl

@[simp] theorem patchWiring_apply (name : Fin 3) :
    patchWiring name = (match name.val with | 0 => 7 | 1 => 2 | _ => 3) := rfl

noncomputable def prepareIndex : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 0 4 (by decide)

noncomputable def copyArray : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 1 3 (by decide)

noncomputable def seek : Machine Alphabet RuntimeArraySeek.State :=
  MultiTape.wire seekWiring RuntimeArraySeek.machine

noncomputable def patch : Machine Alphabet (Fin 4) :=
  MultiTape.wire patchWiring UnaryCopy.machine

noncomputable def restore : Machine Alphabet (Fin 3) :=
  MultiTape.wire (oneTape (3 : Fin 8)) StandardHead.BlankReturn.machine

abbrev State :=
  Sum (Fin 3) (Sum (Fin 3)
    (Sum RuntimeArraySeek.State (Sum (Fin 4) (Fin 3))))

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence prepareIndex
    (MultiTape.sequence copyArray
      (MultiTape.sequence seek
        (MultiTape.sequence patch restore 0)
        (.inl 0))
      (Sum.inl RuntimeArraySeek.entry)) (.inl 0)

def entry : State := .inl 0

def exit : State := .inr (.inr (.inr (.inr 2)))

/-- Initial arbitrary writable contents are represented explicitly. -/
def initialFrame (elementWidth : ℕ) (index array : List Bool) (element : List Symbol) (result : List Symbol)
    (counter scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  Function.update
    (frame elementWidth index (buffer (word array)) element (buffer result) [] scratch flag)
    4 (buffer counter)

private theorem seek_positions (localOffset enclosingOffset : ℤ) :
    install seekWiring (RuntimeArraySeek.position localOffset)
      (position enclosingOffset) = position localOffset := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · change install seekWiring _ _ (seekWiring 3) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 0) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 1) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 2) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 4) = _
    rw [install_at]; rfl

private theorem seek_install (elementWidth : ℕ) (index counter oldCounter : List Bool)
    (array oldArray result : Turing.Tape Symbol) (element scratch oldScratch : List Symbol)
    (flag oldFlag : Symbol) :
    install seekWiring (RuntimeArraySeek.frame elementWidth counter scratch flag array)
      (frame elementWidth index oldArray element result oldCounter oldScratch oldFlag) =
      frame elementWidth index oldArray element array counter scratch flag := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [seekWiring_apply] at equal
  · change install seekWiring _ _ (seekWiring 3) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 0) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 1) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 2) = _
    rw [install_at]
    rfl
  · change install seekWiring _ _ (seekWiring 4) = _
    rw [install_at]; rfl

private theorem array_split (before block after : List Bool) :
    (Turing.Tape.move .right)^[before.length]
      (buffer (word (before ++ block ++ after))) =
      Binary.tape (word before.reverse ++ [0]) (word (block ++ after) ++ [0]) () := by
  rw [← buffer_padding (word (before ++ block ++ after))]
  dsimp only [Binary.tape]
  have moved := Move.right_list (word before) [0] (word (block ++ after) ++ [0])
  simpa [word, List.map_append, List.append_assoc] using moved

private theorem patch_install (elementWidth : ℕ)
    (index before oldBlock newBlock after replacement : List Bool)
    (sourceArray : Turing.Tape Symbol) (counter : List Bool) (scratch : List Symbol) (flag : Symbol) :
    install patchWiring
      (UnaryCopy.frame [0] (List.replicate elementWidth (data true) ++ [0])
        [0] (word replacement ++ [0]) (word before.reverse ++ [0])
        (word newBlock ++ (word after ++ [0])))
      (frame elementWidth index sourceArray (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (oldBlock ++ after) ++ [0]) ())
        counter scratch flag) =
      frame elementWidth index sourceArray (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (newBlock ++ after) ++ [0]) ())
        counter scratch flag := by
  funext name
  fin_cases name
  all_goals first
    | (change install patchWiring _ _ (patchWiring 0) = _; rw [install_at]
       simp [UnaryCopy.frame, frame, unary, CallingConvention.tape, word]
       exact buffer_padding _)
    | (change install patchWiring _ _ (patchWiring 1) = _; rw [install_at]
       exact buffer_padding _)
    | (change install patchWiring _ _ (patchWiring 2) = _; rw [install_at]
       simp [UnaryCopy.frame, Binary.tape, frame, word, List.map_append, List.append_assoc])
    | (rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩
        fin_cases localName <;> simp [patchWiring_apply] at equal)]; rfl)

/-- Copy the input array to a separate result tape, replace one selected block,
and return every head to its region start. The output and scratch may initially
contain arbitrary symbols. -/
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
  let arrayWidth := arrayBits.length
  let width := widths elementWidth index.length arrayWidth
  have prepared := StandardTapeCommands.copy_runs (0 : Fin 8) 4 (by decide)
    width readOnly (by simp [readOnly]) index oldCounter rfl rfl counterLength
    (initialFrame elementWidth index arrayBits (word replacement) oldOutput oldCounter scratch flag)
    rfl (Function.update_self _ _ _)
  have preparedFrame :
      Function.update
        (initialFrame elementWidth index arrayBits (word replacement) oldOutput oldCounter scratch flag)
        4 (buffer (word index)) =
      frame elementWidth index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
        index scratch flag := by
    funext name
    fin_cases name <;> simp [initialFrame, frame]
  rw [preparedFrame] at prepared
  have copied := StandardTapeCommands.copy_runs (1 : Fin 8) 3 (by decide)
    width readOnly (by simp [readOnly]) arrayBits oldOutput rfl rfl outputLength
    (frame elementWidth index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
      index scratch flag) rfl rfl
  have copiedFrame :
      Function.update
        (frame elementWidth index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
          index scratch flag)
        3 (buffer (word arrayBits)) =
      frame elementWidth index (buffer (word arrayBits)) (word replacement) (buffer (word arrayBits))
        index scratch flag := by
    funext name
    fin_cases name <;> simp [frame]
  rw [copiedFrame] at copied
  let seekReadOnly : Fin 8 → Bool := fun name => readOnly name || decide (name = 3)
  have sought := (RuntimeArraySeek.runs elementWidth index scratch scratchLength flag
    (buffer (word arrayBits)) arrayWidth 0).wire seekWiring width seekReadOnly
    (by
      intro name
      fin_cases name <;> simp [seekWiring_apply, width, widths, arrayWidth, arrayBits,
        RuntimeArraySeek.widths])
    (by
      intro name premise
      fin_cases name <;> simp_all [seekWiring_apply, seekReadOnly, readOnly,
        RuntimeArraySeek.readOnly])
    (frame elementWidth index (buffer (word arrayBits)) (word replacement) (buffer (word arrayBits))
      index scratch flag) (position 0)
  rw [seek_positions, seek_positions, seek_install] at sought
  have seekReadOnlyWeakening : ∀ name, readOnly name = true → seekReadOnly name = true := by
    intro name premise
    simp [seekReadOnly, premise]
  have sought := sought.readOnly_mono seekReadOnlyWeakening
  have zeroPosition : position 0 = fun _ : Fin 8 => (0 : ℤ) := by
    funext name
    simp [position]
  have offsetPosition : position (before.length : ℤ) =
      fun name => if name = 3 then (before.length : ℤ) else 0 := by
    funext name
    simp [position]
  have seekOffset : value index * elementWidth = before.length := prefixLength.symm
  simp only [zeroPosition, ← Nat.cast_mul, seekOffset, offsetPosition, zero_add] at sought
  rw [array_split before block after] at sought
  repeat rw [seek_install] at sought
  let selectedArray := Binary.tape (word before.reverse ++ [0])
    (word (block ++ after) ++ [0]) ()
  have blockFits : 0 ≤ (before.length : ℤ) ∧
      (before.length : ℤ) + elementWidth ≤ arrayWidth := by
    simp [arrayWidth, arrayBits]
    omega
  have patched := (UnaryCopy.runs (word replacement) (word block)
    (by simp [word, blockLength, replacementLength]) [0] [0]
    (word before.reverse ++ [0]) (word after ++ [0])
    (fun name => width (patchWiring name))
    (fun name => position before.length (patchWiring name)) (by
      simpa [width, widths, position, patchWiring_apply, word, replacementLength] using blockFits)).wire
    patchWiring width readOnly (by intro name; rfl)
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise ⊢)
    (frame elementWidth index (buffer (word arrayBits)) (word replacement) selectedArray
      (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) (position before.length)
  have wordLength : (word replacement).length = elementWidth := by simp [word, replacementLength]
  simp only [wordLength] at patched
  rw [install_self] at patched
  dsimp only [selectedArray] at patched
  rw [patch_install, patch_install] at patched
  let updatedBits := before ++ replacement ++ after
  have returned := StandardHead.BlankReturn.runs before (replacement ++ after) (by
    intro empty
    have replacementEmpty := (List.append_eq_nil_iff.mp empty).1
    have afterEmpty := (List.append_eq_nil_iff.mp empty).2
    have widthZero : elementWidth = 0 := by
      simpa [replacementEmpty] using replacementLength.symm
    have beforeEmpty : before = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [prefixLength, widthZero]
      simp
    exact beforeEmpty)
  obtain ⟨restoreTicks, restoreBound, returned⟩ := returned
  have restored := returned.wire (oneTape (3 : Fin 8)) width readOnly
    (by
      intro name
      cases name
      simp [oneTape_apply, width, widths, arrayWidth, arrayBits, List.length_append]
      omega)
    (by intro name premise; fin_cases name; simp [readOnly] at premise)
    (frame elementWidth index (buffer (word arrayBits)) (word replacement)
      (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
      (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false))
    (position (before.length : ℤ))
  have restoreStart : install (oneTape (3 : Fin 8))
      (fun _ : Unit => (before.length : ℤ)) (position (before.length : ℤ)) =
      position (before.length : ℤ) := install_self (oneTape (3 : Fin 8)) _
  have restoreEnd : install (oneTape (3 : Fin 8)) (fun _ : Unit => (0 : ℤ))
      (position (before.length : ℤ)) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [install_one, position]
  have restoreStartTapes : install (oneTape (3 : Fin 8))
      (fun _ : Unit => Binary.tape (word before.reverse ++ [0])
        (word (replacement ++ after) ++ [0]) ())
      (frame elementWidth index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame elementWidth index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name <;> simp [install_one, frame]
  rw [restoreStart, restoreEnd, restoreStartTapes] at restored
  have restoreOutput : install (oneTape (3 : Fin 8))
      (fun _ : Unit => buffer (word (before ++ (replacement ++ after))))
      (frame elementWidth index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame elementWidth index (buffer (word arrayBits)) (word replacement)
        (buffer (word (before ++ replacement ++ after)))
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name
    · simp [install_one, frame]
    · simp [install_one, frame]
    · simp [install_one, frame]
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame]
    · simp [install_one, frame]
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName
      have contradiction : (3 : Fin 8) = 6 := by change (3 : Fin 8) = 6 at equal; exact equal
      exact (by decide : (3 : Fin 8) ≠ 6) contradiction
    · simp [install_one, frame]
  rw [restoreOutput] at restored
  have last := patched.sequence (MultiTape.wire (oneTape (3 : Fin 8))
      StandardHead.BlankReturn.machine) 0
    (by intro symbols; simp [MultiTape.wire, UnaryCopy.halt])
    (by simpa [word, Binary.tape, List.map_append, List.append_assoc] using restored)
  rw [offsetPosition] at last
  have beforePatch := sought.sequence (MultiTape.sequence patch restore 0)
    (.inl 0)
    (by intro symbols; simp [MultiTape.wire, RuntimeArraySeek.machine,
      RuntimeArraySeek.exit, MultiTape.sequence, RuntimeArraySeek.cleanup,
      StandardArraySeek.Counter.clear, StandardBinaryScan.machine])
    (by simpa [patch, restore, position, word, Binary.tape, List.map_append,
      List.append_assoc] using last)
  have afterCopy := copied.sequence
    (MultiTape.sequence seek
      (MultiTape.sequence patch restore 0)
      (.inl 0))
    (Sum.inl RuntimeArraySeek.entry)
    (by intro symbols; simp [MultiTape.wire, StandardTapeCommands.copy,
      StandardTerminatedCopy.machine]) beforePatch
  have complete := prepared.sequence
    (MultiTape.sequence copyArray
      (MultiTape.sequence seek
        (MultiTape.sequence patch restore 0)
        (.inl 0))
      (Sum.inl RuntimeArraySeek.entry))
    (.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardTapeCommands.copy,
      StandardTerminatedCopy.machine]) afterCopy
  let totalTicks := 2 * index.length + 2 +
    (2 * arrayBits.length + 2 +
      (value index * (6 * index.length + 2 * elementWidth + 16) +
        4 * index.length + 6 + (3 * elementWidth + 3 + restoreTicks + 1) + 1) + 1) + 1
  refine ⟨totalTicks, ?_, ?_⟩
  · simp only [totalTicks, arrayBits]
    omega
  · simpa [totalTicks, machine, prepareIndex, copyArray, seek, patch, restore,
      entry, exit, initialFrame, frame, width, widths, arrayWidth, arrayBits,
      word, Binary.tape,
      List.map_append, List.append_assoc, List.length_append, Nat.add_assoc] using complete



@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, MultiTape.wire, StandardHead.BlankReturn.machine]

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
