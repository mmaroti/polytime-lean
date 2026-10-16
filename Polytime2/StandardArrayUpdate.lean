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
import Polytime2.StandardTapeCommands
import Polytime2.EncodedArray

/-! # Separate-output binary-indexed array update

The source array, index, and replacement element are immutable arguments. The
array is first copied to its output tape, then one fixed-width block is replaced
there. All scratch regions are returned to canonical zero values.
-/

namespace Polytime2.StandardArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 7)

/-- Index, source array, replacement, result array, counter, decrement scratch,
and a one-bit guard. -/
def frame (index : List Bool) (array : Turing.Tape Symbol) (element : List Symbol)
    (result : Turing.Tape Symbol) (counter : List Bool) (scratch : List Symbol)
    (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word index)
  else if name = 1 then array
  else if name = 2 then buffer element
  else if name = 3 then result
  else if name = 4 then buffer (word counter)
  else if name = 5 then buffer scratch
  else buffer [flag]

def widths (elementWidth digits arrayWidth : ℕ) (name : Fin 7) : ℕ :=
  if name = 1 ∨ name = 3 then arrayWidth
  else if name = 2 then elementWidth
  else if name = 6 then 1 else digits

def readOnly (name : Fin 7) : Bool := decide (name = 0 ∨ name = 1 ∨ name = 2)

def position (offset : ℤ) (name : Fin 7) : ℤ := if name = 3 then offset else 0

def seekWiring : Fin 4 ↪ Fin 7 :=
  ⟨(fun name => match name.val with | 0 => 4 | 1 => 5 | 2 => 6 | _ => 3), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def patchWiring : Bool ↪ Fin 7 :=
  ⟨(fun name => if name then 3 else 2), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Fin 4) :
    seekWiring name = (match name.val with | 0 => 4 | 1 => 5 | 2 => 6 | _ => 3) := rfl

@[simp] theorem patchWiring_apply (name : Bool) :
    patchWiring name = (if name then 3 else 2) := rfl

noncomputable def prepareIndex : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 0 4 (by decide)

noncomputable def copyArray : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 1 3 (by decide)

noncomputable def seek (elementWidth : ℕ) :
    Machine Alphabet (StandardArraySeek.State elementWidth) :=
  MultiTape.wire seekWiring (StandardArraySeek.machine elementWidth)

noncomputable def patch (elementWidth : ℕ) : Machine Alphabet (Copy.State elementWidth) :=
  MultiTape.wire patchWiring (Copy.machine elementWidth)

noncomputable def restore : Machine Alphabet (Fin 3) :=
  MultiTape.wire (oneTape (3 : Fin 7)) StandardHead.BlankReturn.machine

abbrev State (elementWidth : ℕ) :=
  Sum (Fin 3) (Sum (Fin 3)
    (Sum (StandardArraySeek.State elementWidth) (Sum (Copy.State elementWidth) (Fin 3))))

noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  MultiTape.sequence prepareIndex
    (MultiTape.sequence copyArray
      (MultiTape.sequence (seek elementWidth)
        (MultiTape.sequence (patch elementWidth) restore 0)
        (Sum.inl (false, Fin.last elementWidth)))
      (Sum.inl (StandardArraySeek.entry elementWidth))) (.inl 0)

def entry (elementWidth : ℕ) : State elementWidth := .inl 0

def exit (elementWidth : ℕ) : State elementWidth := .inr (.inr (.inr (.inr 2)))

-- parameterLevel: unary size-parameter names; carrierLevel: array elements.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The same update layout over any finite collection of unary size inputs. -/
def domainsSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 7) → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 1 | .inr 3 => element.arrayOfLength length
  | .inr 2 => element
  | .inr 4 | .inr 5 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 6 => EncodedDomain.booleans

def argumentReadOnlySized : Sum Parameter (Fin 7) → Bool
  | .inl _ => true
  | .inr name => decide (name.val < 3)

def sizeTapesSized : Parameter ↪ Sum Parameter (Fin 7) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def dataTapesSized : Fin 7 ↪ Sum Parameter (Fin 7) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithmSized (elementWidth : ℕ) :
    Machine (CallingConvention.Alphabet (Sum Parameter (Fin 7)))
      (State elementWidth) :=
  MultiTape.wire dataTapesSized (machine elementWidth)

/-- Mathematical types on the two unary size tapes, arguments, result, and
private scratch tapes. -/
noncomputable def domains (element : EncodedDomain.{0, 0} Bool) :
    Sum Bool (Fin 7) → EncodedDomain Bool :=
  domainsSized element false (MvPolynomial.X true)

def argumentReadOnly : Sum Bool (Fin 7) → Bool := argumentReadOnlySized

def sizeTapes : Bool ↪ Sum Bool (Fin 7) := sizeTapesSized

def dataTapes : Fin 7 ↪ Sum Bool (Fin 7) := dataTapesSized

noncomputable def algorithm (elementWidth : ℕ) :
    Machine (CallingConvention.Alphabet (Sum Bool (Fin 7))) (State elementWidth) :=
  algorithmSized elementWidth

/-- Initial arbitrary writable contents are represented explicitly. -/
def initialFrame (index array : List Bool) (element : List Symbol) (result : List Symbol)
    (counter scratch : List Symbol) (flag : Symbol) : Tapes Alphabet :=
  Function.update
    (frame index (buffer (word array)) element (buffer result) [] scratch flag)
    4 (buffer counter)

private theorem seek_positions (localOffset enclosingOffset : ℤ) :
    install seekWiring (StandardArraySeek.position localOffset)
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

private theorem seek_install (index counter oldCounter : List Bool)
    (array oldArray result : Turing.Tape Symbol) (element scratch oldScratch : List Symbol)
    (flag oldFlag : Symbol) :
    install seekWiring (StandardArraySeek.frame counter scratch flag array)
      (frame index oldArray element result oldCounter oldScratch oldFlag) =
      frame index oldArray element array counter scratch flag := by
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

private theorem patch_positions (offset : ℤ) :
    install patchWiring (fun name => if name then offset else 0) (position offset) =
      position offset := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · change install patchWiring _ _ (patchWiring false) = _
    rw [install_at]
    rfl
  · change install patchWiring _ _ (patchWiring true) = _
    rw [install_at]
    rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal

private theorem array_split (before block after : List Bool) :
    (Turing.Tape.move .right)^[before.length]
      (buffer (word (before ++ block ++ after))) =
      Binary.tape (word before.reverse ++ [0]) (word (block ++ after) ++ [0]) () := by
  rw [← buffer_padding (word (before ++ block ++ after))]
  dsimp only [Binary.tape]
  have moved := Move.right_list (word before) [0] (word (block ++ after) ++ [0])
  simpa [word, List.map_append, List.append_assoc] using moved

private theorem patch_array_split (before replacement after : List Bool) :
    (Turing.Tape.move .right)^[before.length]
      (buffer (word (before ++ replacement ++ after))) =
      Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) () :=
  array_split before replacement after

private theorem patch_start_install (index before block after replacement : List Bool)
    (sourceArray : Turing.Tape Symbol) (counter : List Bool) (scratch : List Symbol)
    (flag : Symbol) :
    install patchWiring
      (Copy.frame [0] (word replacement ++ [0]) (word before.reverse ++ [0])
        (word (block ++ after) ++ [0]))
      (frame index sourceArray (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (block ++ after) ++ [0]) ())
        counter scratch flag) =
      frame index sourceArray (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (block ++ after) ++ [0]) ())
        counter scratch flag := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · change install patchWiring _ _ (patchWiring false) = _
    rw [install_at]
    simp only [Copy.frame, Binary.tape, frame, word, List.map_append,
      List.append_assoc]
    exact buffer_padding (word replacement)
  · change install patchWiring _ _ (patchWiring true) = _
    rw [install_at]
    rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [patchWiring_apply] at equal

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
        value index * (6 * index.length + elementWidth + 11) + 4 * index.length + 6 +
        2 * elementWidth + 1 + before.length + 3 + 4 ∧
      Runs (widths elementWidth index.length (before ++ block ++ after).length) readOnly
        (machine elementWidth) ticks (entry elementWidth) (fun _ => 0)
        (initialFrame index (before ++ block ++ after) (word replacement) oldOutput
          oldCounter scratch flag)
        (exit elementWidth) (fun _ => 0)
        (frame index (buffer (word (before ++ block ++ after))) (word replacement)
          (buffer (word (before ++ replacement ++ after)))
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) := by
  let arrayBits := before ++ block ++ after
  let arrayWidth := arrayBits.length
  let width := widths elementWidth index.length arrayWidth
  have prepared := StandardTapeCommands.copy_runs (0 : Fin 7) 4 (by decide)
    width readOnly (by simp [readOnly]) index oldCounter rfl rfl counterLength
    (initialFrame index arrayBits (word replacement) oldOutput oldCounter scratch flag)
    rfl (Function.update_self _ _ _)
  have preparedFrame :
      Function.update
        (initialFrame index arrayBits (word replacement) oldOutput oldCounter scratch flag)
        4 (buffer (word index)) =
      frame index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
        index scratch flag := by
    funext name
    fin_cases name <;> simp [initialFrame, frame]
  rw [preparedFrame] at prepared
  have copied := StandardTapeCommands.copy_runs (1 : Fin 7) 3 (by decide)
    width readOnly (by simp [readOnly]) arrayBits oldOutput rfl rfl outputLength
    (frame index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
      index scratch flag) rfl rfl
  have copiedFrame :
      Function.update
        (frame index (buffer (word arrayBits)) (word replacement) (buffer oldOutput)
          index scratch flag)
        3 (buffer (word arrayBits)) =
      frame index (buffer (word arrayBits)) (word replacement) (buffer (word arrayBits))
        index scratch flag := by
    funext name
    fin_cases name <;> simp [frame]
  rw [copiedFrame] at copied
  let seekReadOnly : Fin 7 → Bool := fun name => readOnly name || decide (name = 3)
  have sought := (StandardArraySeek.runs elementWidth index scratch scratchLength flag
    (buffer (word arrayBits)) arrayWidth 0).wire seekWiring width seekReadOnly
    (by
      intro name
      fin_cases name <;> simp [seekWiring_apply, width, widths, arrayWidth, arrayBits,
        StandardArraySeek.widths])
    (by
      intro name premise
      fin_cases name <;> simp_all [seekWiring_apply, seekReadOnly, readOnly,
        StandardArraySeek.readOnly])
    (frame index (buffer (word arrayBits)) (word replacement) (buffer (word arrayBits))
      index scratch flag) (position 0)
  rw [seek_positions, seek_positions, seek_install] at sought
  have seekReadOnlyWeakening : ∀ name, readOnly name = true → seekReadOnly name = true := by
    intro name premise
    simp [seekReadOnly, premise]
  have sought := sought.readOnly_mono seekReadOnlyWeakening
  have zeroPosition : position 0 = fun _ : Fin 7 => (0 : ℤ) := by
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
  have patched := (StandardCopy.slice_runs elementWidth replacement
    (word block) replacementLength (by simpa [word] using blockLength)
    [0] [0] (word before.reverse ++ [0]) (word after ++ [0])
    (fun name => if name then arrayWidth else elementWidth)
    (fun name => if name then (before.length : ℤ) else 0) blockFits).wire
    patchWiring width readOnly
    (by
      intro name
      cases name <;> simp [width, widths, arrayWidth, arrayBits, patchWiring_apply,
        List.length_map, word, List.length_append])
    (by
      intro name premise
      cases name <;> simp [readOnly, patchWiring_apply, StandardCopy.readOnly] at premise ⊢)
    (frame index (buffer (word arrayBits)) (word replacement) selectedArray
      (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false))
    (position (before.length : ℤ))
  simp only [word, List.map_append, List.append_assoc, selectedArray] at patched
  rw [patch_positions] at patched
  have patchStart := patch_start_install index before block after replacement
    (buffer (word arrayBits)) (List.replicate index.length false)
    (word (List.replicate index.length false)) (data false)
  have patchStartNormalized :
      install patchWiring
        (Copy.frame [0] (List.map data replacement ++ [0])
          (List.map data before.reverse ++ [0])
          (List.map data block ++ (List.map data after ++ [0])))
        (frame index (buffer (List.map data arrayBits)) (List.map data replacement)
          (Binary.tape (List.map data before.reverse ++ [0])
            (List.map data block ++ (List.map data after ++ [0])) ())
          (List.replicate index.length false)
          (List.map data (List.replicate index.length false)) (data false)) =
      frame index (buffer (List.map data arrayBits)) (List.map data replacement)
        (Binary.tape (List.map data before.reverse ++ [0])
          (List.map data block ++ (List.map data after ++ [0])) ())
        (List.replicate index.length false)
        (List.map data (List.replicate index.length false)) (data false) := by
    simpa [word, Binary.tape, List.map_append, List.append_assoc] using patchStart
  rw [patchStartNormalized] at patched
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
  have restored := returned.wire (oneTape (3 : Fin 7)) width readOnly
    (by
      intro name
      cases name
      simp [oneTape_apply, width, widths, arrayWidth, arrayBits, List.length_append]
      omega)
    (by intro name premise; fin_cases name <;> simp [readOnly] at premise)
    (frame index (buffer (word arrayBits)) (word replacement)
      (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
      (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false))
    (position (before.length : ℤ))
  have restoreStart : install (oneTape (3 : Fin 7))
      (fun _ : Unit => (before.length : ℤ)) (position (before.length : ℤ)) =
      position (before.length : ℤ) := install_self (oneTape (3 : Fin 7)) _
  have restoreEnd : install (oneTape (3 : Fin 7)) (fun _ : Unit => (0 : ℤ))
      (position (before.length : ℤ)) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [install_one, position]
  have restoreStartTapes : install (oneTape (3 : Fin 7))
      (fun _ : Unit => Binary.tape (word before.reverse ++ [0])
        (word (replacement ++ after) ++ [0]) ())
      (frame index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name <;> simp [install_one, frame]
  have restoreEndTapes : install (oneTape (3 : Fin 7))
      (fun _ : Unit => buffer (word updatedBits))
      (frame index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame index (buffer (word arrayBits)) (word replacement) (buffer (word updatedBits))
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name
    · simp [install_one, frame]
    · simp [install_one, frame]
    · simp [install_one, frame]
    · change install (oneTape (3 : Fin 7))
        (fun _ : Unit => buffer (word updatedBits))
        (frame index (buffer (word arrayBits)) (word replacement)
          (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) (3 : Fin 7) = _
      exact install_at (oneTape (3 : Fin 7)) _ _ ()
    · simp [install_one, frame]
    · simp [install_one, frame]
    · simp [install_one, frame]
  rw [restoreStart, restoreEnd, restoreStartTapes] at restored
  have restoreOutput : install (oneTape (3 : Fin 7))
      (fun _ : Unit => buffer (word (before ++ (replacement ++ after))))
      (frame index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0]) (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false)) =
      frame index (buffer (word arrayBits)) (word replacement)
        (buffer (word (before ++ replacement ++ after)))
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame, List.append_assoc]
    · simp [install_one, frame, List.append_assoc]
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName
      have contradiction : (3 : Fin 7) = 6 := by change (3 : Fin 7) = 6 at equal; exact equal
      exact (by decide : (3 : Fin 7) ≠ 6) contradiction
  rw [restoreOutput] at restored
  have patchEndInstall :
      install patchWiring
        (Copy.frame [0] (word replacement ++ [0]) (word before.reverse ++ [0])
          (word replacement ++ (word after ++ [0])))
        (frame index (buffer (word arrayBits)) (word replacement)
          (Binary.tape (word before.reverse ++ [0])
            (word (block ++ after) ++ [0]) ())
          (List.replicate index.length false)
          (word (List.replicate index.length false)) (data false)) =
      frame index (buffer (word arrayBits)) (word replacement)
        (Binary.tape (word before.reverse ++ [0])
          (word (replacement ++ after) ++ [0]) ())
        (List.replicate index.length false)
        (word (List.replicate index.length false)) (data false) := by
    funext name
    fin_cases name
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName <;> simp [patchWiring_apply] at equal
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName <;> simp [patchWiring_apply] at equal
    · change install patchWiring _ _ (patchWiring false) = _
      rw [install_at]
      simp [Copy.frame, Binary.tape, Turing.Tape.mk₁, Turing.Tape.mk₂,
        frame, word, List.map_append, List.append_assoc]
      exact buffer_padding (word replacement)
    · change install patchWiring _ _ (patchWiring true) = _
      rw [install_at]
      simp [Copy.frame, Binary.tape, frame, word, List.map_append, List.append_assoc]
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName <;> simp [patchWiring_apply] at equal
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName <;> simp [patchWiring_apply] at equal
    · apply install_outside
      rintro ⟨localName, equal⟩
      cases localName <;> simp [patchWiring_apply] at equal
  have patchEndInstallNormalized :
      install patchWiring
        (Copy.frame [0] (List.map data replacement ++ [0])
          (List.map data before.reverse ++ [0])
          (List.map data replacement ++ (List.map data after ++ [0])))
        (frame index (buffer (List.map data arrayBits)) (List.map data replacement)
          (Binary.tape (List.map data before.reverse ++ [0])
            (List.map data block ++ (List.map data after ++ [0])) ())
          (List.replicate index.length false)
          (List.map data (List.replicate index.length false)) (data false)) =
      frame index (buffer (List.map data arrayBits)) (List.map data replacement)
        (Binary.tape (List.map data before.reverse ++ [0])
          (List.map data replacement ++ (List.map data after ++ [0])) ())
        (List.replicate index.length false)
        (List.map data (List.replicate index.length false)) (data false) := by
    simpa [word, Binary.tape, List.map_append, List.append_assoc] using patchEndInstall
  rw [patchEndInstallNormalized] at patched
  have last := patched.sequence (MultiTape.wire (oneTape (3 : Fin 7))
      StandardHead.BlankReturn.machine) 0
    (by intro symbols; simp [MultiTape.wire, Copy.machine])
    (by simpa [word, Binary.tape, List.map_append, List.append_assoc] using restored)
  rw [offsetPosition] at last
  have beforePatch := sought.sequence (MultiTape.sequence (patch elementWidth) restore 0)
    (Sum.inl (false, Fin.last elementWidth))
    (by intro symbols; simp [MultiTape.wire, StandardArraySeek.machine,
      StandardArraySeek.exit, MultiTape.sequence, StandardArraySeek.cleanup,
      StandardArraySeek.Counter.clear, StandardBinaryScan.machine])
    (by simpa [patch, restore, position, word, Binary.tape, List.map_append,
      List.append_assoc] using last)
  have afterCopy := copied.sequence
    (MultiTape.sequence (seek elementWidth)
      (MultiTape.sequence (patch elementWidth) restore 0)
      (Sum.inl (false, Fin.last elementWidth)))
    (Sum.inl (StandardArraySeek.entry elementWidth))
    (by intro symbols; simp [MultiTape.wire, StandardTapeCommands.copy,
      StandardTerminatedCopy.machine]) beforePatch
  have complete := prepared.sequence
    (MultiTape.sequence copyArray
      (MultiTape.sequence (seek elementWidth)
        (MultiTape.sequence (patch elementWidth) restore 0)
        (Sum.inl (false, Fin.last elementWidth)))
      (Sum.inl (StandardArraySeek.entry elementWidth)))
    (.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardTapeCommands.copy,
      StandardTerminatedCopy.machine]) afterCopy
  let totalTicks := 2 * index.length + 2 +
    (2 * arrayBits.length + 2 +
      (value index * (6 * index.length + elementWidth + 11) +
        4 * index.length + 6 + (2 * elementWidth + 1 + restoreTicks + 1) + 1) + 1) + 1
  refine ⟨totalTicks, ?_, ?_⟩
  · simp only [totalTicks, arrayWidth, arrayBits]
    omega
  · simpa [totalTicks, machine, prepareIndex, copyArray, seek, patch, restore,
      entry, exit, initialFrame, frame, width, widths, arrayWidth, arrayBits,
      word, Binary.tape,
      List.map_append, List.append_assoc, List.length_append, Nat.add_assoc] using complete

def outputTapesSized : Unit ↪ Sum Parameter (Fin 7) := oneTape (.inr 3)

/-- An in-range update returns the mathematical array with that coordinate
replaced. Private counters and flags have no validity obligation on return. -/
theorem contractSized (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (elementWidth : ℕ) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domainsSized element indexCapacity length)
      argumentReadOnlySized sizeTapesSized outputTapesSized (algorithmSized elementWidth)
      (entry elementWidth) (exit elementWidth)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment length)
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
          output () =
            Function.update (input ⟨.inr 1, rfl⟩)
              ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithmSized,
    machine, exit, MultiTape.sequence, restore, MultiTape.wire,
    StandardHead.BlankReturn.machine]),
    length *
        (6 * MvPolynomial.X indexCapacity + MvPolynomial.C (4 * elementWidth + 11)) +
      6 * MvPolynomial.X indexCapacity + MvPolynomial.C (2 * elementWidth + 18), ?_⟩
  intro assignment input initial valid represented sizes
  let indexValue : Fin (2 ^ assignment indexCapacity) := input ⟨.inr 0, rfl⟩
  let index := EncodedDomain.ArrayEncoding.bits (BitVec.ofFin indexValue)
  let arrayLength := MvPolynomial.eval assignment length
  let arrayValue : (element.arrayOfLength length).Carrier assignment := input ⟨.inr 1, rfl⟩
  let replacement : element.Carrier assignment := input ⟨.inr 2, rfl⟩
  have indexLength : index.length = assignment indexCapacity := List.length_ofFn
  have indexValueEq : value index = indexValue.val := Binary.value_bits (BitVec.ofFin indexValue)
  have within : value index < arrayLength := by
    rw [indexValueEq]
    exact valid
  have withinInput : indexValue.val < arrayLength := valid
  let indexInArray : Fin arrayLength := ⟨value index, within⟩
  obtain ⟨before, after, decomposition, prefixLength, updatedDecomposition⟩ :=
    EncodedDomain.ArrayEncoding.split_encode_update (element.encode assignment)
      arrayLength arrayValue indexInArray replacement
  let block := EncodedDomain.ArrayEncoding.bits (element.encode assignment (arrayValue indexInArray))
  let replacementBits := EncodedDomain.ArrayEncoding.bits (element.encode assignment replacement)
  let arrayBits := EncodedDomain.ArrayEncoding.bits
    ((element.arrayOfLength length).encode assignment arrayValue)
  have arrayBitsEq : arrayBits = before ++ block ++ after := decomposition
  have arrayBitsLength : arrayBits.length = arrayLength * element.width assignment := by
    change (List.ofFn (fun index : Fin (arrayLength * element.width assignment) =>
      ((EncodedDomain.ArrayEncoding.encode (element.encode assignment)
        arrayLength arrayValue).getLsbD index.val))).length = _
    simp
  have blockLength : block.length = element.width assignment := List.length_ofFn
  have replacementLength : replacementBits.length = element.width assignment :=
    List.length_ofFn
  have prefixLengthUpdate : before.length = value index * element.width assignment :=
    prefixLength
  obtain ⟨oldOutput, outputLength, outputEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldCounter, counterLength, counterEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨scratch, scratchLength, scratchEq⟩ := represented.2 (.inr 5) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 6) rfl
  have flagWidth : flags.length = 1 := by
    have booleanWidth : (EncodedDomain.booleans (Parameter := Parameter)).width assignment = 1 := by
      norm_num [EncodedDomain.booleans, EncodedDomain.fixed, finTwoEquiv]
    change flags.length = (EncodedDomain.booleans (Parameter := Parameter)).width assignment
      at flagLength
    rw [booleanWidth] at flagLength
    exact flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagWidth
  have outputWidth : oldOutput.length = arrayBits.length := by
    have width : oldOutput.length = arrayLength * element.width assignment := by
      simpa [domainsSized, EncodedDomain.arrayOfLength] using outputLength
    rw [arrayBitsLength]
    exact width
  have counterWidth : oldCounter.length = assignment indexCapacity := by
    change oldCounter.length = (domainsSized element indexCapacity length (.inr 4)).width assignment at counterLength
    simpa [domainsSized, EncodedDomain.binaryNaturals] using counterLength
  have scratchWidth : scratch.length = assignment indexCapacity := by
    change scratch.length = (domainsSized element indexCapacity length (.inr 5)).width assignment at scratchLength
    simpa [domainsSized, EncodedDomain.binaryNaturals] using scratchLength
  have indexEq : initial (.inr 0) = buffer (word index) := by
    rw [represented.1 (.inr 0) rfl]
    change encoded (EncodedDomain.binaryNaturals indexCapacity) assignment indexValue =
      buffer (word index)
    rw [← encoded_binaryNaturals indexCapacity assignment index indexLength]
    congr 1
    exact Fin.ext indexValueEq.symm
  have arrayEq : initial (.inr 1) = buffer (word arrayBits) := by
    rw [represented.1 (.inr 1) rfl]
    rfl
  have replacementEq : initial (.inr 2) = buffer (word replacementBits) := by
    rw [represented.1 (.inr 2) rfl]
    rfl
  let elementWidth' := element.width assignment
  obtain ⟨ticks, cost, localTrace⟩ := runs elementWidth' index before block after
    replacementBits prefixLengthUpdate blockLength replacementLength oldOutput oldCounter scratch
    (by rw [outputWidth, arrayBitsEq])
    (counterWidth.trans indexLength.symm) (scratchWidth.trans indexLength.symm) flag
  have chosenWidth := fixedWidth assignment
  subst elementWidth
  let resultValue := Function.update arrayValue indexInArray replacement
  have inputEq : install dataTapesSized (initialFrame index (before ++ block ++ after)
      (word replacementBits)
      oldOutput oldCounter scratch flag) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨dataName, equal⟩
      cases equal
    | inr dataName =>
      rw [show Sum.inr dataName = dataTapesSized dataName from rfl, install_at]
      fin_cases dataName
      · exact indexEq.symm
      · have splice : buffer (word (before ++ block ++ after)) =
            buffer (word arrayBits) := by rw [← arrayBitsEq]
        change buffer (word (before ++ block ++ after)) = initial (.inr 1)
        exact splice.trans arrayEq.symm
      · exact replacementEq.symm
      · exact outputEq.symm
      · exact counterEq.symm
      · exact scratchEq.symm
      · exact flagEq.symm
  have initialPositions : install dataTapesSized (fun _ : Fin 7 => (0 : ℤ))
      (fun _ : Sum Parameter (Fin 7) => (0 : ℤ)) = fun _ => 0 :=
    install_self dataTapesSized _
  let dataWidth : Sum Parameter (Fin 7) → ℕ :=
    fun name => (domainsSized element indexCapacity length name).width assignment
  have concatLength : arrayBits.length = (before ++ block ++ after).length := by
    rw [arrayBitsEq]
  have localWidth : ∀ name : Fin 7, dataWidth (dataTapesSized name) =
      widths elementWidth' index.length arrayBits.length name := by
    intro name
    have boolWidth : Nat.clog 2 2 = 1 := by norm_num
    change (domainsSized element indexCapacity length (.inr name)).width assignment =
      widths elementWidth' index.length arrayBits.length name
    fin_cases name <;> simp [domainsSized, widths,
      EncodedDomain.arrayOfLength, EncodedDomain.binaryNaturals,
      EncodedDomain.booleans, EncodedDomain.fixed, indexLength,
      arrayBitsLength, arrayLength, elementWidth', boolWidth]
  have trace := localTrace.wire dataTapesSized dataWidth argumentReadOnlySized
    (by
      intro name
      rw [← concatLength]
      exact localWidth name)
    (by
      intro name premise
      change argumentReadOnlySized (.inr name) = true at premise
      have indexInArguments : name.val < 3 := of_decide_eq_true
        (by simpa [argumentReadOnlySized] using premise)
      have valueCases : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
      rcases valueCases with zero | one | two
      · have nameEq : name = 0 := Fin.ext zero
        simp [readOnly, nameEq]
      · have nameEq : name = 1 := Fin.ext one
        simp [readOnly, nameEq]
      · have nameEq : name = 2 := Fin.ext two
        simp [readOnly, nameEq])
    initial (fun _ => 0)
  rw [inputEq, initialPositions] at trace
  let output : Outputs (domainsSized element indexCapacity length) outputTapesSized assignment :=
    fun _ => resultValue
  let final := install dataTapesSized
    (frame index (buffer (word (before ++ block ++ after))) (word replacementBits)
      (buffer (word (before ++ replacementBits ++ after)))
      (List.replicate index.length false)
      (word (List.replicate index.length false)) (data false)) initial
  refine ⟨ticks, output, final, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have indexBound : value index ≤ arrayLength := by omega
    have arrayBound : arrayBits.length = arrayLength * elementWidth' := by
      simpa [elementWidth'] using arrayBitsLength
    have beforeBound : before.length = value index * elementWidth' := by
      simpa [elementWidth'] using prefixLengthUpdate
    have concatBound : (before ++ block ++ after).length =
        arrayLength * elementWidth' := by
      rw [← arrayBitsEq]
      simpa [elementWidth'] using arrayBitsLength
    have costNormalized : ticks ≤
        6 * assignment indexCapacity + 2 * elementWidth' + 18 +
          2 * (arrayLength * elementWidth') +
          value index * (6 * assignment indexCapacity + 2 * elementWidth' + 11) := by
      have costRewrite := cost
      rw [indexLength, concatBound, beforeBound] at costRewrite
      nlinarith
    have factorNonnegative :
        0 ≤ 6 * assignment indexCapacity + 2 * elementWidth' + 11 := by omega
    have indexedBound := Nat.mul_le_mul_right
      (6 * assignment indexCapacity + 2 * elementWidth' + 11) indexBound
    have boundIdentity :
        6 * assignment indexCapacity + 2 * elementWidth' + 18 +
          2 * (arrayLength * elementWidth') +
          arrayLength * (6 * assignment indexCapacity + 2 * elementWidth' + 11) =
        arrayLength * (6 * assignment indexCapacity + 4 * elementWidth' + 11) +
          6 * assignment indexCapacity + 2 * elementWidth' + 18 := by ring
    calc
      ticks ≤ 6 * assignment indexCapacity + 2 * elementWidth' + 18 +
          2 * (arrayLength * elementWidth') +
          value index * (6 * assignment indexCapacity + 2 * elementWidth' + 11) :=
        costNormalized
      _ ≤ 6 * assignment indexCapacity + 2 * elementWidth' + 18 +
          2 * (arrayLength * elementWidth') +
          arrayLength * (6 * assignment indexCapacity + 2 * elementWidth' + 11) := by
        omega
      _ = arrayLength * (6 * assignment indexCapacity +
          (4 * element.width assignment + 11)) + 6 * assignment indexCapacity +
          (2 * element.width assignment + 18) := by
        rw [boundIdentity]
        simp [elementWidth']
        ring
  · refine ⟨withinInput, ?_⟩
    have equalIndex : indexInArray =
        (⟨indexValue.val, withinInput⟩ : Fin arrayLength) :=
      Fin.ext indexValueEq
    exact congrArg (fun selected => Function.update arrayValue selected replacement) equalIndex
  · intro name
    cases name
    change install dataTapesSized _ initial (dataTapesSized 3) = _
    rw [install_at]
    change buffer (word (before ++ replacementBits ++ after)) =
      encoded (domainsSized element indexCapacity length (Sum.inr 3)) assignment (output ())
    simp only [output, domainsSized, EncodedDomain.arrayOfLength]
    change buffer (word (before ++ replacementBits ++ after)) =
      buffer (word (EncodedDomain.ArrayEncoding.bits
        (EncodedDomain.ArrayEncoding.encode (element.encode assignment) arrayLength resultValue)))
    congr 1
    exact (congrArg (List.map data) updatedDecomposition).symm

/- The two-size-parameter specialization keeps the original update API. -/
theorem contract (element : EncodedDomain.{0, 0} Bool) (elementWidth : ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domains element) argumentReadOnly sizeTapes (oneTape (.inr 3))
      (algorithm elementWidth) (entry elementWidth) (exit elementWidth)
      (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
        MvPolynomial.eval assignment (MvPolynomial.X true))
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val <
            MvPolynomial.eval assignment (MvPolynomial.X true),
          output () =
            Function.update (input ⟨.inr 1, rfl⟩)
              ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) := by
  exact contractSized element elementWidth false (MvPolynomial.X true) fixedWidth

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, MultiTape.wire,
    StandardHead.BlankReturn.machine]

end Polytime2.StandardArrayUpdate
