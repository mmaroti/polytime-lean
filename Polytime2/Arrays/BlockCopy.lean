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

import Polytime2.Arrays.Counter
import Polytime2.Arithmetic.BinaryGuard
import Polytime2.Primitives.TapeCommands
import Polytime2.Primitives.Head

/-! # Shared indexed copying between an array block and a scalar

Lookup copies a selected array block to a scalar. Replacement copies a scalar
to the selected block. The index preparation and array-head restoration are
identical; certified seek and transfer commands supply the width-dependent work.
-/

namespace Polytime2.ArrayBlockCopy

open MultiTape CallingConvention
open Binary (Symbol data word value)

variable {tapeCount : ℕ} [Fact (6 ≤ tapeCount)] {SeekState TransferState : Type}

private instance tapeCount_neZero : NeZero tapeCount := by
  have minimum : 6 ≤ tapeCount := Fact.out
  exact ⟨by omega⟩

abbrev Alphabet (tapeCount : ℕ) := CallingConvention.Alphabet (Fin tapeCount)

@[simp] private theorem small_mod (number : ℕ) (small : number < 6) :
    number % tapeCount = number := Nat.mod_eq_of_lt (by have minimum : 6 ≤ tapeCount := Fact.out; omega)

/-- Index, array cursor, scalar, counter, scratch, guard, and immutable context. -/
def frame (context : Tapes (Alphabet tapeCount)) (index : List Bool)
    (array : Turing.Tape Symbol) (scalar : List Symbol) (counter : List Bool)
    (scratch : List Symbol) (flag : Symbol) : Tapes (Alphabet tapeCount) := fun name =>
  if name = 0 then buffer (word index)
  else if name = 1 then array
  else if name = 2 then buffer scalar
  else if name = 3 then buffer (word counter)
  else if name = 4 then buffer scratch
  else if name = 5 then buffer [flag] else context name

def widths (extraWidths : Fin tapeCount → ℕ) (elementWidth digits arrayWidth : ℕ)
    (name : Fin tapeCount) : ℕ :=
  if name = 1 then arrayWidth else if name = 2 then elementWidth
  else if name = 5 then 1 else if name = 0 ∨ name = 3 ∨ name = 4 then digits else extraWidths name

def readOnly (sourceIsArray : Bool) (name : Fin tapeCount) : Bool :=
  if name = 1 then sourceIsArray else if name = 2 then !sourceIsArray
  else decide (name = 0 ∨ 6 ≤ name.val)

def position (offset : ℤ) (name : Fin tapeCount) : ℤ := if name = 1 then offset else 0

noncomputable def prepare : Machine (Alphabet tapeCount) (Fin 3) :=
  StandardTapeCommands.copy 0 3 (by simp [Fin.ext_iff, -Fin.val_eq_zero_iff])

noncomputable def restore : Machine (Alphabet tapeCount) (Fin 3) :=
  MultiTape.wire (oneTape (1 : Fin tapeCount)) StandardHead.BlankReturn.machine

abbrev State (SeekState TransferState : Type) :=
  Sum (Fin 3) (Sum SeekState (Sum TransferState (Fin 3)))

noncomputable def machine (seek : Machine (Alphabet tapeCount) SeekState) (seekEntry : SeekState)
    (transfer : Machine (Alphabet tapeCount) TransferState) (transferEntry : TransferState) :
    Machine (Alphabet tapeCount) (State SeekState TransferState) :=
  MultiTape.sequence prepare
    (MultiTape.sequence seek (MultiTape.sequence transfer restore 0) (.inl transferEntry))
    (.inl seekEntry)

def entry (SeekState TransferState : Type) : State SeekState TransferState := .inl 0
def exit (SeekState TransferState : Type) : State SeekState TransferState := .inr (.inr (.inr 2))

@[simp] theorem halt (seek : Machine (Alphabet tapeCount) SeekState) (seekEntry : SeekState)
    (transfer : Machine (Alphabet tapeCount) TransferState) (transferEntry : TransferState)
    (symbols : Symbols (Alphabet tapeCount)) :
    machine seek seekEntry transfer transferEntry (exit SeekState TransferState) symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, MultiTape.wire, StandardHead.BlankReturn.machine]

def initialFrame (context : Tapes (Alphabet tapeCount)) (index array : List Bool)
    (scalar counter scratch : List Symbol) (flag : Symbol) : Tapes (Alphabet tapeCount) :=
  Function.update (frame context index (buffer (word array)) scalar [] scratch flag) 3 (buffer counter)

def selectedArray (before block after : List Bool) : Turing.Tape Symbol :=
  Binary.tape (word before.reverse ++ [0]) (word (block ++ after) ++ [0]) ()

variable (context : Tapes (Alphabet tapeCount)) (extraWidths : Fin tapeCount → ℕ)
variable (sourceIsArray : Bool) (elementWidth transferTicks : ℕ) (seekUnit : ℕ → ℕ)
variable (seek : Machine (Alphabet tapeCount) SeekState) (seekEntry seekExit : SeekState)
variable (transfer : Machine (Alphabet tapeCount) TransferState) (transferEntry transferExit : TransferState)
variable (seekHalt : ∀ symbols, seek seekExit symbols = none)
variable (transferHalt : ∀ symbols, transfer transferExit symbols = none)
variable (seekRuns : ∀ (index : List Bool) (scratch : List Symbol)
    (_sameLength : scratch.length = index.length) (flag : Symbol)
    (array : Turing.Tape Symbol) (scalar : List Symbol) (arrayWidth : ℕ),
  Runs (widths extraWidths elementWidth index.length arrayWidth) (readOnly sourceIsArray)
    seek (value index * seekUnit index.length + 4 * index.length + 6)
    seekEntry (position 0) (frame context index array scalar index scratch flag)
    seekExit (position (value index * elementWidth))
    (frame context index ((Turing.Tape.move .right)^[value index * elementWidth] array) scalar
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false)))
variable (transferRuns : ∀ (index before block after replacement : List Bool) (scalar : List Symbol),
  block.length = elementWidth → replacement.length = elementWidth → scalar.length = elementWidth →
  (sourceIsArray = false → scalar = word replacement) →
  Runs (widths extraWidths elementWidth index.length (before ++ block ++ after).length)
    (readOnly sourceIsArray) transfer transferTicks transferEntry (position before.length)
    (frame context index (selectedArray before block after) scalar
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
    transferExit (position before.length)
    (frame context index (selectedArray before (if sourceIsArray then block else replacement) after)
      (if sourceIsArray then word block else scalar)
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false)))

include seekRuns transferRuns seekHalt transferHalt in
/-- Both directions share preparation, binary seeking, transfer, and restoration. -/
theorem runs (index before block after replacement : List Bool)
    (prefixLength : before.length = value index * elementWidth)
    (blockLength : block.length = elementWidth) (replacementLength : replacement.length = elementWidth)
    (scalar oldCounter scratch : List Symbol) (scalarLength : scalar.length = elementWidth)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) (scalarInput : sourceIsArray = false → scalar = word replacement) :
    ∃ ticks, ticks ≤ value index * (seekUnit index.length + elementWidth) + 6 * index.length + transferTicks + 14 ∧
      Runs (widths extraWidths elementWidth index.length (before ++ block ++ after).length)
        (readOnly sourceIsArray) (machine seek seekEntry transfer transferEntry) ticks
        (entry SeekState TransferState) (fun _ => 0)
        (initialFrame context index (before ++ block ++ after) scalar oldCounter scratch flag)
        (exit SeekState TransferState) (fun _ => 0)
        (frame context index (buffer (word (before ++ (if sourceIsArray then block else replacement) ++ after)))
          (if sourceIsArray then word block else scalar)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  let array := before ++ block ++ after
  let width := widths extraWidths elementWidth index.length array.length
  have copied := StandardTapeCommands.copy_runs (0 : Fin tapeCount) 3 (by simp [Fin.ext_iff, -Fin.val_eq_zero_iff]) width (readOnly sourceIsArray) (by simp [readOnly, Fin.ext_iff, -Fin.val_eq_zero_iff])
    index oldCounter (by simp [width, widths, Fin.ext_iff, -Fin.val_eq_zero_iff])
    (by simp [width, widths, Fin.ext_iff, -Fin.val_eq_zero_iff]) counterLength
    (initialFrame context index array scalar oldCounter scratch flag)
    (by simp [initialFrame, frame, Fin.ext_iff, -Fin.val_eq_zero_iff]) (Function.update_self _ _ _)
  have prepared : Function.update (initialFrame context index array scalar oldCounter scratch flag) 3
      (buffer (word index)) = frame context index (buffer (word array)) scalar index scratch flag := by
    funext name
    by_cases counter : name = 3
    · subst name; simp [frame, initialFrame, Fin.ext_iff, -Fin.val_eq_zero_iff]
    · simp [frame, initialFrame, counter]
  rw [prepared] at copied
  have sought := seekRuns index scratch scratchLength flag (buffer (word array)) scalar array.length
  have zero : position (tapeCount := tapeCount) 0 = fun _ => (0 : ℤ) := by funext name; simp [position]
  simp only [← Nat.cast_mul, ← prefixLength, zero] at sought
  have arraySplit : (Turing.Tape.move .right)^[before.length] (buffer (word array)) = selectedArray before block after := by
    rw [← buffer_padding (word array)]
    have moved := Move.right_list (word before) [0] (word (block ++ after) ++ [0])
    simpa [selectedArray, Binary.tape, word, array, List.map_append, List.append_assoc] using moved
  rw [arraySplit] at sought
  have transferred := transferRuns index before block after replacement scalar blockLength replacementLength scalarLength scalarInput
  let newBlock := if sourceIsArray then block else replacement
  have newLength : newBlock.length = elementWidth := by cases sourceIsArray <;> assumption
  obtain ⟨returnTicks, returnCost, returned⟩ := StandardHead.BlankReturn.runs before (newBlock ++ after) (by
    intro empty
    have blockEmpty : newBlock = [] := (List.append_eq_nil_iff.mp empty).1
    have zeroWidth : elementWidth = 0 := by simpa only [blockEmpty, List.length_nil] using newLength.symm
    apply List.eq_nil_of_length_eq_zero
    rw [prefixLength, zeroWidth, Nat.mul_zero])
  have restored := returned.wire_at_of_eq (oneTape (1 : Fin tapeCount)) width (readOnly sourceIsArray)
    (by intro name; cases name; simp [width, widths, array, List.length_append, newLength, blockLength])
    (by intro name premise; cases name; rfl)
    (position before.length) (fun _ => 0)
    (frame context index (selectedArray before newBlock after)
      (if sourceIsArray then word block else scalar)
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
    (frame context index (buffer (word (before ++ newBlock ++ after)))
      (if sourceIsArray then word block else scalar)
      (List.replicate index.length false) (word (List.replicate index.length false)) (data false))
    (by intro name; cases name; simp [position]) (by intro name; cases name; rfl)
    (by
      intro name outside
      have different : name ≠ 1 := by
        intro equal; subst name; exact outside ⟨(), rfl⟩
      simp [position, different])
    (by intro name; cases name; simp [frame, selectedArray, Fin.ext_iff, -Fin.val_eq_zero_iff])
    (by intro name; cases name; simp [frame, Fin.ext_iff, -Fin.val_eq_zero_iff, List.append_assoc])
    (by
      intro name outside
      have different : name ≠ 1 := by
        intro equal; subst name; exact outside ⟨(), rfl⟩
      simp [frame, different])
  have last := transferred.sequence restore 0 transferHalt restored
  have middle := sought.sequence (MultiTape.sequence transfer restore 0) (.inl transferEntry) seekHalt last
  have complete := copied.sequence _ (Sum.inl seekEntry)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) middle
  refine ⟨_, ?_, complete⟩
  nlinarith [returnCost]

end Polytime2.ArrayBlockCopy
