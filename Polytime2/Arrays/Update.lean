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

import Polytime2.Arrays.BlockCopy
import Mathlib.Data.Fin.Tuple.Basic

/-! # Separate-output array update with a certified block command

Copying the immutable source and patching the result share one controller and
one preservation proof, independently of the element-width command.
-/

namespace Polytime2.ArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol data word value)

variable {extra : ℕ} {BlockState : Type}

private instance : Fact (6 ≤ extra + 6) := ⟨by omega⟩

@[simp] private theorem small_mod_seven (number : ℕ) (small : number < 7) :
    number % (extra + 7) = number := Nat.mod_eq_of_lt (by omega)

@[simp] private theorem small_mod_six (number : ℕ) (small : number < 6) :
    number % (extra + 6) = number := Nat.mod_eq_of_lt (by omega)

abbrev Alphabet (extra : ℕ) := CallingConvention.Alphabet (Fin (extra + 7))

/-- Insert the immutable source beside the block command's tapes. -/
def blockWiring : Fin (extra + 6) ↪ Fin (extra + 7) :=
  ⟨(fun name => (1 : Fin (extra + 7)).succAbove (Equiv.swap 1 2 name)),
    Fin.succAbove_right_injective.comp (Equiv.swap 1 2).injective⟩

def insertSource {Value : Type} (source : Value) (values : Fin (extra + 6) → Value) :
    Fin (extra + 7) → Value := Fin.insertNth 1 source (fun name => values (Equiv.swap 1 2 name))

@[simp] private theorem insert_source {Value : Type} (source : Value) (values : Fin (extra + 6) → Value) :
    insertSource source values 1 = source := by simp [insertSource]

@[simp] private theorem insert_block {Value : Type} (source : Value) (values : Fin (extra + 6) → Value)
    (name : Fin (extra + 6)) : insertSource source values (blockWiring name) = values name := by
  simp [insertSource, blockWiring]

private theorem blockWiring_one : blockWiring (extra := extra) 1 = 3 := by
  apply Fin.ext
  simp [blockWiring, Equiv.swap_apply_def, Fin.succAbove, Fin.ext_iff, -Fin.val_eq_zero_iff]

/-- The block command's array cursor becomes the separate result tape. -/
def frame (context : Tapes (Alphabet extra)) (index : List Bool)
    (array : Turing.Tape Symbol) (element : List Symbol) (result : Turing.Tape Symbol)
    (counter : List Bool) (scratch : List Symbol) (flag : Symbol) : Tapes (Alphabet extra) :=
  insertSource array (ArrayBlockCopy.frame (fun name => context (blockWiring name)) index result element counter scratch flag)

def widths (extraWidths : Fin (extra + 7) → ℕ) (elementWidth digits arrayWidth : ℕ) : Fin (extra + 7) → ℕ :=
  insertSource arrayWidth (ArrayBlockCopy.widths (fun name => extraWidths (blockWiring name)) elementWidth digits arrayWidth)

def readOnly : Fin (extra + 7) → Bool := insertSource true (ArrayBlockCopy.readOnly false)

noncomputable def copyArray : Machine (Alphabet extra) (Fin 3) := StandardTapeCommands.copy 1 3 (by simp [Fin.ext_iff, -Fin.val_eq_zero_iff])
noncomputable def access (block : Machine (ArrayBlockCopy.Alphabet (extra + 6)) BlockState) :
    Machine (Alphabet extra) BlockState := MultiTape.wire blockWiring block
noncomputable def machine (block : Machine (ArrayBlockCopy.Alphabet (extra + 6)) BlockState)
    (blockEntry : BlockState) : Machine (Alphabet extra) (Fin 3 ⊕ BlockState) :=
  MultiTape.sequence copyArray (access block) blockEntry

def initialFrame (context : Tapes (Alphabet extra)) (index array : List Bool)
    (element result counter scratch : List Symbol) (flag : Symbol) : Tapes (Alphabet extra) :=
  insertSource (buffer (word array))
    (Function.update (ArrayBlockCopy.initialFrame (fun name => context (blockWiring name)) index array
      element counter scratch flag) 1 (buffer result))

/-- A block command may use extra immutable tapes, such as a unary width header. -/
theorem runs (context : Tapes (Alphabet extra)) (extraWidths : Fin (extra + 7) → ℕ)
    (elementWidth unit overhead : ℕ)
    (blockCommand : Machine (ArrayBlockCopy.Alphabet (extra + 6)) BlockState)
    (blockEntry blockExit : BlockState)
    (index before block after replacement : List Bool)
    (oldOutput oldCounter scratch : List Symbol) (flag : Symbol)
    (outputLength : oldOutput.length = (before ++ block ++ after).length)
    (blockRuns : ∃ ticks, ticks ≤ value index * unit + overhead ∧
      Runs (ArrayBlockCopy.widths (fun name => extraWidths (blockWiring name)) elementWidth index.length
          (before ++ block ++ after).length) (ArrayBlockCopy.readOnly false) blockCommand ticks
        blockEntry (fun _ => 0)
        (ArrayBlockCopy.initialFrame (fun name => context (blockWiring name)) index (before ++ block ++ after)
          (word replacement) oldCounter scratch flag)
        blockExit (fun _ => 0)
        (ArrayBlockCopy.frame (fun name => context (blockWiring name)) index
          (buffer (word (before ++ replacement ++ after))) (word replacement)
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false))) :
    ∃ ticks, ticks ≤ 2 * (before ++ block ++ after).length + value index * unit + overhead + 3 ∧
      Runs (widths extraWidths elementWidth index.length (before ++ block ++ after).length) readOnly
        (machine blockCommand blockEntry) ticks (.inl 0) (fun _ => 0)
        (initialFrame context index (before ++ block ++ after) (word replacement) oldOutput oldCounter scratch flag)
        (.inr blockExit) (fun _ => 0)
        (frame context index (buffer (word (before ++ block ++ after))) (word replacement)
          (buffer (word (before ++ replacement ++ after)))
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  let array := before ++ block ++ after
  let width := widths extraWidths elementWidth index.length array.length
  let initial := initialFrame context index array (word replacement) oldOutput oldCounter scratch flag
  let middle := Function.update initial 3 (buffer (word array))
  let final := frame context index (buffer (word array)) (word replacement)
    (buffer (word (before ++ replacement ++ after)))
    (List.replicate index.length false) (word (List.replicate index.length false)) (data false)
  have copied := StandardTapeCommands.copy_runs (1 : Fin (extra + 7)) 3
    (by simp [Fin.ext_iff, -Fin.val_eq_zero_iff]) width readOnly
    (by rw [← blockWiring_one]; simp [readOnly, ArrayBlockCopy.readOnly, -Fin.val_eq_zero_iff])
    array oldOutput (by simp [width, widths])
    (by rw [← blockWiring_one]; simp [width, widths, ArrayBlockCopy.widths]) outputLength initial
    (by simp [initial, initialFrame])
    (by rw [← blockWiring_one]; simp [initial, initialFrame])
  obtain ⟨ticks, cost, trace⟩ := blockRuns
  have patched := trace.wire_of_eq blockWiring width readOnly
    (by intro name; simp [width, widths, array])
    (by intro name premise; simpa [readOnly] using premise)
    middle final
    (by
      intro name
      by_cases result : name = 1
      · subst name
        simp [middle, initial, initialFrame, blockWiring_one, ArrayBlockCopy.initialFrame, ArrayBlockCopy.frame,
          array, Fin.ext_iff, -Fin.val_eq_zero_iff]
      · have different : blockWiring name ≠ 3 := by
          rw [← blockWiring_one]; exact blockWiring.injective.ne result
        simp [middle, different, initial, initialFrame, result, array])
    (by intro name; simp [final, frame])
    (by
      intro name outside
      have source : name = 1 := by
        by_contra different
        obtain ⟨localName, equal⟩ := Fin.exists_succAbove_eq different
        exact outside ⟨Equiv.swap 1 2 localName, by simpa [blockWiring] using equal⟩
      subst name
      simp [final, middle, initial, initialFrame, frame, Fin.ext_iff, -Fin.val_eq_zero_iff])
  have complete := copied.sequence _ blockEntry
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) patched
  exact ⟨_, by dsimp [array] at *; omega, complete⟩

end Polytime2.ArrayUpdate
