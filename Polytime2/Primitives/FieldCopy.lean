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

import Polytime2.Primitives.UnaryMove
import Polytime2.Primitives.UnaryCopy

/-! # Copying a polynomial-width field at a unary offset

The offset and length are immutable unary words. A record and a scalar use
separate tapes. The record is immutable and the selected field is copied to the scalar.
-/

namespace Polytime2.FieldCopy

open MultiTape CallingConvention
open Binary (Symbol word)

abbrev Alphabet := CallingConvention.Alphabet (Fin 4)
abbrev State := (Bool ⊕ (Fin 2 ⊕ Fin 3)) ⊕ (Fin 4 ⊕ (Fin 2 ⊕ Fin 3))

def readOnly (name : Fin 4) : Bool :=
  decide (name ≠ 3)

def position (offset : ℤ) (name : Fin 4) : ℤ := if name = 2 then offset else 0

def frame (offset length : ℕ) (record scalar : Turing.Tape Symbol) : Tapes Alphabet :=
  ![unary offset, unary length, record, scalar]

def seekWiring : Bool ↪ Fin 4 :=
  ⟨(fun name => if name then 2 else 0), by intro a b equal; cases a <;> cases b <;> simp_all⟩

def copyWiring : Fin 3 ↪ Fin 4 :=
  ⟨(fun name => if name = 0 then 1 else if name = 1 then
      2 else 3), by
    intro a b equal; fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem seekWiring_apply (name : Bool) : seekWiring name = if name then 2 else 0 := rfl
@[simp] theorem copyWiring_apply (name : Fin 3) :
    copyWiring name = (if name = 0 then 1 else if name = 1 then
      2 else 3) := rfl

noncomputable def seek : Machine Alphabet (Bool ⊕ (Fin 2 ⊕ Fin 3)) := wire seekWiring UnaryMove.machine
noncomputable def transfer : Machine Alphabet (Fin 4) :=
  wire copyWiring UnaryCopy.machine
noncomputable def restore : Machine Alphabet (Fin 2 ⊕ Fin 3) :=
  wire (oneTape 2) StandardHead.BlankReturn.fromEnd

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence seek (MultiTape.sequence transfer restore (.inl 1)) (.inl 0)

def entry : State := .inl (.inl false)
def exit : State := .inr (.inr (.inr 2))

@[simp] theorem halt (symbols : Symbols Alphabet) :
    machine exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, restore, wire, StandardHead.BlankReturn.fromEnd,
    StandardHead.BlankReturn.machine]

/-- Seeking preserves the entire record. -/
theorem seek_runs (offset length : ℕ) (record scalar : Turing.Tape Symbol)
    (width : Fin 4 → ℕ) :
    Runs width readOnly seek (2 * offset + 5) (.inl false) (position 0)
      (frame offset length record scalar) (.inr (.inr 2)) (position offset)
      (frame offset length ((Turing.Tape.move .right)^[offset] record) scalar) := by
  have trace := UnaryMove.runs offset record (fun name => width (seekWiring name))
    (fun name => readOnly (seekWiring name)) (fun _ => 0)
  exact trace.wire_at_of_eq seekWiring width readOnly
    (by intro name; rfl) (by intro name premise; exact premise)
    (position 0) (position offset)
    (frame offset length record scalar)
    (frame offset length ((Turing.Tape.move .right)^[offset] record) scalar)
    (by intro name; cases name <;> rfl)
    (by intro name; cases name <;> simp [position])
    (by intro name outside; fin_cases name <;> simp_all [position])
    (by intro name; cases name <;> rfl)
    (by intro name; cases name <;> simp [frame])
    (by intro name outside; fin_cases name <;> simp_all [frame])

/-- The record head is at the start of its selected field. -/
def selected (before : List Bool) (block after : List Symbol) : Turing.Tape Symbol :=
  Binary.tape (word before.reverse ++ [0]) (block ++ after) ()

/-- Unary-controlled transfer restores both data heads, including zero widths. -/
theorem transfer_runs (before bits : List Bool)
    (after old : List Symbol) (oldLength : old.length = bits.length)
    (width : Fin 4 → ℕ)
    (scalarFits : bits.length ≤ width 3) :
    Runs width readOnly transfer (3 * bits.length + 3)
      0 (position before.length)
      (frame before.length bits.length
        (selected before (word bits) after)
        (buffer old))
      3 (position before.length)
      (frame before.length bits.length (selected before (word bits) after) (buffer (word bits))) := by
  have trace := UnaryCopy.runs (word bits) old (by simpa [word] using oldLength)
    (word before.reverse ++ [0]) after [] []
    (fun name => width (copyWiring name))
    (fun name => position before.length (copyWiring name))
    (by simp [position, word]; omega)
  simpa [word, transfer] using trace.wire_at_of_eq copyWiring width readOnly
    (by intro name; rfl)
    (by intro name premise; fin_cases name <;> simp_all [readOnly])
    (position before.length) (position before.length)
    (frame before.length bits.length (selected before (word bits) after) (buffer old))
    (frame before.length bits.length (selected before (word bits) after) (buffer (word bits)))
    (by intro name; rfl) (by intro name; rfl) (by intros; rfl)
    (by intro name; fin_cases name <;> simp [frame, UnaryCopy.frame, selected, unary, CallingConvention.tape, word, buffer, Binary.tape, Turing.Tape.mk₁, Turing.Tape.mk₂]; exact (buffer_padding _).symm)
    (by intro name; fin_cases name <;> simp [frame, UnaryCopy.frame, selected, unary, CallingConvention.tape, word, buffer, Binary.tape, Turing.Tape.mk₁, Turing.Tape.mk₂]; exact (buffer_padding _).symm)
    (by intro name outside; fin_cases name <;> simp_all [frame, Set.mem_range, Fin.exists_fin_succ])

/-- The known binary prefix restores the record head without a boundary marker. -/
theorem restore_runs (before bits : List Bool) (after : List Symbol)
    (width : Fin 4 → ℕ) :
    Runs width readOnly restore (before.length + 3)
      (.inl 1) (position before.length)
      (frame before.length bits.length (selected before (word bits) after) (buffer (word bits)))
      (.inr 2) (position 0)
      (frame before.length bits.length (buffer (word (before ++ bits) ++ after)) (buffer (word bits))) := by
  have trace := (StandardHead.BlankReturn.fromPrefix_runs before (word bits ++ after)).regions
    (fun _ : Unit => width 2) (fun _ => 0) (by intros; contradiction)
  simpa [restore, position, word, List.append_assoc] using
    trace.wire_at_of_eq (oneTape (2 : Fin 4)) width readOnly
      (by intro name; rfl) (by intro name premise; rfl)
      (position before.length) (position 0)
      (frame before.length bits.length (selected before (word bits) after) (buffer (word bits)))
      (frame before.length bits.length (buffer (word (before ++ bits) ++ after)) (buffer (word bits)))
      (by intro name; cases name; simp [position])
      (by intro name; cases name; simp [position])
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))
      (by intro name; cases name; rfl)
      (by intro name; cases name; simp [frame, word, List.append_assoc])
      (by intro name outside; fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))

/-- Extract a field, preserving the record and restoring all heads. -/
theorem runs (before bits : List Bool)
    (after old : List Symbol) (oldLength : old.length = bits.length)
    (width : Fin 4 → ℕ)
    (scalarFits : bits.length ≤ width 3) :
    Runs width readOnly (machine)
      (3 * before.length + 3 * bits.length + 13) entry (fun _ => 0)
      (frame before.length bits.length
        (buffer (word before ++ (word bits) ++ after))
        (buffer old))
      exit (fun _ => 0)
      (frame before.length bits.length (buffer (word (before ++ bits) ++ after)) (buffer (word bits))) := by
  let initialRecord := buffer (word before ++ (word bits) ++ after)
  let scalar := buffer (old)
  have sought := seek_runs before.length bits.length initialRecord scalar width
  have moved : (Turing.Tape.move .right)^[before.length] initialRecord =
      selected before (word bits) after := by
    rw [show initialRecord = Turing.Tape.mk' (Turing.ListBlank.mk [])
      (Turing.ListBlank.mk (word before ++ (word bits) ++ after)) from rfl]
    have trace := Move.right_list (word before) [] ((word bits) ++ after)
    simpa [selected, Binary.tape, word, Binary.mk_append_blank, List.append_assoc] using trace
  rw [moved] at sought
  have copied := transfer_runs before bits after old oldLength width scalarFits
  have returned := restore_runs before bits after width
  have tail := copied.sequence restore (.inl 1)
    (by intro symbols; simp [transfer, wire, UnaryCopy.halt]) returned
  have complete := sought.sequence (MultiTape.sequence transfer restore (.inl 1)) (.inl 0)
    (by intro symbols; simp [seek, wire, UnaryMove.halt]) tail
  have zero : position 0 = fun _ => (0 : ℤ) := by funext name; simp [position]
  rw [zero] at complete
  convert complete using 1 <;> first | rfl | omega

end Polytime2.FieldCopy
