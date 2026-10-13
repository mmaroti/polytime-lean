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

import Polytime2.StandardHead

/-! # Reading a fixed-width value into finite control

Finite scalar tables use a specialization-fixed register. Reading preserves
every input cell and restores its head; no runtime-sized object is put into
finite control.
-/

namespace Polytime2.StandardFixedRead

open MultiTape CallingConvention
open Binary (Symbol data word)

abbrev Alphabet := CallingConvention.Alphabet Unit
abbrev Memory (width : ℕ) := Fin width → Bool
abbrev State (width : ℕ) := (Bool × Fin (width + 1)) × Memory width

def store {width : ℕ} (offset : ℕ) (memory : Memory width) (bit : Bool) : Memory width :=
  fun index => if index.val = offset then bit else memory index

def collect {width : ℕ} (offset : ℕ) (memory : Memory width) : List Bool → Memory width
  | [] => memory
  | bit :: bits => collect (offset + 1) (store offset memory bit) bits

private theorem collect_get {width : ℕ} (offset : ℕ) (memory : Memory width)
    (bits : List Bool) (index : Fin width) :
    collect offset memory bits index =
      if offset ≤ index.val ∧ index.val < offset + bits.length then
        (bits[index.val - offset]?).getD false else memory index := by
  induction bits generalizing offset memory with
  | nil =>
    simp only [collect, List.length_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | cons bit bits hypothesis =>
    rw [collect, hypothesis]
    by_cases equal : index.val = offset
    · simp [equal, store]
    · by_cases before : index.val < offset
      · have notLater : ¬offset + 1 ≤ index.val := by omega
        have notCurrent : ¬offset ≤ index.val := by omega
        simp [notLater, notCurrent, store, equal]
      · have later : offset + 1 ≤ index.val := by omega
        have current : offset ≤ index.val := by omega
        have shifted : index.val - offset = index.val - (offset + 1) + 1 := by omega
        have range : (index.val < offset + (bit :: bits).length) =
            (index.val < offset + 1 + bits.length) := by simp; omega
        simp only [later, true_and, current, range, shifted, List.getElem?_cons_succ]
        simp only [store, equal, ↓reduceIte]

/-- All collected bits are available once the fixed input word has been read. -/
theorem collect_complete (width : ℕ) (bits : List Bool) (length : bits.length = width)
    (memory : Memory width) :
    collect 0 memory bits = fun index => (bits[index.val]?).getD false := by
  funext index
  rw [collect_get]
  simp [length, index.isLt]

def machine (width : ℕ) : Machine Alphabet (State width)
  | ((false, remaining), memory), symbols =>
    if finished : remaining.val = 0 then
      some (((true, Fin.last width), memory), stationary symbols)
    else some (((false, ⟨remaining.val - 1, by omega⟩),
      store (width - remaining.val) memory (symbols () == 2)),
      fun _ => (symbols (), some .right))
  | ((true, remaining), memory), symbols =>
    if finished : remaining.val = 0 then none
    else some (((true, ⟨remaining.val - 1, by omega⟩), memory),
      fun _ => (symbols (), some .left))

private theorem forward (width offset : ℕ) (memory : Memory width)
    (bits : List Bool) (fits : offset + bits.length = width) (left right : List Symbol) :
    Runs (fun _ : Unit => width) (fun _ => true) (machine width) bits.length
      ((false, ⟨bits.length, by omega⟩), memory) (fun _ => offset)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (word bits ++ right)))
      ((false, 0), collect offset memory bits) (fun _ => width)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk ((word bits).reverse ++ left))
        (Turing.ListBlank.mk right)) := by
  induction bits generalizing offset memory left with
  | nil =>
    have position : offset = width := by simpa using fits
    subst offset
    simpa [collect, word] using Runs.zero (machine := machine width) ((false, 0), memory)
      (fun _ : Unit => (width : ℤ))
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right))
  | cons bit bits hypothesis =>
    have nextFits : offset + 1 + bits.length = width := by simp at fits; omega
    have selected : width - (bit :: bits).length = offset := by omega
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have digit : (data bit == 2) = bit := by cases bit <;> decide
    have instruction : machine width
        ((false, ⟨(bit :: bits).length, by omega⟩), memory)
        (MultiTape.read (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
          (Turing.ListBlank.mk (word (bit :: bits) ++ right)))) =
        some (((false, ⟨bits.length, by omega⟩), store offset memory bit),
          fun _ => (data bit, some .right)) := by
      simp only [machine, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceDIte, Nat.add_sub_cancel, MultiTape.read, word,
        List.map_cons, List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, digit]
      rw [show width - (bits.length + 1) = offset by simpa only [List.length_cons] using selected]
    have allowed : Allowed (fun _ : Unit => width) (fun _ => true) (fun _ => offset)
        (MultiTape.read (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
          (Turing.ListBlank.mk (word (bit :: bits) ++ right))))
        (fun _ => (data bit, some .right)) := by intro name premise; rfl
    have rest := hypothesis (offset + 1) (store offset memory bit) nextFits (data bit :: left)
    have moved : act (fun _ : Unit => (data bit, some Turing.Dir.right))
        (fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk left)
          (Turing.ListBlank.mk (word (bit :: bits) ++ right))) =
        fun _ : Unit => Turing.Tape.mk' (Turing.ListBlank.mk (data bit :: left))
          (Turing.ListBlank.mk (word bits ++ right)) := by
      funext name
      simp [act, word, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have positions : (fun _ : Unit => (offset : ℤ) + displacement (some Turing.Dir.right)) =
        fun _ : Unit => ((offset + 1 : ℕ) : ℤ) := by funext name; simp [displacement]
    rw [← moved, ← positions] at rest
    simpa [collect, word, List.reverse_cons, List.append_assoc] using Runs.next instruction allowed rest

/-- Fixed scalar reading takes linear time, preserves every input bit, and
returns the complete register with the tape head at its original start. -/
theorem runsWithContext (width : ℕ) (bits : List Bool) (length : bits.length = width)
    (memory : Memory width) (left right : List Symbol) :
    Runs (fun _ : Unit => width) (fun _ => true) (machine width) (2 * width + 1)
      ((false, Fin.last width), memory) (fun _ => 0) (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right)))
      ((true, 0), fun index => (bits[index.val]?).getD false) (fun _ => 0)
      (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right))) := by
  let finalMemory := collect 0 memory bits
  have read := forward width 0 memory bits (by simpa using length) left right
  simp only [Nat.cast_zero, length] at read
  let middle := fun _ : Unit => Turing.Tape.mk'
    (Turing.ListBlank.mk ((word bits).reverse ++ left)) (Turing.ListBlank.mk right)
  have switch : Runs (fun _ : Unit => width) (fun _ => true) (machine width) 1
      ((false, 0), finalMemory) (fun _ => width) middle
      ((true, Fin.last width), finalMemory) (fun _ => width) middle := by
    apply Runs.next (nextState := ((true, Fin.last width), finalMemory))
      (actions := stationary (MultiTape.read middle)) (by simp [machine])
      (by intro name premise; rfl)
    simpa only [act_stationary, stationary, displacement, add_zero] using
      Runs.zero (machine := machine width) ((true, Fin.last width), finalMemory)
        (fun _ => width) middle
  have returned := (StandardHead.move_runs width .left (fun _ : Unit => width)
    (fun _ => true) (fun _ => width) middle).rename
    (fun remaining => ((true, remaining), finalMemory)) (target := machine width) (by
      intro state symbols next actions instruction
      simpa [Move.machine, machine] using instruction)
  have finalPosition : (fun _ : Unit => (width : ℤ) +
      width * displacement (some Turing.Dir.left)) = fun _ => (0 : ℤ) := by
    funext name
    simp [displacement]
  have reversed : (fun name : Unit => (Turing.Tape.move Turing.Dir.left)^[width]
      (middle name)) = fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left)
        (Turing.ListBlank.mk (word bits ++ right)) := by
    funext name
    have rightward := Move.right_list (word bits) left right
    have undo : Function.LeftInverse
        (Turing.Tape.move Turing.Dir.left : Turing.Tape Symbol → Turing.Tape Symbol)
        (Turing.Tape.move Turing.Dir.right) := by
      intro source
      simp
    have back := congrArg ((Turing.Tape.move Turing.Dir.left)^[width]) rightward
    have cancel := undo.iterate width
    simp only [word, List.length_map, length] at back
    rw [cancel] at back
    simpa only [middle, word] using back.symm
  rw [finalPosition, reversed] at returned
  have complete := read.trans (switch.trans returned)
  dsimp only [finalMemory] at complete
  rw [collect_complete width bits length memory] at complete
  convert complete using 1 <;> first | rfl | omega

/-- The public reader uses a standalone canonical data region. -/
theorem runs (width : ℕ) (bits : List Bool) (length : bits.length = width)
    (memory : Memory width) :
    Runs (fun _ : Unit => width) (fun _ => true) (machine width) (2 * width + 1)
      ((false, Fin.last width), memory) (fun _ => 0) (fun _ => buffer (word bits))
      ((true, 0), fun index => (bits[index.val]?).getD false) (fun _ => 0)
      (fun _ => buffer (word bits)) := by
  simpa only [buffer_padding] using runsWithContext width bits length memory [0] [0]

end Polytime2.StandardFixedRead
