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
import Polytime2.Wiring

/-! # Moving an array head by a runtime unary width

The width tape is immutable and returns to its entry position. The data head
advances by the width without changing any symbols.
-/

namespace Polytime2.UnaryMove

open MultiTape CallingConvention
open Binary (Symbol data word)

abbrev Alphabet := CallingConvention.Alphabet Bool

private def scan : Machine Alphabet Bool := fun finished symbols =>
  if finished then none
  else if symbols false = 0 then some (true, stationary symbols)
  else some (false, fun name => (symbols name, some .right))

private def frame (left right : List Symbol) (array : Turing.Tape Symbol) : Tapes Alphabet
  | false => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)
  | true => array

private theorem scan_runs (count : ℕ) (left : List Symbol) (array : Turing.Tape Symbol)
    (width : Bool → ℕ) (readOnly : Bool → Bool) (position : Bool → ℤ) :
    Runs width readOnly scan count false position
      (frame left (List.replicate count (data true) ++ [0]) array)
      false (fun name => position name + count)
      (frame (List.replicate count (data true) ++ left) [0]
        ((Turing.Tape.move .right)^[count] array)) := by
  induction count generalizing left array position with
  | zero => simpa using Runs.zero (machine := scan) false position (frame left [0] array)
  | succ count hypothesis =>
    let tapes := frame left (List.replicate (count + 1) (data true) ++ [0]) array
    have instruction : scan false (MultiTape.read tapes) =
        some (false, fun name => (MultiTape.read tapes name, some .right)) := by
      simp [scan, MultiTape.read, tapes, frame, List.replicate_succ, data]
    have moved : act (fun name => (MultiTape.read tapes name, some .right)) tapes =
        frame (data true :: left) (List.replicate count (data true) ++ [0]) (array.move .right) := by
      rw [act_move]
      funext name
      cases name <;> simp [tapes, frame, List.replicate_succ,
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (data true :: left) (array.move .right) (fun name => position name + 1)
    have trace := Runs.next instruction (by intro name outside; rfl) (by
      simpa only [displacement, moved] using rest)
    convert trace using 1
    · funext name; simp only [Nat.cast_add, Nat.cast_one]; omega
    · simp [List.replicate_succ', List.append_assoc, Function.iterate_succ_apply]

noncomputable section Movement

private def restore : Machine Alphabet (Fin 2 ⊕ Fin 3) :=
  MultiTape.wire (oneTape false) StandardHead.BlankReturn.fromEnd

/-- A fixed finite controller; the number of moved cells is supplied on tape false. -/
def machine : Machine Alphabet (Bool ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.sequence scan restore (.inl 1)

@[simp] theorem halt (symbols : Symbols Alphabet) : machine (.inr (.inr 2)) symbols = none := by
  simp [machine, restore, MultiTape.sequence, MultiTape.wire,
    StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]

/-- Both tapes are preserved, the width head is restored, and the data head
advances exactly `count` cells. No capacity assumption is needed for movement. -/
theorem runs (count : ℕ) (array : Turing.Tape Symbol)
    (width : Bool → ℕ) (readOnly : Bool → Bool) (position : Bool → ℤ) :
    Runs width readOnly machine (2 * count + 5) (.inl false) position
      (fun name => if name then array else unary count)
      (.inr (.inr 2)) (fun name => if name then position name + count else position name)
      (fun name => if name then (Turing.Tape.move .right)^[count] array else unary count) := by
  have forward := scan_runs count [0] array width readOnly position
  let moved := (Turing.Tape.move .right)^[count] array
  let middle := frame (List.replicate count (data true) ++ [0]) [0] moved
  have stopped : Runs width readOnly scan 1 false (fun name => position name + count) middle
      true (fun name => position name + count) middle := by
    apply Runs.next (nextState := true) (actions := stationary (MultiTape.read middle))
      (by simp [scan, MultiTape.read, middle, frame]) (by intro name outside; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using
      Runs.zero (machine := scan) true (fun name => position name + count) middle
  have returned := (StandardHead.BlankReturn.fromEnd_runs (List.replicate count true)).regions
    (fun _ : Unit => width false) (fun _ => position false)
    (by simp)
  have restored := returned.wire (oneTape false) width readOnly (by intro name; rfl)
    (by intro name premise; rfl) middle (fun name => position name + count)
  simp only [List.length_replicate] at restored
  have initialTapes : install (oneTape false)
      (Binary.tape (word (List.replicate count true).reverse ++ [0]) [0]) middle = middle := by
    funext name
    cases name <;> simp [install_one, middle, frame, Binary.tape, word]
  have finalTapes : install (oneTape false) (fun _ : Unit => buffer (word (List.replicate count true))) middle =
      fun name => if name then moved else unary count := by
    funext name
    cases name <;> simp [install_one, middle, frame, unary, CallingConvention.tape, word, buffer]
  have initialPosition : install (oneTape false) (fun _ : Unit => (count : ℤ) + position false)
      (fun name => position name + count) = fun name => position name + count := by
    funext name; cases name <;> simp [install_one, add_comm]
  have finalPosition : install (oneTape false) (fun _ : Unit => (0 : ℤ) + position false)
      (fun name => position name + count) = fun name => if name then position name + count else position name := by
    funext name; cases name <;> simp [install_one]
  rw [initialTapes, finalTapes, initialPosition, finalPosition] at restored
  have complete := (forward.trans stopped).sequence restore (.inl 1) (by intro symbols; rfl) restored
  convert complete using 1 <;> try rfl
  · omega
  · funext name
    cases name <;> simp [frame, unary, CallingConvention.tape, word]
    exact (buffer_padding _).symm

end Movement
end Polytime2.UnaryMove
