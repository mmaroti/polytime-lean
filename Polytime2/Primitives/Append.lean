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

import Polytime2.Primitives.Head
import Polytime2.Primitives.FixedCopy

/-! # Append an immutable word to a writable tape prefix

The source head is restored; the destination head finishes after the new field.
The source's surrounding blank determines its runtime width.
-/

namespace Polytime2.Append

open MultiTape CallingConvention
open Binary (Symbol word data)
open Copy (frame)

abbrev Alphabet := CallingConvention.Alphabet Bool

private def forward : Machine Alphabet Bool := fun finished symbols =>
  if finished then none else
  if symbols false = 0 then some (true, stationary symbols)
  else some (false, fun _ => (symbols false, some .right))

private theorem forward_runs (bits : List Bool) (old : List Symbol)
    (oldLength : old.length = bits.length)
    (sourceLeft targetLeft targetRight : List Symbol)
    (width : Bool → ℕ) (position : Bool → ℤ)
    (fits : 0 ≤ position true ∧ position true + bits.length ≤ width true) :
    Runs width (fun name => !name) forward bits.length false position
      (frame sourceLeft (word bits ++ [0]) targetLeft (old ++ targetRight))
      false (fun name => position name + bits.length)
      (frame (word bits.reverse ++ sourceLeft) [0]
        (word bits.reverse ++ targetLeft) targetRight) := by
  induction bits generalizing old sourceLeft targetLeft position with
  | nil =>
    have empty := List.eq_nil_of_length_eq_zero oldLength
    subst old
    simpa [word] using Runs.zero (machine := forward) false position
      (frame sourceLeft [0] targetLeft targetRight)
  | cons bit bits hypothesis =>
    cases old with
    | nil => simp at oldLength
    | cons previous old =>
      have nonblank : data bit ≠ 0 := by cases bit <;> decide
      have first : step forward
          (false, frame sourceLeft (word (bit :: bits) ++ [0]) targetLeft ((previous :: old) ++ targetRight)) =
          some (false, frame (data bit :: sourceLeft) (word bits ++ [0])
            (data bit :: targetLeft) (old ++ targetRight)) := by
        simp only [step, forward, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
          nonblank, Bool.false_eq_true, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk',
          Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis old (by simpa using oldLength) (data bit :: sourceLeft)
        (data bit :: targetLeft) (fun name => position name + 1) (by
          simp only [List.length_cons] at fits; constructor <;> omega)
      have trace := Runs.next_of_step first (position := position) (nextPosition := fun name => position name + 1)
        (by
          intro actions instruction
          simp [forward, MultiTape.read, frame, word, nonblank] at instruction
          cases instruction
          constructor
          · intro name outside
            cases name
            · rfl
            · simp only [Bool.not_true, Bool.false_eq_true, false_or] at outside
              simp only [List.length_cons] at fits
              omega
          · funext name; simp [displacement]) rest
      convert trace using 1 <;>
        first | rfl | (funext name; simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; omega)
              | simp [word, List.reverse_cons, List.append_assoc]

noncomputable def restore : Machine Alphabet (Fin 2 ⊕ Fin 3) :=
  wire (oneTape false) StandardHead.BlankReturn.fromEnd

noncomputable def machine : Machine Alphabet (Bool ⊕ (Fin 2 ⊕ Fin 3)) :=
  MultiTape.sequence forward restore (.inl 1)

@[simp] theorem halt (symbols : Symbols Alphabet) : machine (.inr (.inr 2)) symbols = none := by
  simp [machine, MultiTape.sequence, restore, wire, StandardHead.BlankReturn.fromEnd,
    StandardHead.BlankReturn.machine]

/-- Append a complete field while preserving the source and neighboring output. -/
theorem runs (bits : List Bool) (old : List Symbol) (oldLength : old.length = bits.length)
    (before : List Bool) (after : List Symbol)
    (width : Bool → ℕ) (fits : before.length + bits.length ≤ width true) :
    Runs width (fun name => !name) machine (2 * bits.length + 5)
      (.inl false) (fun name => if name then before.length else 0)
      (frame [0] (word bits ++ [0]) (word before.reverse ++ [0]) (old ++ after))
      (.inr (.inr 2)) (fun name => if name then (before.length : ℤ) + bits.length else 0)
      (frame [0] (word bits ++ [0]) (word (before ++ bits).reverse ++ [0]) after) := by
  have scanned := forward_runs bits old oldLength [0] (word before.reverse ++ [0]) after width
    (fun name => if name then before.length else 0) (by simp; omega)
  let middle := frame (word bits.reverse ++ [0]) [0]
    (word bits.reverse ++ (word before.reverse ++ [0])) after
  let headPosition : Bool → ℤ := fun name => (if name then (before.length : ℤ) else 0) + bits.length
  have stopped : Runs width (fun name => !name) forward 1 false headPosition middle
      true headPosition middle := by
    apply Runs.next (nextState := true) (actions := stationary (MultiTape.read middle))
      (by simp [forward, MultiTape.read, middle, frame]) (by intro name outside; rfl)
    simpa [stationary, displacement, act_stationary] using Runs.zero (machine := forward) true headPosition middle
  have returned := (StandardHead.BlankReturn.fromEnd_runs bits).regions (fun _ : Unit => width false)
    (fun _ => 0) (by intros; contradiction)
  have returned := returned.wire_at_of_eq (oneTape false) width (fun name => !name)
    (by intro name; rfl) (by intro name premise; rfl)
    headPosition (fun name => if name then (before.length : ℤ) + bits.length else 0)
    middle (frame [0] (word bits ++ [0]) (word (before ++ bits).reverse ++ [0]) after)
    (by intro name; cases name; simp [headPosition])
    (by intro name; cases name; simp)
    (by intro name outside; cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))
    (by intro name; cases name; rfl)
    (by intro name; cases name; exact buffer_padding _)
    (by intro name outside; cases name <;> first
      | exact False.elim (outside ⟨(), rfl⟩)
      | simp [middle, frame, word, List.reverse_append, List.append_assoc])
  have complete := (scanned.trans stopped).sequence restore (.inl 1) (by intro symbols; rfl) returned
  convert complete using 1 <;> first | rfl | omega

end Polytime2.Append
