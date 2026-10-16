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

import Polytime2.CallingConvention

/-! # Runtime-width transfer controlled by a unary tape

Tape 0 is an immutable unary width, tape 1 the source, and tape 2 the
destination. The controller is independent of the runtime width.
-/

namespace Polytime2.UnaryCopy

open MultiTape CallingConvention
open Binary (Symbol data)

abbrev Alphabet := CallingConvention.Alphabet (Fin 3)

/-- Forward copy, rewind control, rewind test, and halt. Only the destination
is overwritten. -/
def machine : Machine Alphabet (Fin 4)
  | 0, symbols =>
    if symbols 0 = 0 then some (1, stationary symbols)
    else some (0, fun name => (if name = 2 then symbols 1 else symbols name, some .right))
  | 1, symbols =>
    some (2, fun name => (symbols name, if name = 0 then some .left else none))
  | 2, symbols =>
    if symbols 0 = 0 then
      some (3, fun name => (symbols name, if name = 0 then some .right else none))
    else some (1, fun name => (symbols name, if name = 0 then none else some .left))
  | 3, _ => none

/-- A split width tape accompanies the two data tapes. -/
def frame (widthLeft widthRight sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Tapes Alphabet := fun name =>
  if name = 0 then Turing.Tape.mk' (Turing.ListBlank.mk widthLeft) (Turing.ListBlank.mk widthRight)
  else if name = 1 then
    Turing.Tape.mk' (Turing.ListBlank.mk sourceLeft) (Turing.ListBlank.mk sourceRight)
  else Turing.Tape.mk' (Turing.ListBlank.mk targetLeft) (Turing.ListBlank.mk targetRight)

private def ones (count : ℕ) := List.replicate count (data true)

private theorem forward (payload old : List Symbol) (sameLength : old.length = payload.length)
    (widthLeft sourceLeft sourceRight targetLeft targetRight : List Symbol)
    (width : Fin 3 → ℕ) (position : Fin 3 → ℤ)
    (fits : 0 ≤ position 2 ∧ position 2 + payload.length ≤ width 2) :
    Runs width (fun name => decide (name ≠ 2)) machine payload.length
      0 position (frame widthLeft (ones payload.length ++ [0]) sourceLeft
        (payload ++ sourceRight) targetLeft (old ++ targetRight))
      0 (fun name => position name + payload.length) (frame (ones payload.length ++ widthLeft) [0]
        (payload.reverse ++ sourceLeft) sourceRight
        (payload.reverse ++ targetLeft) targetRight) := by
  induction payload generalizing old widthLeft sourceLeft targetLeft position with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [ones] using Runs.zero (machine := machine) 0 position
      (frame widthLeft [0] sourceLeft sourceRight targetLeft targetRight)
  | cons symbol payload hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have first : step machine
          (0, frame widthLeft (ones (symbol :: payload).length ++ [0]) sourceLeft
            ((symbol :: payload) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight)) =
          some (0, frame (data true :: widthLeft) (ones payload.length ++ [0])
            (symbol :: sourceLeft) (payload ++ sourceRight)
            (symbol :: targetLeft) (old ++ targetRight)) := by
        simp only [step, machine]
        simp [MultiTape.read, frame, ones, List.replicate_succ, data]
        funext name
        fin_cases name <;>
          simp [act, frame,
            Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis old (by simpa using sameLength)
        (data true :: widthLeft) (symbol :: sourceLeft) (symbol :: targetLeft)
        (fun name => position name + 1) (by simp only [List.length_cons] at fits; constructor <;> omega)
      have safe : ∀ actions, machine 0 (MultiTape.read
          (frame widthLeft (ones (symbol :: payload).length ++ [0]) sourceLeft
            ((symbol :: payload) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight))) =
          some (0, actions) →
          Allowed width (fun name => decide (name ≠ 2)) position
            (MultiTape.read (frame widthLeft (ones (symbol :: payload).length ++ [0]) sourceLeft
              ((symbol :: payload) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight))) actions ∧
          (fun name => position name + 1) = fun name => position name + displacement (actions name).2 := by
        intro actions instruction
        simp [machine, MultiTape.read, frame, ones, List.replicate_succ, data] at instruction
        subst actions
        constructor
        · intro name outside
          by_cases destination : name = 2
          · subst name
            simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, false_or] at outside
            simp only [List.length_cons] at fits
            omega
          · simp [destination, MultiTape.read, frame, ones, List.replicate_succ, data]
        · rfl
      convert Runs.next_of_step first safe rest using 1 <;>
        simp [ones, List.replicate_succ', List.reverse_cons, List.append_assoc]
      funext name
      omega

private theorem rewind (sourceBlock targetBlock : List Symbol)
    (sameLength : targetBlock.length = sourceBlock.length)
    (widthRight sourceLeft sourceRight targetLeft targetRight : List Symbol)
    (width : Fin 3 → ℕ) (readOnly : Fin 3 → Bool) (position : Fin 3 → ℤ) :
    Runs width readOnly machine (2 * sourceBlock.length)
      1 position (frame (ones sourceBlock.length ++ [0]) widthRight
        (sourceBlock ++ sourceLeft) sourceRight (targetBlock ++ targetLeft) targetRight)
      1 (fun name => position name - sourceBlock.length) (frame [0] (ones sourceBlock.length ++ widthRight)
        sourceLeft (sourceBlock.reverse ++ sourceRight)
        targetLeft (targetBlock.reverse ++ targetRight)) := by
  induction sourceBlock generalizing targetBlock widthRight sourceRight targetRight position with
  | nil =>
    have empty : targetBlock = [] := List.eq_nil_of_length_eq_zero sameLength
    subst targetBlock
    simpa [ones] using Runs.zero (machine := machine) 1 position
      (frame [0] widthRight sourceLeft sourceRight targetLeft targetRight)
  | cons symbol sourceBlock hypothesis =>
    cases targetBlock with
    | nil => simp at sameLength
    | cons target targetBlock =>
      let middle := frame (ones sourceBlock.length ++ [0]) (data true :: widthRight)
        ((symbol :: sourceBlock) ++ sourceLeft) sourceRight
        ((target :: targetBlock) ++ targetLeft) targetRight
      have first : step machine
          (1, frame (ones (symbol :: sourceBlock).length ++ [0]) widthRight
            ((symbol :: sourceBlock) ++ sourceLeft) sourceRight
            ((target :: targetBlock) ++ targetLeft) targetRight) = some (2, middle) := by
        simp only [step, machine, Option.map_some]
        congr 2
        funext name
        fin_cases name <;>
          simp only [act, MultiTape.read, Turing.Tape.write_self] <;>
          simp [frame, middle, ones, List.replicate_succ,
            Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have second : step machine (2, middle) =
          some (1, frame (ones sourceBlock.length ++ [0]) (data true :: widthRight)
            (sourceBlock ++ sourceLeft) (symbol :: sourceRight)
            (targetBlock ++ targetLeft) (target :: targetRight)) := by
        have guard : MultiTape.read middle 0 ≠ 0 := by
          simp [MultiTape.read, middle, frame, data]
        simp only [step, machine, guard, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        fin_cases name <;>
          simp only [act, MultiTape.read, Turing.Tape.write_self] <;>
          simp [middle, frame,
            Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis targetBlock (by simpa using sameLength)
        (data true :: widthRight) (symbol :: sourceRight) (target :: targetRight)
        (fun name => position name - 1)
      have returned := Runs.next_of_step second (nextPosition := fun name => position name - 1)
        (position := fun name => position name + if name = 0 then -1 else 0) (by
          intro actions instruction
          have guard : MultiTape.read middle 0 ≠ 0 := by
            simp [MultiTape.read, middle, frame, data]
          simp only [machine, guard, ↓reduceIte] at instruction
          cases instruction
          constructor
          · intro name outside; rfl
          · funext name; fin_cases name <;> simp [displacement, sub_eq_add_neg]) rest
      have complete := Runs.next_of_step first (position := position) (by
        intro actions instruction
        simp only [machine] at instruction
        cases instruction
        constructor
        · intro name outside; rfl
        · funext name; fin_cases name <;> simp [displacement]) returned
      convert complete using 1 <;>
        simp [ones, List.replicate_succ', List.reverse_cons, List.append_assoc]
      funext name
      omega

/-- The same finite controller copies every runtime width, preserves the width
and source tapes, and restores all three heads in linear time. -/
theorem runs (payload old : List Symbol) (sameLength : old.length = payload.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol)
    (width : Fin 3 → ℕ) (position : Fin 3 → ℤ)
    (fits : 0 ≤ position 2 ∧ position 2 + payload.length ≤ width 2) :
    Runs width (fun name => decide (name ≠ 2)) machine (3 * payload.length + 3)
      0 position (frame [0] (List.replicate payload.length (data true) ++ [0]) sourceLeft
        (payload ++ sourceRight) targetLeft (old ++ targetRight))
      3 position (frame [0] (List.replicate payload.length (data true) ++ [0]) sourceLeft
        (payload ++ sourceRight) targetLeft (payload ++ targetRight)) := by
  have copied := (forward payload old sameLength [0] sourceLeft sourceRight targetLeft targetRight
    width position fits)
  let middle := frame (ones payload.length ++ [0]) [0]
    (payload.reverse ++ sourceLeft) sourceRight (payload.reverse ++ targetLeft) targetRight
  have handover : step machine (0, middle) = some (1, middle) := by
    simp [step, machine, MultiTape.read, middle, frame]
  have restored := (rewind payload.reverse payload.reverse rfl [0]
    sourceLeft sourceRight targetLeft targetRight width
      (fun name => decide (name ≠ 2)) (fun name => position name + payload.length))
  simp only [List.length_reverse, List.reverse_reverse] at restored
  let final := frame [0] (ones payload.length ++ [0])
    sourceLeft (payload ++ sourceRight) targetLeft (payload ++ targetRight)
  let boundary := frame [] (0 :: (ones payload.length ++ [0]))
    sourceLeft (payload ++ sourceRight) targetLeft (payload ++ targetRight)
  have left : step machine (1, final) = some (2, boundary) := by
    simp only [step, machine, Option.map_some]
    congr 2
    funext name
    fin_cases name <;>
      simp only [act, MultiTape.read, Turing.Tape.write_self] <;>
      simp [final, boundary, frame, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have right : step machine (2, boundary) = some (3, final) := by
    have guard : MultiTape.read boundary 0 = 0 := by simp [MultiTape.read, boundary, frame]
    simp only [step, machine, guard, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    fin_cases name <;>
      simp only [act, MultiTape.read, Turing.Tape.write_self] <;>
      simp [final, boundary, frame, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have tail := Runs.next_of_step (width := width) (readOnly := fun name => decide (name ≠ 2)) right (position := fun name => position name + if name = 0 then -1 else 0)
    (nextPosition := position) (by
      intro actions instruction
      have guard : MultiTape.read boundary 0 = 0 := by simp [MultiTape.read, boundary, frame]
      simp only [machine, guard, ↓reduceIte] at instruction
      cases instruction
      constructor
      · intro name outside; rfl
      · funext name; fin_cases name <;> simp [displacement])
    (Runs.zero (machine := machine) 3 position final)
  have last := Runs.next_of_step left (position := position) (by
    intro actions instruction
    simp only [machine] at instruction
    cases instruction
    constructor
    · intro name outside; rfl
    · funext name; fin_cases name <;> simp [displacement]) tail
  have positionEq : (fun name => position name + (payload.length : ℤ) - payload.length) = position := by
    funext name; omega
  rw [positionEq] at restored
  have body := restored.trans last
  have middleRun := Runs.next_of_step handover (position := fun name => position name + payload.length) (by
    intro actions instruction
    have guard : MultiTape.read middle 0 = 0 := by simp [MultiTape.read, middle, frame]
    simp only [machine, guard, ↓reduceIte] at instruction
    cases instruction
    constructor
    · intro name outside; rfl
    · simp [stationary, displacement]) body
  have trace := copied.trans middleRun
  convert trace using 1 <;> first | rfl | omega

@[simp] theorem halt (symbols : Symbols Alphabet) : machine 3 symbols = none := rfl

end Polytime2.UnaryCopy
