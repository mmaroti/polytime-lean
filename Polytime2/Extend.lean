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


import Polytime2.MoveMarker

/-! # Physical extension of a marked interval

Replace the two boundary markers by padding rows and write new markers in the
adjacent blank cells. The surrounding tape is blank, so extension needs no
shifting of the payload. The head returns to the new first row. The fixed
padding value is a blank, unmarked track row in the multi-tape simulator.
-/

namespace Polytime2.Extend

open MultiTape

-- symbolLevel: interval payload rows; parameterLevel: runtime size names.
universe symbolLevel parameterLevel

variable {Symbol : Type symbolLevel}

def machine (padding : Symbol) : Machine (fun _ : Unit => Sweep.Alphabet Symbol) (Fin 7)
  | state, symbols => match state.val with
    | 0 => some (1, fun _ => (symbols (), some .left))
    | 1 => some (2, fun _ => (Sweep.row padding, some .left))
    | 2 => some (3, fun _ => (Sweep.leftMarker, some .right))
    | 3 => match symbols () with
      | some (.inr entry) => some (3, fun _ => (Sweep.row entry, some .right))
      | some (.inl true) => some (4, fun _ => (Sweep.row padding, some .right))
      | _ => none
    | 4 => some (5, fun _ => (Sweep.rightMarker, some .left))
    | 5 => if Sweep.isLeft (symbols ()) then some (6, fun _ => (Sweep.leftMarker, some .right))
      else some (5, fun _ => (symbols (), some .left))
    | _ => none

private theorem prepare (padding : Symbol) (rows : List Symbol) :
    Steps (machine padding) 3
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (3, Sweep.tape [Sweep.leftMarker] (Sweep.row padding :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) := by
  have first : step (machine padding)
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker])) =
      some (1, Sweep.tape [] (Sweep.leftMarker :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) := by
    simp only [step, machine, Fin.val_zero, Option.map_some]
    congr 2
    funext name
    cases name
    simp [MultiTape.act, MultiTape.read, Sweep.tape, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    cases rows <;> rfl
  have second : step (machine padding)
      (1, Sweep.tape [] (Sweep.leftMarker :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) =
      some (2, Sweep.tape [] (none :: Sweep.row padding :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) := by
    simp [step, machine]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    rfl
  have third : step (machine padding)
      (2, Sweep.tape [] (none :: Sweep.row padding :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) =
      some (3, Sweep.tape [Sweep.leftMarker] (Sweep.row padding :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) := by
    simp [step, machine]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  exact Steps.next first (Steps.next second (Steps.next third (.zero _)))

private theorem scan (padding : Symbol) (rows : List Symbol)
    (left right : List (Sweep.Alphabet Symbol)) :
    Steps (machine padding) rows.length
      (3, Sweep.tape left (rows.map Sweep.row ++ right))
      (3, Sweep.tape (rows.reverse.map Sweep.row ++ left) right) := by
  induction rows generalizing left with
  | nil => exact .zero _
  | cons entry rest hypothesis =>
    have first : step (machine padding)
        (3, Sweep.tape left (Sweep.row entry :: (rest.map Sweep.row ++ right))) =
        some (3, Sweep.tape (Sweep.row entry :: left) (rest.map Sweep.row ++ right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row]
      congr 2
    have remaining := hypothesis (Sweep.row entry :: left)
    simpa [List.map_cons, List.reverse_cons, List.map_append, List.append_assoc] using Steps.next first remaining

private theorem rewind (padding : Symbol) (rows : List Symbol)
    (current : Sweep.Alphabet Symbol) (notLeft : Sweep.isLeft current = false)
    (left right : List (Sweep.Alphabet Symbol)) :
    Steps (machine padding) (rows.length + 2)
      (5, Sweep.tape (rows.map Sweep.row ++ Sweep.leftMarker :: left) (current :: right))
      (6, Sweep.tape (Sweep.leftMarker :: left) ((rows.map Sweep.row).reverse ++ current :: right)) := by
  induction rows generalizing current right with
  | nil =>
    have first : step (machine padding)
        (5, Sweep.tape (Sweep.leftMarker :: left) (current :: right)) =
        some (5, Sweep.tape left (Sweep.leftMarker :: current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine padding)
        (5, Sweep.tape left (Sweep.leftMarker :: current :: right)) =
        some (6, Sweep.tape (Sweep.leftMarker :: left) (current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, Sweep.leftMarker, Sweep.isLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    exact Steps.next first (Steps.next second (.zero _))
  | cons entry rest hypothesis =>
    have first : step (machine padding)
        (5, Sweep.tape (Sweep.row entry :: (rest.map Sweep.row ++ Sweep.leftMarker :: left)) (current :: right)) =
        some (5, Sweep.tape (rest.map Sweep.row ++ Sweep.leftMarker :: left) (Sweep.row entry :: current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have remaining := hypothesis (Sweep.row entry) (by rfl) (current :: right)
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using Steps.next first remaining

/-- Create two padding rows by moving the physical boundary markers into blank
space. The payload is untouched, including when the interval is empty. -/
theorem steps (padding : Symbol) (rows : List Symbol) :
    Steps (machine padding) (2 * rows.length + 9)
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (6, Sweep.tape [Sweep.leftMarker] ((padding :: rows ++ [padding]).map Sweep.row ++ [Sweep.rightMarker])) := by
  have prepared := prepare padding rows
  have scanned := scan padding (padding :: rows) [Sweep.leftMarker] [Sweep.rightMarker]
  have extendRight : step (machine padding)
      (3, Sweep.tape ((padding :: rows).reverse.map Sweep.row ++ [Sweep.leftMarker]) [Sweep.rightMarker]) =
      some (4, Sweep.tape (Sweep.row padding :: ((padding :: rows).reverse.map Sweep.row ++ [Sweep.leftMarker])) []) := by
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.rightMarker]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have newMarker : step (machine padding)
      (4, Sweep.tape (Sweep.row padding :: ((padding :: rows).reverse.map Sweep.row ++ [Sweep.leftMarker])) []) =
      some (5, Sweep.tape ((padding :: rows).reverse.map Sweep.row ++ [Sweep.leftMarker])
        [Sweep.row padding, Sweep.rightMarker]) := by
    simp [step, machine]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have returned := rewind padding (padding :: rows).reverse (Sweep.row padding) (by rfl) [] [Sweep.rightMarker]
  have combined := prepared.trans (scanned.trans (Steps.next extendRight (Steps.next newMarker returned)))
  convert combined using 1 <;>
    simp [List.map_append, List.map_cons, List.map_reverse, List.append_assoc]
  omega

/-- A fixed finite TM0 controller extends every bounded interval in polynomial
time; the padding row is fixed before all runtime sizes and payloads. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype Symbol]
    (padding : Symbol) (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment (rows : List Symbol), rows.length ≤ MvPolynomial.eval assignment capacity →
        ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine padding))))^[ticks]
            (some (SingleTape.configuration (0, Sweep.tape [Sweep.leftMarker]
              (rows.map Sweep.row ++ [Sweep.rightMarker])))) =
            some (SingleTape.configuration (6, Sweep.tape [Sweep.leftMarker]
              ((padding :: rows ++ [padding]).map Sweep.row ++ [Sweep.rightMarker]))) ∧
          Turing.TM0.step (SingleTape.compile (machine padding))
            (SingleTape.configuration (6, Sweep.tape [Sweep.leftMarker]
              ((padding :: rows ++ [padding]).map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  refine ⟨4 * capacity + 18, ?_⟩
  intro assignment rows bounded
  refine ⟨2 * (2 * rows.length + 9), ?_, SingleTape.steps (machine padding) (steps padding rows), ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · exact SingleTape.halt (machine padding) _ (by rfl)

end Polytime2.Extend
