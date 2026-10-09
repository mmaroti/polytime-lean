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

import Polytime.UnaryMachine

/-! # Resetting a runtime unary header counter

Erase one selected unit and shift only preceding fields one cell right into
its place. Repeat until the selected separator is reached, then return to the
header. All following storage stays in place; no loop fuel is supplied.
-/

namespace Polytime.HeaderResetMachine

open UnaryMachine (Symbol units fields)

abbrev State (position : ℕ) := Sum (Fin (position + 1)) (Symbol × Fin 9)

/-- Scan to the selected field, delete units by carrying its prefix right,
and return to the header when the field is empty. -/
def machine (position : ℕ) : Turing.TM0.Machine Symbol (State position) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else if symbol = 2 then some (.inr (0, 0), .write 0)
    else if symbol = 1 then some (.inr (0, 7), .move .left) else none
  | .inr (carried, phase) =>
    match phase.val with
    | 0 => some (.inr (0, 1), .move .left)
    | 1 => if symbol = 0 then some (.inr (0, 6), .move .right)
        else some (.inr (symbol, 2), .write 0)
    | 2 => some (.inr (carried, 3), .move .right)
    | 3 => some (.inr (carried, 4), .write carried)
    | 4 => some (.inr (carried, 5), .move .left)
    | 5 => some (.inr (0, 1), .move .left)
    | 6 => some (.inl (Fin.last position), .move .right)
    | 7 => if symbol = 0 then some (.inr (0, 8), .move .right)
        else some (.inr (carried, 7), .move .left)
    | _ => none

variable {position : ℕ}

private theorem carry (cells : List Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position) (5 * cells.length)
      (Tape.configuration (.inr (0, 1)) cells.tail (cells.headD 0 :: 0 :: tail))
      (Tape.configuration (.inr (0, 1)) [] (0 :: 0 :: (cells.reverse ++ tail))) := by
  induction cells generalizing tail with
  | nil => exact .zero _
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have write := Tape.write (machine := machine position) (state := .inr (0, 1))
      (nextState := .inr (symbol, 2)) cells (0 :: tail) symbol 0 (by simp [machine, distinct])
    have right := Tape.move_right (machine := machine position) (state := .inr (symbol, 2))
      (nextState := .inr (symbol, 3)) cells (0 :: tail) 0 (by rfl)
    have copy := Tape.write (machine := machine position) (state := .inr (symbol, 3))
      (nextState := .inr (symbol, 4)) (0 :: cells) tail 0 symbol (by rfl)
    have left := Tape.move_left (machine := machine position) (state := .inr (symbol, 4))
      (nextState := .inr (symbol, 5)) cells tail 0 symbol (by rfl)
    have next := Tape.move_left_headD (machine := machine position) (state := .inr (symbol, 5))
      (nextState := .inr (0, 1)) cells (symbol :: tail) 0 (by rfl)
    have rest := hypothesis (symbol :: tail) (by intro current member; exact valid current (by simp [member]))
    have trace := Tape.Steps.next write (Tape.Steps.next right (Tape.Steps.next copy
      (Tape.Steps.next left (Tape.Steps.next next rest))))
    convert trace using 1 <;> simp [List.reverse_cons, List.append_assoc]

private theorem shift (cells : List Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position) (5 * cells.length + 3)
      (Tape.configuration (.inr (0, 0)) cells (0 :: tail))
      (Tape.configuration (.inl (Fin.last position)) [] (cells.reverse ++ tail)) := by
  have enter := Tape.move_left_headD (machine := machine position) (state := .inr (0, 0))
    (nextState := .inr (0, 1)) cells tail 0 (by rfl)
  have moved := carry (position := position) cells tail valid
  have first := Tape.move_right (machine := machine position) (state := .inr (0, 1))
    (nextState := .inr (0, 6)) [] (0 :: (cells.reverse ++ tail)) 0 (by rfl)
  have second := Tape.move_right (machine := machine position) (state := .inr (0, 6))
    (nextState := .inl (Fin.last position)) [0] (cells.reverse ++ tail) 0 (by rfl)
  have padding : Tape.configuration (.inl (Fin.last position) : State position) [0, 0] (cells.reverse ++ tail) =
      Tape.configuration (.inl (Fin.last position) : State position) [] (cells.reverse ++ tail) := by
    calc
      _ = Tape.configuration (.inl (Fin.last position) : State position) [0] (cells.reverse ++ tail) :=
        Tape.configuration_append_blank (Symbol := Symbol) _ [0] _
      _ = _ := Tape.configuration_append_blank (Symbol := Symbol) _ [] _
  rw [padding] at second
  have trace := Tape.Steps.next enter (moved.trans (Tape.Steps.next first (Tape.Steps.next second (.zero _))))
  convert trace using 1

private theorem return_header (cells : List Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine position) (cells.length + 1)
      (Tape.configuration (.inr (0, 7)) cells.tail (cells.headD 0 :: tail))
      (Tape.configuration (.inr (0, 8)) [] (cells.reverse ++ tail)) := by
  induction cells generalizing tail with
  | nil =>
    have move := Tape.move_right (machine := machine position) (state := .inr (0, 7))
      (nextState := .inr (0, 8)) [] tail 0 (by rfl)
    have padding : Tape.configuration (.inr (0, 8) : State position) [0] tail =
        Tape.configuration (.inr (0, 8) : State position) [] tail :=
      Tape.configuration_append_blank (Symbol := Symbol) _ [] _
    rw [padding] at move
    exact .next move (.zero _)
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have move := Tape.move_left_headD (machine := machine position) (state := .inr (0, 7))
      (nextState := .inr (0, 7)) cells tail symbol (by simp [machine, distinct])
    have rest := hypothesis (symbol :: tail) (by intro current member; exact valid current (by simp [member]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Tape.Steps.next move rest

private theorem skip (values : List ℕ) (remaining : Fin (position + 1))
    (count : remaining.val = values.length) (left tail : List Symbol) :
    Tape.Steps (machine position) (fields values).length
      (Tape.configuration (.inl remaining) left (fields values ++ tail))
      (Tape.configuration (.inl 0) ((fields values).reverse ++ left) tail) := by
  induction values generalizing remaining left with
  | nil =>
    have equality : remaining = 0 := Fin.ext count
    subst remaining
    simp only [fields, List.flatMap_nil, List.nil_append, List.reverse_nil]
    exact .zero _
  | cons value values hypothesis =>
    have positive : remaining.val > 0 := by simp at count; omega
    let next : Fin (position + 1) := ⟨remaining.val - 1, by omega⟩
    have scan := Tape.scan_right (machine := machine position) (state := .inl remaining)
      (units value) left (1 :: (fields values ++ tail)) (by
        intro symbol member
        have equality := List.eq_of_mem_replicate member
        subst symbol; simp [machine, positive])
    have advance := Tape.move_right (machine := machine position) (state := .inl remaining)
      (nextState := .inl next) ((units value).reverse ++ left) (fields values ++ tail) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by dsimp [next]; simp at count; omega)
      (1 :: ((units value).reverse ++ left))
    have trace := scan.trans (Tape.Steps.next advance rest)
    simpa [UnaryMachine.fields_cons, List.reverse_append, List.append_assoc] using trace

/-- Reset the selected field, preserving preceding fields and the entire suffix.
The exact transition bound is polynomial in the old value and prefix length. -/
theorem realizes (prior : List ℕ) (value : ℕ) (tail : List Symbol) :
    Tape.Steps (machine prior.length)
      (value * (6 * (fields prior).length + 4) + 2 * (fields prior).length + 2)
      (Tape.configuration (.inl (Fin.last prior.length)) [] (fields (prior ++ [value]) ++ tail))
      (Tape.configuration (.inr (0, 8)) [] (fields (prior ++ [0]) ++ tail)) := by
  have valid : ∀ symbol ∈ (fields prior).reverse, symbol ≠ 0 := by
    intro symbol member
    rcases UnaryMachine.fields_symbols prior symbol (List.mem_reverse.mp member) with equality | equality <;>
      subst symbol <;> decide
  induction value with
  | zero =>
    have scanned := skip prior (Fin.last prior.length) (by simp) [] (1 :: tail)
    simp only [List.append_nil] at scanned
    have enter := Tape.move_left_headD (machine := machine prior.length) (state := .inl 0)
      (nextState := .inr (0, 7)) (fields prior).reverse tail 1 (by rfl)
    have returned := return_header (position := prior.length) (fields prior).reverse (1 :: tail) valid
    have trace := scanned.trans (Tape.Steps.next enter returned)
    convert trace using 1 <;> simp [fields, units, List.flatMap_append, List.append_assoc]
    omega
  | succ value hypothesis =>
    have scanned := skip prior (Fin.last prior.length) (by simp) [] (units (value + 1) ++ 1 :: tail)
    simp only [List.append_nil] at scanned
    have erase := Tape.write (machine := machine prior.length) (state := .inl 0)
      (nextState := .inr (0, 0)) (fields prior).reverse (units value ++ 1 :: tail) 2 0 (by rfl)
    have shifted := shift (position := prior.length) (fields prior).reverse (units value ++ 1 :: tail) valid
    have shifted' : Tape.Steps (machine prior.length) (5 * (fields prior).length + 3)
        (Tape.configuration (.inr (0, 0)) (fields prior).reverse (0 :: (units value ++ 1 :: tail)))
        (Tape.configuration (.inl (Fin.last prior.length)) [] (fields (prior ++ [value]) ++ tail)) := by
      simpa [fields, List.flatMap_append, List.append_assoc] using shifted
    simp only [units, List.replicate_succ, List.cons_append] at scanned erase
    have trace := scanned.trans (Tape.Steps.next erase (shifted'.trans hypothesis))
    convert trace using 1 <;> simp [fields, units, List.flatMap_append, List.append_assoc, List.replicate_succ]
    ring

@[simp] theorem halt (symbol : Symbol) : machine position (.inr (0, 8)) symbol = none := rfl

end Polytime.HeaderResetMachine
