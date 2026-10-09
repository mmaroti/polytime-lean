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

/-! # Incrementing runtime unary header fields

Insert one unit before a selected field, shifting only its preceding header
into one free cell on the left. The selected field's old cells and the entire
following frame stay in place. The field position is fixed in the controller.
-/

namespace Polytime.HeaderIncrementMachine

open UnaryMachine (Symbol units fields)

abbrev State (position : ℕ) := Sum (Fin (position + 1)) (Symbol × Fin 3)

/-- Skip the fixed number of fields, then carry their symbols one cell left.
The second component records write, move-left, or halt. -/
def machine (position : ℕ) : Turing.TM0.Machine Symbol (State position) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else some (.inr (2, 0), .move .left)
  | .inr (carried, phase) =>
    match phase.val with
    | 0 => if symbol = 0 then some (.inr (0, 2), .write carried)
        else some (.inr (symbol, 1), .write carried)
    | 1 => some (.inr (carried, 0), .move .left)
    | _ => none

variable {position : ℕ}

private theorem shift (prior : List Symbol) (carried : Symbol) (tail : List Symbol)
    (valid : ∀ symbol ∈ prior, symbol ≠ 0) :
    Tape.Steps (machine position) (2 * prior.length + 1)
      (Tape.configuration (.inr (carried, 0)) prior.tail (prior.headD 0 :: tail))
      (Tape.configuration (.inr (0, 2)) [] (prior.reverse ++ carried :: tail)) := by
  induction prior generalizing carried tail with
  | nil =>
    exact Tape.Steps.next (Tape.write (machine := machine position)
      (state := .inr (carried, 0)) (nextState := .inr (0, 2)) [] tail 0 carried (by rfl)) (.zero _)
  | cons symbol prior hypothesis =>
    have distinct := valid symbol (by simp)
    have write := Tape.write (machine := machine position) (state := .inr (carried, 0))
      (nextState := .inr (symbol, 1)) prior tail symbol carried (by simp [machine, distinct])
    have move : Turing.TM0.step (machine position)
        (Tape.configuration (.inr (symbol, 1)) prior (carried :: tail)) =
        some (Tape.configuration (.inr (symbol, 0)) prior.tail (prior.headD 0 :: carried :: tail)) := by
      cases prior with
      | nil => exact Tape.move_left_empty _ (by intro current; rfl)
      | cons first rest => exact Tape.move_left_list _ _ first (by intro current; rfl)
    have rest := hypothesis symbol (carried :: tail) (by
      intro current member; exact valid current (by simp [member]))
    have trace := Tape.Steps.next write (Tape.Steps.next move rest)
    convert trace using 1 <;> simp [List.reverse_cons, List.append_assoc]

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
        subst symbol
        simp [machine, positive])
    have advance := Tape.move_right (machine := machine position) (state := .inl remaining)
      (nextState := .inl next) ((units value).reverse ++ left) (fields values ++ tail) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by dsimp [next]; simp at count; omega)
      (1 :: ((units value).reverse ++ left))
    have trace := scan.trans (Tape.Steps.next advance rest)
    simpa [UnaryMachine.fields_cons, List.reverse_append, List.append_assoc] using trace

/-- Increment the field after `prior`, with an exact linear transition count.
Blank left storage is the explicit entry requirement. All following values,
including scalar windows, counters, and matrix bits, are preserved. -/
theorem realizes (prior : List ℕ) (value : ℕ) (tail : List Symbol) :
    Tape.Steps (machine prior.length) (3 * (fields prior).length + 2)
      (Tape.configuration (.inl (Fin.last prior.length)) [] (fields (prior ++ [value]) ++ tail))
      (Tape.configuration (.inr (0, 2)) [] (fields (prior ++ [value + 1]) ++ tail)) := by
  let suffix := units value ++ 1 :: tail
  have skipped := skip prior (Fin.last prior.length) (by simp) [] suffix
  simp only [List.append_nil] at skipped
  have enter : Turing.TM0.step (machine prior.length)
      (Tape.configuration (.inl 0) (fields prior).reverse suffix) =
      some (Tape.configuration (.inr (2, 0)) (fields prior).reverse.tail
        ((fields prior).reverse.headD 0 :: suffix)) := by
    cases equation : (fields prior).reverse with
    | nil => exact Tape.move_left_empty _ (by intro symbol; simp [machine])
    | cons symbol rest => exact Tape.move_left_list _ _ symbol (by intro current; simp [machine])
  have shifted := shift (position := prior.length) (fields prior).reverse 2 suffix (by
    intro symbol member
    rcases UnaryMachine.fields_symbols prior symbol (List.mem_reverse.mp member) with equality | equality <;>
      subst symbol <;> decide)
  have trace := skipped.trans (Tape.Steps.next enter shifted)
  convert trace using 1 <;>
    simp [suffix, fields, units, List.flatMap_append, List.append_assoc, List.replicate_succ]
  omega

@[simp] theorem halt (symbol : Symbol) : machine position (.inr (0, 2)) symbol = none := rfl

end Polytime.HeaderIncrementMachine
