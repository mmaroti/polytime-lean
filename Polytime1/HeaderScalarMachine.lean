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

import Polytime1.BlockLookupMachine
import Polytime1.UnaryMachine

/-! # Copying a scalar before a runtime header

Read the fixed-width scalar following the header into finite controller states,
return over the preserved header, and emit a copy into blank cells to its left.
This adapts a matrix-lookup result to the row-scaling coefficient input.
-/

namespace Polytime1.HeaderScalarMachine

open UnaryMachine (Symbol fields units)
open TupleMachine (word)

abbrev State (count width : ℕ) := Sum (Fin (count + 1))
  (Sum (FiniteTableMachine.State width width) ((Fin width → Bool) × Fin 2))

def machine (count width : ℕ) : Turing.TM0.Machine Symbol (State count width) := fun state symbol =>
  match state with
  | .inl remaining =>
    if remaining.val > 0 then
      some (.inl (if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining), .move .right)
    else some (.inr (.inl (.read 0 (fun _ => false))), .write symbol)
  | .inr (.inl state) =>
    match state with
    | .read position bits =>
      if position.val < width then
        (FiniteTableMachine.machine id state symbol).map fun (next, action) => (.inr (.inl next), action)
      else some (.inr (.inr (bits, 0)), .move .left)
    | _ => (FiniteTableMachine.machine id state symbol).map fun (next, action) => (.inr (.inl next), action)
  | .inr (.inr (bits, phase)) =>
    if phase = 0 then
      if symbol = 0 then some (.inr (.inr (bits, 1)), .move .right)
      else some (.inr (.inr (bits, 0)), .move .left)
    else some (.inr (.inl (.emit (Fin.last width) bits)), .write symbol)

variable {count width : ℕ}

private theorem skip (values : List ℕ) (remaining : Fin (count + 1))
    (length : remaining.val = values.length) (left tail : List Symbol) :
    Tape.Steps (machine count width) (fields values).length
      (Tape.configuration (.inl remaining) left (fields values ++ tail))
      (Tape.configuration (.inl 0) ((fields values).reverse ++ left) tail) := by
  induction values generalizing remaining left with
  | nil =>
    have equality : remaining = 0 := Fin.ext length
    subst remaining
    simp only [fields, List.flatMap_nil, List.nil_append, List.reverse_nil]
    exact .zero _
  | cons value values hypothesis =>
    have positive : remaining.val > 0 := by simp at length; omega
    let next : Fin (count + 1) := ⟨remaining.val - 1, by omega⟩
    have scan := Tape.scan_right (machine := machine count width) (state := .inl remaining)
      (units value) left (1 :: (fields values ++ tail)) (by
        intro symbol member
        have equality := List.eq_of_mem_replicate member
        subst symbol; simp [machine, positive])
    have advance := Tape.move_right (machine := machine count width) (state := .inl remaining)
      (nextState := .inl next) ((units value).reverse ++ left) (fields values ++ tail) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by dsimp [next]; simp at length; omega)
      (1 :: ((units value).reverse ++ left))
    have trace := scan.trans (Tape.Steps.next advance rest)
    simpa [UnaryMachine.fields_cons, List.reverse_append, List.append_assoc] using trace

private theorem reads (bits : Fin width → Bool) (left tail : List Symbol) :
    Tape.Steps (machine count width) width
      (Tape.configuration (.inr (.inl (.read 0 (fun _ => false)))) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration (.inr (.inl (.read (Fin.last width) bits)))
        ((word (List.ofFn bits)).reverse ++ left) tail) := by
  have trace := FiniteTableMachine.reads (id : (Fin width → Bool) → (Fin width → Bool)) bits left tail
  apply (trace.rename_until (fun state => (.inr (.inl state) : State count width)) BlockLookupMachine.reading
    (fun state symbol next => BlockLookupMachine.reading_predecessor state next symbol)
    (targetMachine := machine count width) ?_ trivial).2
  intro state symbol next action allowed nextAllowed command
  cases state with
  | read position stored =>
    by_cases valid : position.val < width
    · simp [machine, valid, command]
    · simp only [FiniteTableMachine.machine, valid, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨rfl, _⟩ := command
      exact nextAllowed.elim
  | rewind | emit | write | halt => exact allowed.elim

private theorem back (cells : List Symbol) (bits : Fin width → Bool) (tail : List Symbol)
    (valid : ∀ symbol ∈ cells, symbol ≠ 0) :
    Tape.Steps (machine count width) (cells.length + 1)
      (Tape.configuration (.inr (.inr (bits, 0))) cells.tail (cells.headD 0 :: tail))
      (Tape.configuration (.inr (.inr (bits, 1))) [] (cells.reverse ++ tail)) := by
  induction cells generalizing tail with
  | nil =>
    have move := Tape.move_right (machine := machine count width) (state := .inr (.inr (bits, 0)))
      (nextState := .inr (.inr (bits, 1))) [] tail 0 (by rfl)
    have padding : Tape.configuration (.inr (.inr (bits, 1)) : State count width) [0] tail =
        Tape.configuration (.inr (.inr (bits, 1)) : State count width) [] tail :=
      Tape.configuration_append_blank (Symbol := Symbol) _ [] _
    rw [padding] at move
    exact .next move (.zero _)
  | cons symbol cells hypothesis =>
    have distinct := valid symbol (by simp)
    have move := Tape.move_left_headD (machine := machine count width) (state := .inr (.inr (bits, 0)))
      (nextState := .inr (.inr (bits, 0))) cells tail symbol (by simp [machine, distinct])
    have rest := hypothesis (symbol :: tail) (by intro current member; exact valid current (by simp [member]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Tape.Steps.next move rest

private def emitting : FiniteTableMachine.State width width → Prop
  | .emit _ _ | .write _ _ | .halt => True
  | _ => False

private theorem emits (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine count width) (2 * width + 1)
      (Tape.configuration (.inr (.inl (.emit (Fin.last width) bits))) [] tail)
      (Tape.configuration (.inr (.inl .halt)) [] (word (List.ofFn bits) ++ tail)) := by
  have trace := FiniteTableMachine.emit_loop (id : (Fin width → Bool) → (Fin width → Bool)) bits
    (List.replicate width 0) [] tail (Fin.last width) (by simp)
  have blanks (length : ℕ) : Tape.configuration (.emit (Fin.last width) bits : FiniteTableMachine.State width width)
      (List.replicate length (0 : Symbol)) tail = Tape.configuration (.emit (Fin.last width) bits) [] tail := by
    induction length with
    | zero => rfl
    | succ length hypothesis =>
      rw [List.replicate_succ']
      have padding := Tape.configuration_append_blank (Symbol := Symbol)
        (.emit (Fin.last width) bits : FiniteTableMachine.State width width) (List.replicate length 0) tail
      change Tape.configuration (FiniteTableMachine.State.emit (Fin.last width) bits)
        (List.replicate length 0 ++ [0]) tail = _ at padding
      rw [padding, hypothesis]
  simp only [List.append_nil] at trace
  rw [blanks] at trace
  have lifted := trace.rename_from (fun state => (.inr (.inl state) : State count width)) emitting
    (targetMachine := machine count width) (by
      intro state symbol next action allowed command
      cases state with
      | read | rewind => exact allowed.elim
      | emit remaining result =>
        by_cases positive : remaining.val > 0 <;>
          simp [FiniteTableMachine.machine, positive, Option.some.injEq, Prod.mk.injEq] at command <;>
          obtain ⟨rfl, _⟩ := command <;> trivial
      | write =>
        simp only [FiniteTableMachine.machine, Option.some.injEq, Prod.mk.injEq] at command
        obtain ⟨rfl, _⟩ := command
        trivial
      | halt => simp [FiniteTableMachine.machine] at command) (by
        intro state symbol next action allowed command
        cases state with
        | read | rewind => exact allowed.elim
        | emit | write | halt => simp [machine, command]) trivial
  simpa [Tape.configuration, List.take_of_length_le] using lifted

/-- Prepend a copy of the scalar following the header, preserving that scalar,
the header, and the entire suffix. The width and field count fix the controller. -/
theorem realizes (values : List ℕ) (bits : Fin width → Bool) (tail : List Symbol) :
    Tape.Steps (machine values.length width) (2 * (fields values).length + 4 * width + 5)
      (Tape.configuration (.inl (Fin.last values.length)) [] (fields values ++ word (List.ofFn bits) ++ tail))
      (Tape.configuration (.inr (.inl .halt)) []
        (word (List.ofFn bits) ++ fields values ++ word (List.ofFn bits) ++ tail)) := by
  let original := fields values ++ word (List.ofFn bits)
  have skipped := skip (width := width) values (Fin.last values.length) (by simp) [] (word (List.ofFn bits) ++ tail)
  simp only [List.append_nil] at skipped
  have enter := Tape.stay (machine := machine values.length width) (state := .inl 0)
    (nextState := .inr (.inl (.read 0 (fun _ => false)))) (fields values).reverse (word (List.ofFn bits) ++ tail)
    (by intro symbol; simp [machine])
  have read := reads (count := values.length) bits (fields values).reverse tail
  have reverse' : Turing.TM0.step (machine values.length width)
      (Tape.configuration (.inr (.inl (.read (Fin.last width) bits))) original.reverse tail) =
      some (Tape.configuration (.inr (.inr (bits, 0))) original.reverse.tail (original.reverse.headD 0 :: tail)) := by
    cases tail with
    | nil =>
      simp only [Turing.TM0.step, Tape.configuration, machine, Fin.val_last, lt_self_iff_false,
        ↓reduceIte, Option.map_some, Turing.Tape.move_left_mk',
        Turing.ListBlank.tail_mk, Turing.ListBlank.head_mk, Turing.ListBlank.cons_mk,
        List.headI, List.headD_eq_head?_getD]
      cases original.reverse <;> rfl
    | cons symbol rest =>
      exact Tape.move_left_headD original.reverse rest symbol (by simp [machine])
  have returned := back (count := values.length) original.reverse bits tail (by
    intro symbol member
    have member := List.mem_reverse.mp member
    simp only [original, List.mem_append] at member
    rcases member with member | member
    · rcases UnaryMachine.fields_symbols values symbol member with equality | equality <;> subst symbol <;> decide
    · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide)
  have emitEntry := Tape.stay (machine := machine values.length width) (state := .inr (.inr (bits, 1)))
    (nextState := .inr (.inl (.emit (Fin.last width) bits))) [] (original ++ tail)
    (by intro symbol; simp [machine])
  have emitted := emits (count := values.length) bits (original ++ tail)
  simp only [List.reverse_reverse] at returned
  simp only [← List.reverse_append] at read
  have trace := skipped.trans (Tape.Steps.next enter (read.trans
    (Tape.Steps.next reverse' (returned.trans (Tape.Steps.next emitEntry emitted)))))
  convert trace using 1 <;> simp [original, word, List.append_assoc]
  omega

@[simp] theorem halt (symbol : Symbol) : machine count width (.inr (.inl .halt)) symbol = none := rfl

end Polytime1.HeaderScalarMachine
