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

/-! # A restoring guard for two runtime unary header counters

Under the loop invariant `index ≤ limit`, match their unary units using
temporary markers, restore both fields, and place `index < limit` immediately
before the original header. All following storage is preserved.
-/

namespace Polytime.HeaderGuardMachine

open UnaryMachine (Symbol units fields)
open TupleMachine (data)

abbrev State (position : ℕ) := Fin (position + 1) × Bool × Fin 15

/-- The fixed position skips preceding header fields. Markers 3 and 4 pair
units, and marker 5 identifies the free result cell before the header. -/
def machine (position : ℕ) : Turing.TM0.Machine Symbol (State position) := fun (remaining, result, phase) symbol =>
  match phase.val with
  | 0 => some ((remaining, result, 1), .move .left)
  | 1 => some ((remaining, result, 2), .write 5)
  | 2 => some ((remaining, result, 3), .move .right)
  | 3 => if remaining.val > 0 then
      some ((if symbol = 1 then ⟨remaining.val - 1, by omega⟩ else remaining, result, 3), .move .right)
      else some ((remaining, result, 4), .write symbol)
  | 4 => if symbol = 2 then some ((remaining, result, 5), .write 3)
      else if symbol = 1 then some ((remaining, result, 9), .move .right) else none
  | 5 => some ((remaining, result, 6), .move .right)
  | 6 => if symbol = 1 then some ((remaining, result, 7), .move .right)
      else some ((remaining, result, 6), .move .right)
  | 7 => if symbol = 4 then some ((remaining, result, 7), .move .right)
      else if symbol = 2 then some ((remaining, result, 8), .write 4) else none
  | 8 => if symbol = 3 then some ((remaining, result, 4), .move .right)
      else some ((remaining, result, 8), .move .left)
  | 9 => if symbol = 4 then some ((remaining, result, 9), .move .right)
      else some ((remaining, decide (symbol = 2), 10), .move .left)
  | 10 => if symbol = 4 then some ((remaining, result, 11), .write 2)
      else if symbol = 1 then some ((remaining, result, 12), .move .left) else none
  | 11 => some ((remaining, result, 10), .move .left)
  | 12 => if symbol = 3 then some ((remaining, result, 13), .write 2)
      else if symbol = 5 then some ((0, false, 14), .write (data result))
      else some ((remaining, result, 12), .move .left)
  | 13 => some ((remaining, result, 12), .move .left)
  | _ => none

variable {position : ℕ}

private theorem repeat_rotate (symbol : Symbol) (count : ℕ) (tail : List Symbol) :
    symbol :: (List.replicate count symbol ++ tail) = List.replicate count symbol ++ symbol :: tail := by
  simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
    congrArg (fun cells : List Symbol => cells ++ tail)
      ((List.replicate_succ (n := count) (a := symbol)).symm.trans
        (List.replicate_succ' (n := count) (a := symbol)))

private theorem pair (first second processed : ℕ) (left tail : List Symbol) :
    Tape.Steps (machine position) (2 * first + 2 * processed + 7)
      (Tape.configuration (0, false, 4) (List.replicate processed 3 ++ left)
        (units (first + 1) ++ 1 :: (List.replicate processed 4 ++ units (second + 1) ++ 1 :: tail)))
      (Tape.configuration (0, false, 4) (List.replicate (processed + 1) 3 ++ left)
        (units first ++ 1 :: (List.replicate (processed + 1) 4 ++ units second ++ 1 :: tail))) := by
  let next := units first ++ 1 :: (List.replicate processed 4 ++ units (second + 1) ++ 1 :: tail)
  have mark := Tape.write (machine := machine position) (state := (0, false, 4))
    (nextState := (0, false, 5)) (List.replicate processed 3 ++ left) next 2 3 (by rfl)
  have enter := Tape.move_right (machine := machine position) (state := (0, false, 5))
    (nextState := (0, false, 6)) (List.replicate processed 3 ++ left) next 3 (by rfl)
  have firstScan := Tape.scan_right (machine := machine position) (state := (0, false, 6))
    (units first) (3 :: (List.replicate processed 3 ++ left))
    (1 :: (List.replicate processed 4 ++ units (second + 1) ++ 1 :: tail)) (by
      intro symbol member
      have equality := List.eq_of_mem_replicate member
      subst symbol; rfl)
  have cross := Tape.move_right (machine := machine position) (state := (0, false, 6))
    (nextState := (0, false, 7)) (units first ++ 3 :: (List.replicate processed 3 ++ left))
    (List.replicate processed 4 ++ units (second + 1) ++ 1 :: tail) 1 (by rfl)
  have secondScan := Tape.scan_right (machine := machine position) (state := (0, false, 7))
    (List.replicate processed 4) (1 :: (units first ++ 3 :: (List.replicate processed 3 ++ left)))
    (units (second + 1) ++ 1 :: tail) (by
      intro symbol member
      have equality := List.eq_of_mem_replicate member
      subst symbol; rfl)
  let gap := List.replicate processed (4 : Symbol) ++ 1 :: units first
  have secondMark := Tape.write (machine := machine position) (state := (0, false, 7))
    (nextState := (0, false, 8)) (gap ++ 3 :: (List.replicate processed 3 ++ left))
    (units second ++ 1 :: tail) 2 4 (by rfl)
  have back := Tape.scan_left (machine := machine position) (state := (0, false, 8))
    gap (List.replicate processed 3 ++ left) (units second ++ 1 :: tail) 3 4 (by
      intro symbol member
      have distinct : symbol ≠ (3 : Symbol) := by
        simp only [gap, List.mem_cons, List.mem_append, units, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ | equality | ⟨_, equality⟩ <;> subst symbol <;> decide
      simp [machine, distinct])
  have advance := Tape.move_right (machine := machine position) (state := (0, false, 8))
    (nextState := (0, false, 4)) (List.replicate processed 3 ++ left)
    (gap.reverse ++ 4 :: (units second ++ 1 :: tail)) 3 (by rfl)
  simp only [UnaryMachine.units_reverse, List.reverse_replicate] at firstScan secondScan
  simp only [next, gap, units, List.replicate_succ, List.cons_append, List.append_assoc]
    at mark enter firstScan cross secondScan secondMark back advance
  have trace := Tape.Steps.next mark (Tape.Steps.next enter
    (firstScan.trans (Tape.Steps.next cross (secondScan.trans
      (Tape.Steps.next secondMark (back.trans (Tape.Steps.next advance (.zero _))))))))
  convert trace using 1 <;>
    simp [units, List.reverse_append, List.reverse_cons, List.append_assoc, List.replicate_succ]
  · omega
  · simp only [← repeat_rotate]

private theorem pairs (count processed extra : ℕ) (left tail : List Symbol) :
    Tape.Steps (machine position) (count * (2 * (processed + count) + 5))
      (Tape.configuration (0, false, 4) (List.replicate processed 3 ++ left)
        (units count ++ 1 :: (List.replicate processed 4 ++ units (count + extra) ++ 1 :: tail)))
      (Tape.configuration (0, false, 4) (List.replicate (processed + count) 3 ++ left)
        (1 :: (List.replicate (processed + count) 4 ++ units extra ++ 1 :: tail))) := by
  induction count generalizing processed with
  | zero => simp [units]; exact .zero _
  | succ count hypothesis =>
    have first := pair (position := position) count (count + extra) processed left tail
    have rest := hypothesis (processed + 1)
    have trace := first.trans rest
    convert trace using 1 <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    ring

private theorem restore_second (count : ℕ) (result : Bool) (left right : List Symbol) :
    let cells := List.replicate count (4 : Symbol) ++ 1 :: left
    Tape.Steps (machine position) (2 * count + 1)
      (Tape.configuration (0, result, 10) cells.tail (cells.headD 0 :: right))
      (Tape.configuration (0, result, 12) left.tail (left.headD 0 :: 1 :: (units count ++ right))) := by
  dsimp only
  induction count generalizing right with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, List.tail_cons, List.headD_cons,
      units, List.nil_append]
    have move : Turing.TM0.step (machine position) (Tape.configuration (0, result, 10) left (1 :: right)) =
        some (Tape.configuration (0, result, 12) left.tail (left.headD 0 :: 1 :: right)) := by
      exact Tape.move_left_headD left right 1 (by rfl)
    exact .next move (.zero _)
  | succ count hypothesis =>
    let cells := List.replicate count (4 : Symbol) ++ 1 :: left
    have write := Tape.write (machine := machine position) (state := (0, result, 10))
      (nextState := (0, result, 11)) cells right 4 2 (by rfl)
    have move : Turing.TM0.step (machine position) (Tape.configuration (0, result, 11) cells (2 :: right)) =
        some (Tape.configuration (0, result, 10) cells.tail (cells.headD 0 :: 2 :: right)) := by
      cases cells with
      | nil => exact Tape.move_left_empty _ (by intro symbol; rfl)
      | cons symbol rest => exact Tape.move_left_list _ _ symbol (by intro current; rfl)
    have trace := Tape.Steps.next write (Tape.Steps.next move (hypothesis (2 :: right)))
    convert trace using 1 <;> simp [cells, units, List.replicate_succ]
    simp only [← repeat_rotate]

private theorem restore_first (count : ℕ) (result : Bool) (prior right : List Symbol) :
    let cells := List.replicate count (3 : Symbol) ++ prior
    Tape.Steps (machine position) (2 * count)
      (Tape.configuration (0, result, 12) cells.tail (cells.headD 0 :: right))
      (Tape.configuration (0, result, 12) prior.tail (prior.headD 0 :: (units count ++ right))) := by
  dsimp only
  induction count generalizing right with
  | zero => simp [units]; exact .zero _
  | succ count hypothesis =>
    let cells := List.replicate count (3 : Symbol) ++ prior
    have write := Tape.write (machine := machine position) (state := (0, result, 12))
      (nextState := (0, result, 13)) cells right 3 2 (by rfl)
    have move : Turing.TM0.step (machine position) (Tape.configuration (0, result, 13) cells (2 :: right)) =
        some (Tape.configuration (0, result, 12) cells.tail (cells.headD 0 :: 2 :: right)) := by
      cases cells with
      | nil => exact Tape.move_left_empty _ (by intro symbol; rfl)
      | cons symbol rest => exact Tape.move_left_list _ _ symbol (by intro current; rfl)
    have trace := Tape.Steps.next write (Tape.Steps.next move (hypothesis (2 :: right)))
    convert trace using 1 <;> simp [cells, units, List.replicate_succ]
    simp only [← repeat_rotate]

private theorem retreat (prior : List Symbol) (result : Bool) (right caller : List Symbol)
    (valid : ∀ symbol ∈ prior, symbol ≠ 3 ∧ symbol ≠ 5) :
    let cells := prior ++ 5 :: caller
    Tape.Steps (machine position) (prior.length + 1)
      (Tape.configuration (0, result, 12) cells.tail (cells.headD 0 :: right))
      (Tape.configuration (0, false, 14) caller (data result :: (prior.reverse ++ right))) := by
  dsimp only
  induction prior generalizing right with
  | nil => exact .next (Tape.write caller right 5 (data result) (by rfl)) (.zero _)
  | cons symbol prior hypothesis =>
    have safe := valid symbol (by simp)
    let cells := prior ++ 5 :: caller
    have move : Turing.TM0.step (machine position) (Tape.configuration (0, result, 12) cells (symbol :: right)) =
        some (Tape.configuration (0, result, 12) cells.tail (cells.headD 0 :: symbol :: right)) := by
      exact Tape.move_left_headD cells right symbol (by simp [machine, safe])
    have rest := hypothesis (symbol :: right) (by intro current member; exact valid current (by simp [member]))
    simpa [cells, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Tape.Steps.next move rest

private theorem finish (prior : List Symbol) (count extra : ℕ) (tail caller : List Symbol)
    (valid : ∀ symbol ∈ prior, symbol ≠ 3 ∧ symbol ≠ 5) :
    Tape.Steps (machine position) (5 * count + prior.length + 4)
      (Tape.configuration (0, false, 4) (List.replicate count 3 ++ (prior.reverse ++ 5 :: caller))
        (1 :: (List.replicate count 4 ++ units extra ++ 1 :: tail)))
      (Tape.configuration (0, false, 14) caller
        (data (decide (0 < extra)) :: (prior ++ fields [count, count + extra] ++ tail))) := by
  let retained := prior.reverse ++ 5 :: caller
  let right := units extra ++ 1 :: tail
  let cells := List.replicate count (4 : Symbol) ++ 1 :: (List.replicate count 3 ++ retained)
  have cross := Tape.move_right (machine := machine position) (state := (0, false, 4))
    (nextState := (0, false, 9)) (List.replicate count 3 ++ retained)
    (List.replicate count 4 ++ right) 1 (by rfl)
  have scan := Tape.scan_right (machine := machine position) (state := (0, false, 9))
    (List.replicate count 4) (1 :: (List.replicate count 3 ++ retained)) right (by
      intro symbol member
      have equality := List.eq_of_mem_replicate member
      subst symbol; rfl)
  have decision : Turing.TM0.step (machine position) (Tape.configuration (0, false, 9) cells right) =
      some (Tape.configuration (0, decide (0 < extra), 10) cells.tail (cells.headD 0 :: right)) := by
    cases extra with
    | zero => exact Tape.move_left_headD cells tail 1 (by rfl)
    | succ extra =>
      simpa [right, units, List.replicate_succ] using
        (Tape.move_left_headD (machine := machine position) (state := (0, false, 9))
          (nextState := (0, true, 10)) cells (units extra ++ 1 :: tail) 2 (by rfl))
  have second := restore_second (position := position) count (decide (0 < extra))
    (List.replicate count 3 ++ retained) right
  have first := restore_first (position := position) count (decide (0 < extra)) retained
    (1 :: (units count ++ right))
  have back := retreat (position := position) prior.reverse (decide (0 < extra))
    (units count ++ 1 :: (units count ++ right)) caller (by
      intro symbol member; exact valid symbol (List.mem_reverse.mp member))
  simp only [List.reverse_replicate] at scan
  have trace := Tape.Steps.next cross (scan.trans (Tape.Steps.next decision
    (second.trans (first.trans back))))
  convert trace using 1 <;>
    simp [retained, right, fields, UnaryMachine.units_add, List.append_assoc]
  omega

private theorem skip (values : List ℕ) (remaining : Fin (position + 1))
    (count : remaining.val = values.length) (left tail : List Symbol) :
    Tape.Steps (machine position) (fields values).length
      (Tape.configuration (remaining, false, 3) left (fields values ++ tail))
      (Tape.configuration (0, false, 3) ((fields values).reverse ++ left) tail) := by
  induction values generalizing remaining left with
  | nil =>
    have equality : remaining = 0 := Fin.ext count
    subst remaining
    simp only [fields, List.flatMap_nil, List.nil_append, List.reverse_nil]
    exact .zero _
  | cons value values hypothesis =>
    have positive : remaining.val > 0 := by simp at count; omega
    let next : Fin (position + 1) := ⟨remaining.val - 1, by omega⟩
    have scan := Tape.scan_right (machine := machine position) (state := (remaining, false, 3))
      (units value) left (1 :: (fields values ++ tail)) (by
        intro symbol member
        have equality := List.eq_of_mem_replicate member
        subst symbol; simp [machine, positive])
    have advance := Tape.move_right (machine := machine position) (state := (remaining, false, 3))
      (nextState := (next, false, 3)) ((units value).reverse ++ left) (fields values ++ tail) 1
      (by simp [machine, positive, next])
    have rest := hypothesis next (by dsimp [next]; simp at count; omega)
      (1 :: ((units value).reverse ++ left))
    have trace := scan.trans (Tape.Steps.next advance rest)
    simpa [UnaryMachine.fields_cons, List.reverse_append, List.append_assoc] using trace

/-- A restoring comparison uses one reserved cell before the header for its
Boolean result. Caller storage on both sides is preserved; the exit head is on
the result cell, one cell left of its entry position. -/
theorem realizes_reserved (prior : List ℕ) (index limit : ℕ) (caller tail : List Symbol) (bounded : index ≤ limit) :
    Tape.Steps (machine prior.length) (2 * index ^ 2 + 10 * index + 2 * (fields prior).length + 8)
      (Tape.configuration (Fin.last prior.length, false, 0) (0 :: caller) (fields (prior ++ [index, limit]) ++ tail))
      (Tape.configuration (0, false, 14) caller
        (data (decide (index < limit)) :: (fields (prior ++ [index, limit]) ++ tail))) := by
  let remaining := Fin.last prior.length
  let suffix := fields [index, limit] ++ tail
  have enter := Tape.move_left_list (machine := machine prior.length) (state := (remaining, false, 0))
    (nextState := (remaining, false, 1)) caller (fields prior ++ suffix) 0 (by intro symbol; rfl)
  have mark := Tape.write (machine := machine prior.length) (state := (remaining, false, 1))
    (nextState := (remaining, false, 2)) caller (fields prior ++ suffix) 0 5 (by rfl)
  have advance := Tape.move_right (machine := machine prior.length) (state := (remaining, false, 2))
    (nextState := (remaining, false, 3)) caller (fields prior ++ suffix) 5 (by rfl)
  have skipped := skip prior remaining (by simp [remaining]) (5 :: caller) suffix
  have start := Tape.stay (machine := machine prior.length) (state := (0, false, 3))
    (nextState := (0, false, 4)) ((fields prior).reverse ++ 5 :: caller) suffix
    (by intro symbol; simp [machine])
  have paired := pairs (position := prior.length) index 0 (limit - index) ((fields prior).reverse ++ 5 :: caller) tail
  have finished := finish (position := prior.length) (fields prior) index (limit - index) tail caller (by
    intro symbol member
    rcases UnaryMachine.fields_symbols prior symbol member with equality | equality <;> subst symbol <;> decide)
  have sum : index + (limit - index) = limit := by omega
  have condition : (decide (0 < limit - index) : Bool) = decide (index < limit) := by
    simp only [Nat.sub_pos_iff_lt]
  simp only [Nat.zero_add, List.replicate_zero, List.nil_append, sum] at paired
  rw [sum, condition] at finished
  have paired' : Tape.Steps (machine prior.length) (index * (2 * index + 5))
      (Tape.configuration (0, false, 4) ((fields prior).reverse ++ 5 :: caller) suffix)
      (Tape.configuration (0, false, 4) (List.replicate index 3 ++ ((fields prior).reverse ++ 5 :: caller))
        (1 :: (List.replicate index 4 ++ units (limit - index) ++ 1 :: tail))) := by
    simpa [suffix, fields, List.append_assoc] using paired
  have trace := Tape.Steps.next enter (Tape.Steps.next mark (Tape.Steps.next advance
    (skipped.trans (Tape.Steps.next start (paired'.trans finished)))))
  convert trace using 1 <;> simp [suffix, remaining, UnaryMachine.fields_append, List.append_assoc]
  ring

/-- The blank-left calling convention is the empty-caller case. -/
theorem realizes (prior : List ℕ) (index limit : ℕ) (tail : List Symbol) (bounded : index ≤ limit) :
    Tape.Steps (machine prior.length) (2 * index ^ 2 + 10 * index + 2 * (fields prior).length + 8)
      (Tape.configuration (Fin.last prior.length, false, 0) [] (fields (prior ++ [index, limit]) ++ tail))
      (Tape.configuration (0, false, 14) []
        (data (decide (index < limit)) :: (fields (prior ++ [index, limit]) ++ tail))) := by
  simpa only [show (0 :: ([] : List Symbol)) = [] ++ [default] from rfl,
    Tape.configuration_append_blank] using realizes_reserved prior index limit [] tail bounded

/-- Use a declared field position, such as one derived from a named layout.
The prefix-length certificate keeps controller casts inside the library. -/
theorem realizes_at (position : ℕ) (prior : List ℕ) (prefixLength : prior.length = position)
    (index limit : ℕ) (tail : List Symbol) (bounded : index ≤ limit) :
    Tape.Steps (machine position) (2 * index ^ 2 + 10 * index + 2 * (fields prior).length + 8)
      (Tape.configuration (Fin.last position, false, 0) [] (fields (prior ++ [index, limit]) ++ tail))
      (Tape.configuration (0, false, 14) [] (data (decide (index < limit)) :: (fields (prior ++ [index, limit]) ++ tail))) := by
  subst position
  exact realizes prior index limit tail bounded

@[simp] theorem halt (symbol : Symbol) : machine position (0, false, 14) symbol = none := rfl

/-- Erase a guard result and enter the original header, restoring its reserved cell. -/
def consume : Turing.TM0.Machine Symbol (Fin 3) := fun phase _ =>
  match phase.val with
  | 0 => some (1, .write 0)
  | 1 => some (2, .move .right)
  | _ => none

/-- Erasing the result restores the reserved blank cell, without entering
or changing the caller's protected left region. -/
theorem consumes_reserved (result : Bool) (caller tail : List Symbol) :
    Tape.Steps consume 2 (Tape.configuration 0 caller (data result :: tail))
      (Tape.configuration 2 (0 :: caller) tail) := by
  have write := Tape.write (machine := consume) (state := 0) (nextState := 1)
    caller tail (data result) 0 (by rfl)
  have move := Tape.move_right (machine := consume) (state := 1) (nextState := 2) caller tail 0 (by rfl)
  exact .next write (.next move (.zero _))

theorem consumes (result : Bool) (tail : List Symbol) :
    Tape.Steps consume 2 (Tape.configuration 0 [] (data result :: tail))
      (Tape.configuration 2 [] tail) := by
  simpa only [show (0 :: ([] : List Symbol)) = [] ++ [default] from rfl,
    Tape.configuration_append_blank] using consumes_reserved result [] tail

@[simp] theorem consume_halt (symbol : Symbol) : consume 2 symbol = none := rfl

end Polytime.HeaderGuardMachine
