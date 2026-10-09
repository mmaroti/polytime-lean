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

/-! # Returning to a counter header after an indexed read

The fixed field count identifies the preserved header. Evaluation scratch to
its left is erased up to the start marker, and the head returns to the header.
-/

namespace Polytime.HeaderReturnMachine

open UnaryMachine (Symbol units fields)

abbrev State (count : ℕ) := Fin (count + 1) × Fin 6

/-- Phases: enter the header, cross its fields, erase scratch, move left,
return across erased cells, and halt. -/
def machine (count : ℕ) : Turing.TM0.Machine Symbol (State count) := fun (remaining, phase) symbol =>
  match phase.val with
  | 0 => some ((remaining, 1), .move .left)
  | 1 => if symbol = 2 then some ((remaining, 1), .move .left)
      else if remaining.val > 0 then some ((⟨remaining.val - 1, by omega⟩, 1), .move .left)
      else some ((remaining, 2), .write symbol)
  | 2 => if symbol = 7 then some ((remaining, 4), .write 0) else some ((remaining, 3), .write 0)
  | 3 => some ((remaining, 2), .move .left)
  | 4 => if symbol = 0 then some ((remaining, 4), .move .right) else some ((remaining, 5), .write symbol)
  | _ => none

variable {count : ℕ}

private theorem field (value : ℕ) (remaining : Fin (count + 1)) (positive : 0 < remaining.val)
    (marker : Symbol) (left right : List Symbol) :
    let next : Fin (count + 1) := ⟨remaining.val - 1, by omega⟩
    Tape.Steps (machine count) (value + 1)
      (Tape.configuration (remaining, 1) (units value ++ marker :: left) (1 :: right))
      (Tape.configuration (next, 1) left (marker :: (units value ++ 1 :: right))) := by
  dsimp only
  let next : Fin (count + 1) := ⟨remaining.val - 1, by omega⟩
  cases value with
  | zero =>
    exact Tape.Steps.next (Tape.move_left (machine := machine count) (state := (remaining, 1))
      (nextState := (next, 1)) left right marker 1 (by simp [machine, positive, next])) (.zero _)
  | succ value =>
    have first := Tape.move_left (machine := machine count) (state := (remaining, 1))
      (nextState := (next, 1)) (units value ++ marker :: left) right 2 1 (by simp [machine, positive, next])
    have scan := Tape.scan_left (machine := machine count) (state := (next, 1))
      (units value) left (1 :: right) marker 2 (by
        intro symbol member
        simp only [List.mem_cons, units, List.mem_replicate] at member
        rcases member with equality | ⟨_, equality⟩ <;> subst symbol <;> simp [machine])
    have changed : units value ++ 2 :: 1 :: right = units (value + 1) ++ 1 :: right := by
      simp [units, List.replicate_succ', List.append_assoc]
    simp only [UnaryMachine.units_reverse] at scan
    rw [changed] at scan
    simpa [units, List.replicate_succ, List.append_assoc] using Tape.Steps.next first scan

/-- Cross precisely the original header fields from right to left. The head
then rests on the scratch cell immediately before the header. -/
private theorem header (values : List ℕ) (remaining : Fin (count + 1))
    (position : remaining.val = values.length) (marker : Symbol) (left right : List Symbol) :
    let cells := (fields values).reverse ++ marker :: left
    Tape.Steps (machine count) (fields values).length
      (Tape.configuration (remaining, 1) cells.tail (cells.headD 0 :: right))
      (Tape.configuration (0, 1) left (marker :: (fields values ++ right))) := by
  induction values using List.reverseRecOn generalizing remaining right with
  | nil =>
    have equality : remaining = 0 := Fin.ext position
    subst remaining
    simp only [fields, List.flatMap_nil, List.reverse_nil, List.nil_append,
      List.tail_cons, List.headD_cons]
    exact .zero _
  | append_singleton values value hypothesis =>
    have positive : 0 < remaining.val := by simp at position; omega
    let next : Fin (count + 1) := ⟨remaining.val - 1, by omega⟩
    let cells := (fields values).reverse ++ marker :: left
    have nonempty : cells ≠ [] := by simp [cells]
    have cellsSplit : cells.headD 0 :: cells.tail = cells := by
      cases equation : cells with
      | nil => exact False.elim (nonempty equation)
      | cons symbol rest => rfl
    have first := field value remaining positive (cells.headD 0) cells.tail right
    have rest := hypothesis next (by dsimp [next]; simp at position; omega) (units value ++ 1 :: right)
    rw [cellsSplit] at first
    have result := first.trans rest
    simpa [cells, cellsSplit, fields, List.append_assoc,
      List.reverse_append, UnaryMachine.units_reverse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using result

private theorem erase (cells left right : List Symbol) (current : Symbol)
    (safe : ∀ symbol ∈ current :: cells, symbol ≠ 7) :
    Tape.Steps (machine count) (2 * cells.length + 3)
      (Tape.configuration (0, 2) (cells ++ 7 :: left) (current :: right))
      (Tape.configuration (0, 4) left (List.replicate (cells.length + 2) 0 ++ right)) := by
  induction cells generalizing current right with
  | nil =>
    have write := Tape.write (machine := machine count) (state := (0, 2)) (nextState := (0, 3))
      (7 :: left) right current 0 (by simp [machine, safe current (by simp)])
    have back := Tape.move_left (machine := machine count) (state := (0, 3)) (nextState := (0, 2))
      left right 7 0 (by rfl)
    have mark := Tape.write (machine := machine count) (state := (0, 2)) (nextState := (0, 4))
      left (0 :: right) 7 0 (by rfl)
    exact Tape.Steps.next write (Tape.Steps.next back (Tape.Steps.next mark (.zero _)))
  | cons symbol cells hypothesis =>
    have write := Tape.write (machine := machine count) (state := (0, 2)) (nextState := (0, 3))
      (symbol :: (cells ++ 7 :: left)) right current 0 (by simp [machine, safe current (by simp)])
    have back := Tape.move_left (machine := machine count) (state := (0, 3)) (nextState := (0, 2))
      (cells ++ 7 :: left) right symbol 0 (by rfl)
    have rest := hypothesis (0 :: right) symbol (by
      intro other member; exact safe other (by simp only [List.mem_cons] at member ⊢; tauto))
    have changed : List.replicate (cells.length + 2) (0 : Symbol) ++ 0 :: right =
        List.replicate (cells.length + 3) 0 ++ right := by
      rw [List.replicate_succ' (n := cells.length + 2), List.append_assoc]; rfl
    rw [changed] at rest
    simpa [Nat.mul_add, Nat.add_assoc] using Tape.Steps.next write (Tape.Steps.next back rest)

/-- Erase evaluation scratch and restore the original counter header. The scalar
output and the complete matrix suffix remain untouched. The number of header
fields is fixed in the controller, while all field values and scratch lengths vary. -/
theorem realizes (values scratch : List ℕ) (address : ℕ) (right : List Symbol)
    (nonempty : values ≠ []) :
    Tape.Steps (machine values.length)
      ((fields values).length + 3 * ((fields scratch).length + address) + 8)
      (Tape.configuration (Fin.last values.length, 0)
        ((fields values).reverse ++ (fields scratch).reverse ++ 6 :: (List.replicate address 0 ++ [7])) right)
      (Tape.configuration (0, 5) [] (fields values ++ right)) := by
  let trash := (fields scratch).reverse ++ [6]
  have trashNonempty : trash ≠ [] := by simp [trash]
  have trashSplit : trash.headD 6 :: trash.tail = trash := by
    cases equation : trash with
    | nil => exact False.elim (trashNonempty equation)
    | cons symbol rest => rfl
  have boundarySafe : trash.headD 6 ≠ 2 := by
    cases scratch using List.reverseRecOn with
    | nil => decide
    | append_singleton before value =>
      simp [trash, fields, List.reverse_append, List.append_assoc]
  let garbage := trash.tail ++ List.replicate address 0 ++ [7]
  let cells := (fields values).reverse ++ trash.headD 6 :: garbage
  have cellsNonempty : cells ≠ [] := by simp [cells]
  have enter : Turing.TM0.step (machine values.length)
      (Tape.configuration (Fin.last values.length, 0) cells right) =
      some (Tape.configuration (Fin.last values.length, 1) cells.tail (cells.headD 0 :: right)) := by
    cases equation : cells with
    | nil => exact False.elim (cellsNonempty equation)
    | cons symbol rest =>
      exact Tape.move_left_list (machine := machine values.length)
        (state := (Fin.last values.length, 0)) (nextState := (Fin.last values.length, 1))
        rest right symbol (by intro current; rfl)
  have preserved := header values (Fin.last values.length) rfl (trash.headD 6) garbage right
  have switch := Tape.write (machine := machine values.length) (state := (0, 1)) (nextState := (0, 2))
    garbage (fields values ++ right) (trash.headD 6) (trash.headD 6) (by
      have safe := boundarySafe
      rw [List.headD_eq_head?_getD] at safe
      simp [machine, safe])
  have safe : ∀ symbol ∈ trash.headD 6 :: (trash.tail ++ List.replicate address 0), symbol ≠ 7 := by
    intro symbol member
    have equality : trash.headD 6 :: (trash.tail ++ List.replicate address 0) = trash ++ List.replicate address 0 := by
      rw [← List.cons_append, trashSplit]
    rw [equality] at member
    simp only [trash, List.mem_append, List.mem_reverse, List.mem_singleton, List.mem_replicate] at member
    rcases member with (member | equality) | ⟨_, equality⟩
    · rcases UnaryMachine.fields_symbols scratch symbol member with equality | equality <;> subst symbol <;> decide
    · subst symbol; decide
    · subst symbol; decide
  have erased := erase (count := values.length) (trash.tail ++ List.replicate address 0) []
    (fields values ++ right) (trash.headD 6) safe
  let width := (trash.tail ++ List.replicate address 0).length + 2
  have returnHead := Tape.scan_right (machine := machine values.length) (state := (0, 4))
    (List.replicate width 0) [] (fields values ++ right) (by
      intro symbol member
      have equality : symbol = 0 := List.eq_of_mem_replicate member
      subst symbol; rfl)
  have returned : Tape.Steps (machine values.length) 1
      (Tape.configuration (0, 4) (List.replicate width 0) (fields values ++ right))
      (Tape.configuration (0, 5) (List.replicate width 0) (fields values ++ right)) := by
    have fieldsNonempty : fields values ≠ [] := by
      cases values with
      | nil => exact False.elim (nonempty rfl)
      | cons value values => simp [fields]
    cases equation : fields values with
    | nil => exact False.elim (fieldsNonempty equation)
    | cons symbol tail =>
      have member : symbol ∈ fields values := by rw [equation]; simp
      have nonzero : symbol ≠ 0 := by
        rcases UnaryMachine.fields_symbols values symbol member with equality | equality <;> subst symbol <;> decide
      exact Tape.Steps.next (Tape.write (machine := machine values.length) (state := (0, 4))
        (nextState := (0, 5)) (List.replicate width 0) (tail ++ right) symbol symbol
        (by simp [machine, nonzero])) (.zero _)
  have blankLeft (length : ℕ) : Tape.configuration ((0, 5) : State values.length)
      (List.replicate length (0 : Symbol)) (fields values ++ right) =
      Tape.configuration ((0, 5) : State values.length) [] (fields values ++ right) := by
    induction length with
    | zero => rfl
    | succ length hypothesis =>
      rw [List.replicate_succ']
      exact (Tape.configuration_append_blank ((0, 5) : State values.length)
        (List.replicate length (0 : Symbol)) (fields values ++ right)).trans hypothesis
  simp only [List.reverse_replicate, List.append_nil] at returnHead
  rw [blankLeft] at returned
  dsimp only [cells, garbage] at enter preserved switch
  simp only [List.append_assoc] at enter preserved erased switch
  have result := Tape.Steps.next enter (preserved.trans (Tape.Steps.next switch
    (erased.trans (returnHead.trans returned))))
  have trashLength : trash.tail.length = (fields scratch).length := by
    have lengths := congrArg List.length trashSplit
    simp only [List.length_cons] at lengths
    have total : trash.length = (fields scratch).length + 1 := by simp [trash]
    omega
  have erasedLength : (trash.tail ++ List.replicate address 0).length = (fields scratch).length + address := by
    simp [trashLength]
  have returnWidth : width = (fields scratch).length + address + 2 := by simp [width, erasedLength]
  convert result using 1
  · simp only [List.length_replicate]
    omega
  · simp only [List.append_assoc, ← List.cons_append, trashSplit, trash, List.singleton_append]

@[simp] theorem halt (symbol : Symbol) : machine count (0, 5) symbol = none := rfl

end Polytime.HeaderReturnMachine
