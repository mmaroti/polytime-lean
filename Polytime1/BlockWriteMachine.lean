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

/-! # Indexed fixed-width writes with a runtime replacement value

The replacement is read from its input slot into fixed-width finite controller
states. Routing consumes a binary scratch index; the output slot retains the
replacement and the selected array field is overwritten.
-/

namespace Polytime1.BlockWriteMachine

open TupleMachine

/-- Reuse fixed readers/writers and the indexed router; the held replacement
has a constant width independent of array length and address. -/
abbrev State (width : ℕ) :=
  Sum (FiniteTableMachine.State width width)
    (Sum ((Fin width → Bool) × TupleMachine.State)
      (Sum (FiniteTableMachine.State width width) (BlockLookupMachine.State width)))

instance {width : ℕ} : Inhabited (State width) := ⟨.inl (.read 0 (fun _ => false))⟩

variable {width : ℕ}

def machine : Turing.TM0.Machine Symbol (State width) := fun state symbol =>
  match state with
  | .inl (.read position bits) =>
    if position.val < width then
      (FiniteTableMachine.machine (id : (Fin width → Bool) → (Fin width → Bool))
        (.read position bits) symbol).map fun (next, action) => (.inl next, action)
    else some (.inr (.inl (bits, (false, 1))), .write symbol)
  | .inl _ => none
  | .inr (.inl (bits, (flag, phase))) =>
    if phase = 13 ∧ (symbol = cursor false ∨ symbol = cursor true) then
      if positive : 0 < width then
        some (.inr (.inr (.inl (.write ⟨0, positive⟩ bits))), .write (data (symbol = cursor true)))
      else none
    else (TupleMachine.machine (flag, phase) symbol).map
      fun (next, action) => (.inr (.inl (bits, next)), action)
  | .inr (.inr (.inl (.write position bits))) =>
    some (.inr (.inr (.inl (.emit ⟨position.val + 1, by omega⟩ bits))), .write (data (bits position)))
  | .inr (.inr (.inl (.emit position bits))) =>
    if valid : position.val < width then
      some (.inr (.inr (.inl (.write ⟨position.val, valid⟩ bits))), .move .right)
    else some (.inr (.inr (.inr (.inr (.inr (.read (Fin.last width) bits))))), .move .right)
  | .inr (.inr (.inl _)) => none
  | .inr (.inr (.inr state)) =>
    (BlockLookupMachine.machine state symbol).map fun (next, action) => (.inr (.inr (.inr next)), action)

/-- Read the replacement from runtime tape data. -/
theorem reads (bits : Fin width → Bool) (left tail : List Symbol) :
    Tape.Steps (machine (width := width)) width
      (Tape.configuration (.inl (.read 0 (fun _ => false))) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration (.inl (.read (Fin.last width) bits))
        ((word (List.ofFn bits)).reverse ++ left) tail) := by
  have trace := FiniteTableMachine.reads (id : (Fin width → Bool) → (Fin width → Bool)) bits left tail
  apply (trace.rename_until (fun state => (.inl state : State width)) BlockLookupMachine.reading
    (fun state symbol next => BlockLookupMachine.reading_predecessor state next symbol)
    (targetMachine := machine) ?_ trivial).2
  intro state symbol next action sourceAllowed nextAllowed command
  cases state with
  | read position stored =>
    by_cases valid : position.val < width
    · simp [machine, valid, command]
    · simp only [FiniteTableMachine.machine, valid, ↓reduceDIte,
        Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨equality, _⟩ := command
      rw [← equality] at nextAllowed
      exact nextAllowed.elim
  | rewind | emit | write | halt => exact sourceAllowed.elim

private theorem routing (bits : Fin width → Bool) {ticks : ℕ}
    {initial final : Tape.Configuration Symbol TupleMachine.State}
    (trace : Tape.Steps TupleMachine.machine ticks initial final) (early : final.q.2.val ≤ 12) :
    Tape.Steps machine ticks
      ⟨.inr (.inl (bits, initial.q)), initial.Tape⟩
      ⟨.inr (.inl (bits, final.q)), final.Tape⟩ := by
  apply (trace.rename_until (fun state => .inr (.inl (bits, state)))
    (fun state => state.2.val ≤ 12)
    (fun state symbol next => TupleLookupMachine.routing_predecessor state next symbol)
    (targetMachine := machine) ?_ early).2
  intro state symbol next action sourceEarly _ command
  obtain ⟨flag, phase⟩ := state
  have different : phase ≠ (13 : Fin 16) := by
    intro equality
    change phase.val ≤ 12 at sourceEarly
    rw [equality] at sourceEarly
    contradiction
  simp [machine, different, command]

/-- Select the destination and enter the fixed-width writer. -/
theorem select (bits : Fin width → Bool) (counter before after : List Bool) (old : Bool)
    (left right : List Symbol) (positive : 0 < width)
    (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 32 * (counter.length + before.length + after.length + 2) ^ 2 ∧
      Tape.Steps machine ticks
        (Tape.configuration (.inr (.inl (bits, (false, 6)))) (3 :: left)
          (word counter ++ 4 :: (marked (before ++ old :: after) ++ right)))
        (Tape.configuration (.inr (.inr (.inl (.write ⟨0, positive⟩ bits))))
          ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: left))
          (data old :: word after ++ right)) := by
  obtain ⟨ticks, routedBefore, selected, routedAfter, decomposition, lengthEq, bound, trace⟩ :=
    TupleMachine.route counter [] (before ++ old :: after) false left right (by simp [indexValue])
  have beforeEq : before = routedBefore := List.append_inj_left decomposition (by omega)
  subst routedBefore
  simp only [List.append_cancel_left_eq, List.cons.injEq] at decomposition
  obtain ⟨oldEq, afterEq⟩ := decomposition
  subst selected
  subst routedAfter
  have routed := routing bits trace (by change (6 : ℕ) ≤ 12; decide)
  simp only [List.nil_append, word, List.map_nil] at routed
  have borrow := routing bits
    (borrow_zeros counter.length false (3 :: left)
      (4 :: (word before ++ cursor old :: (word after ++ right))))
    (by change (6 : ℕ) ≤ 12; decide)
  have delimiter := Tape.move_right (machine := machine (width := width))
    (state := .inr (.inl (bits, (false, 6)))) (nextState := .inr (.inl (bits, (false, 13))))
    (List.replicate counter.length (data true) ++ 3 :: left)
    (word before ++ cursor old :: (word after ++ right)) 4 (by rfl)
  have scan := Tape.scan_right (machine := machine (width := width))
    (state := .inr (.inl (bits, (false, 13))))
    (word before) (4 :: (List.replicate counter.length (data true) ++ 3 :: left))
    (cursor old :: (word after ++ right)) (by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol
      cases bit <;> rfl)
  have restore := Tape.write (machine := machine (width := width))
    (state := .inr (.inl (bits, (false, 13))))
    (nextState := .inr (.inr (.inl (.write ⟨0, positive⟩ bits))))
    ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: left))
    (word after ++ right) (cursor old) (data old) (by cases old <;> simp [machine, positive, cursor, data])
  have result := routed.trans (borrow.trans (Tape.Steps.next delimiter
    (scan.trans (Tape.Steps.next restore (.zero _)))))
  refine ⟨ticks + (2 * counter.length + (before.length + 2)), ?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero, List.length_append, List.length_cons] at bound
    rw [indexValue] at bound
    nlinarith
  · simpa [Tape.configuration, configuration, word, List.append_assoc, Nat.add_assoc] using result

/-- Overwrite exactly the remaining field cells and leave the head immediately
past them. The replacement stays in constant-width finite controller states. -/
theorem writes (bits : Fin width → Bool) (position : Fin width) (old left tail : List Symbol)
    (length : old.length = width - position.val) :
    Tape.Steps (machine (width := width)) (2 * old.length)
      (Tape.configuration (.inr (.inr (.inl (.write position bits)))) left (old ++ tail))
      (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.read (Fin.last width) bits))))))
        ((word ((List.ofFn bits).drop position.val)).reverse ++ left) tail) := by
  induction old generalizing position left with
  | nil => simp only [List.length_nil] at length; omega
  | cons symbol old hypothesis =>
    let next : Fin (width + 1) := ⟨position.val + 1, by omega⟩
    have write := Tape.write (machine := machine (width := width))
      (state := .inr (.inr (.inl (.write position bits))))
      (nextState := .inr (.inr (.inl (.emit next bits)))) left (old ++ tail)
      symbol (data (bits position)) (by rfl)
    have split : (List.ofFn bits).drop position.val =
        bits position :: (List.ofFn bits).drop next.val := by
      have result := List.drop_eq_getElem_cons (l := List.ofFn bits) (i := position.val)
        (by simp)
      rw [List.getElem_ofFn] at result
      exact result
    by_cases valid : next.val < width
    · let nextPosition : Fin width := ⟨next.val, valid⟩
      have move := Tape.move_right (machine := machine (width := width))
        (state := .inr (.inr (.inl (.emit next bits))))
        (nextState := .inr (.inr (.inl (.write nextPosition bits)))) left (old ++ tail)
        (data (bits position)) (by simp [machine, valid, nextPosition])
      have rest := hypothesis nextPosition (data (bits position) :: left) (by
        simp only [List.length_cons] at length
        dsimp [nextPosition, next]
        omega)
      have result := Tape.Steps.next write (Tape.Steps.next move rest)
      have countEq : 2 * (symbol :: old).length = (2 * old.length + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [countEq]
      simpa [split, word, List.reverse_cons, List.append_assoc, nextPosition] using result
    · have atEnd : next.val = width := by have bound := next.isLt; omega
      have empty : old = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at length
        dsimp [next] at atEnd
        omega
      subst old
      have move := Tape.move_right (machine := machine (width := width))
        (state := .inr (.inr (.inl (.emit next bits))))
        (nextState := .inr (.inr (.inr (.inr (.inr (.read (Fin.last width) bits))))))
        left tail (data (bits position)) (by simp [machine, valid])
      have dropEmpty : (List.ofFn bits).drop next.val = [] := by
        rw [atEnd]
        apply List.drop_eq_nil_of_le
        simp
      simpa [split, dropEmpty, word] using
        Tape.Steps.next write (Tape.Steps.next move (.zero _))

/-- Return navigation reuses the existing lookup controller unchanged. -/
theorem returns (bits : Fin width → Bool) (before : List Bool) (counterWidth : ℕ)
    (reserved left tail : List Symbol) (positive : 0 < width) (length : reserved.length = width) :
    Tape.Steps (machine (width := width)) (counterWidth + before.length + 3 * width + 5)
      (Tape.configuration (.inr (.inr (.inr (.inr (.inr (.read (Fin.last width) bits))))))
        ((word (List.ofFn bits)).reverse ++ (word before).reverse ++
          4 :: (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left))) tail)
      (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) left
        (word (List.ofFn bits) ++ 3 :: (List.replicate counterWidth (data true) ++
          4 :: (word before ++ word (List.ofFn bits) ++ tail)))) := by
  have trace := BlockLookupMachine.returns bits before counterWidth reserved left tail positive length
  have lifted := trace.rename (fun state => (.inr (.inr (.inr state)) : State width))
    (targetMachine := machine) (by
      intro state symbol next action command
      simp [machine, command])
  simpa only [Tape.configuration] using lifted

/-- Write the held replacement into the selected field. The output window and
selected field receive the replacement; all other array entries are preserved. -/
theorem store_prepared (replacement original : Fin width → Bool) (counter before after : List Bool)
    (reserved left right : List Symbol) (positive : 0 < width)
    (length : reserved.length = width) (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 64 * (counter.length + before.length + width + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inr (.inl (replacement, (false, 6)))) (3 :: (reserved ++ left))
          (word counter ++ 4 :: (marked (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) left
          (word (List.ofFn replacement) ++ 3 :: (List.replicate counter.length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  let first : Fin width := ⟨0, positive⟩
  have split : List.ofFn original = original first :: (List.ofFn original).drop 1 := by
    have result := List.drop_eq_getElem_cons (l := List.ofFn original) (i := 0) (by simpa using positive)
    rw [List.getElem_ofFn] at result
    simpa [first] using result
  obtain ⟨selectTicks, selectBound, selected⟩ := select replacement counter before
    ((List.ofFn original).drop 1 ++ after) (original first) (reserved ++ left) right positive indexValue
  have write := writes replacement first (word (List.ofFn original))
    ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: (reserved ++ left)))
    (word after ++ right) (by simp [first])
  have returned := returns replacement before counter.length reserved left (word after ++ right) positive length
  have selected' : Tape.Steps (machine (width := width)) selectTicks
      (Tape.configuration (.inr (.inl (replacement, (false, 6)))) (3 :: (reserved ++ left))
        (word counter ++ 4 :: (marked (before ++ List.ofFn original ++ after) ++ right)))
      (Tape.configuration (.inr (.inr (.inl (.write first replacement))))
        ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: (reserved ++ left)))
        (word (List.ofFn original) ++ word after ++ right)) := by
    have arraySplit : before ++ List.ofFn original ++ after =
        before ++ original first :: ((List.ofFn original).drop 1 ++ after) := by
      exact (congrArg (fun middle => before ++ middle ++ after) split).trans
        (by simp only [List.append_assoc, List.cons_append])
    have packed' : word (List.ofFn original) =
        data (original first) :: word ((List.ofFn original).drop 1) := by
      simpa only [word, List.map_cons] using congrArg word split
    simpa only [arraySplit, word_append, packed', List.cons_append, List.append_assoc, first] using selected
  simp only [word_length, List.length_ofFn, first, List.drop_zero] at write
  simp only [List.append_assoc] at selected' returned
  have result := selected'.trans (write.trans returned)
  refine ⟨selectTicks + (2 * width + (counter.length + before.length + 3 * width + 5)), ?_, ?_⟩
  · have tailLength : ((List.ofFn original).drop 1).length + 1 = width := by
      have lengths := congrArg List.length split
      simp only [List.length_ofFn, List.length_cons] at lengths
      omega
    simp only [List.length_append] at selectBound
    have selectBound' : selectTicks ≤
        32 * (counter.length + before.length + width + after.length + 2) ^ 2 := by
      apply selectBound.trans
      apply Nat.mul_le_mul_left 32
      apply Nat.pow_le_pow_left
      omega
    ring_nf at selectBound' ⊢
    nlinarith
  · simpa only [List.append_assoc] using result

/-- One fixed finite machine reads a runtime replacement, prepares an indexed
write, and returns with exactly that field changed. The replacement slot survives. -/
theorem store (replacement original : Fin width → Bool) (counter before after : List Bool)
    (left right : List Symbol) (positive : 0 < width)
    (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 128 * (counter.length + before.length + width + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (.read 0 (fun _ => false))) left
          (word (List.ofFn replacement) ++ data false :: word counter ++
            4 :: (word (before ++ List.ofFn original ++ after) ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) left
          (word (List.ofFn replacement) ++ 3 :: (List.replicate counter.length (data true) ++
            4 :: (word before ++ word (List.ofFn replacement) ++ word after ++ right)))) := by
  have nonempty : before ++ List.ofFn original ++ after ≠ [] := by
    intro empty
    have sizes := congrArg List.length empty
    simp only [List.length_append, List.length_ofFn, List.length_nil] at sizes
    omega
  obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil nonempty
  let reserved := (word (List.ofFn replacement)).reverse
  let tail := data false :: word counter ++ 4 :: (word (before ++ List.ofFn original ++ after) ++ right)
  have read := reads replacement left tail
  have enter := Tape.stay (machine := machine (width := width))
    (state := .inl (.read (Fin.last width) replacement))
    (nextState := .inr (.inl (replacement, (false, 1)))) (reserved ++ left) tail
    (by intro symbol; simp [machine])
  have prepared := routing replacement
    (TupleMachine.prepare counter rest first false (reserved ++ left) right)
    (by change (6 : ℕ) ≤ 12; decide)
  obtain ⟨ticks, bound, trace⟩ := store_prepared replacement original counter before after
    reserved left right positive (by simp [reserved]) indexValue
  rw [split] at trace
  have prepared' : Tape.Steps (machine (width := width)) (2 * counter.length + 7)
      (Tape.configuration (.inr (.inl (replacement, (false, 1)))) (reserved ++ left) tail)
      (Tape.configuration (.inr (.inl (replacement, (false, 6)))) (3 :: (reserved ++ left))
        (word counter ++ 4 :: (marked (first :: rest) ++ right))) := by
    simpa [Tape.configuration, configuration, tail, split, word] using prepared
  have result := read.trans (Tape.Steps.next enter (prepared'.trans trace))
  refine ⟨width + (2 * counter.length + 7 + ticks + 1), ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa [tail, Nat.add_assoc] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr (.inr (.inr (.inr .halt))))) symbol = none := rfl

end Polytime1.BlockWriteMachine
