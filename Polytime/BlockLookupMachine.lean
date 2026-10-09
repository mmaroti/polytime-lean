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

import Polytime.TupleLookupMachine
import Polytime.FiniteTableMachine

/-! # Indexed fixed-width field lookup in a prepared frame

The field width is fixed before runtime. Routing consumes a binary scratch
index; reading stores only the fixed field in finite controller states.
-/

namespace Polytime.BlockLookupMachine

open TupleMachine

/-- Reuse the router and table controller; the Boolean return phase selects
navigation to the array separator or to the scratch-index start marker. -/
abbrev State (width : ℕ) :=
  Sum TupleMachine.State (Sum (Bool × (Fin width → Bool)) (FiniteTableMachine.State width width))

instance {width : ℕ} : Inhabited (State width) := ⟨.inl (false, 1)⟩

variable {width : ℕ}

def machine : Turing.TM0.Machine Symbol (State width) := fun state symbol =>
  match state with
  | .inl (flag, phase) =>
    if phase = 13 ∧ (symbol = cursor false ∨ symbol = cursor true) then
      some (.inr (.inr (.read 0 (fun _ => false))), .write (data (symbol = cursor true)))
    else (TupleMachine.machine (flag, phase) symbol).map
      fun (next, action) => (.inl next, action)
  | .inr (.inl (indexPhase, bits)) =>
    if indexPhase then
      if symbol = 3 then some (.inr (.inr (.emit (Fin.last width) bits)), .write symbol)
      else some (.inr (.inl (true, bits)), .move .left)
    else
      if symbol = 4 then some (.inr (.inl (true, bits)), .write symbol)
      else some (.inr (.inl (false, bits)), .move .left)
  | .inr (.inr (.read position bits)) =>
    if position.val < width then
      (FiniteTableMachine.machine (id : (Fin width → Bool) → (Fin width → Bool))
        (.read position bits) symbol).map fun (next, action) => (.inr (.inr next), action)
    else some (.inr (.inl (false, bits)), .move .left)
  | .inr (.inr state) =>
    (FiniteTableMachine.machine (id : (Fin width → Bool) → (Fin width → Bool)) state symbol).map
      fun (next, action) => (.inr (.inr next), action)

private theorem routing {ticks : ℕ} {initial final : Tape.Configuration Symbol TupleMachine.State}
    (trace : Tape.Steps TupleMachine.machine ticks initial final) (early : final.q.2.val ≤ 12) :
    Tape.Steps (machine (width := width)) ticks
      ⟨.inl initial.q, initial.Tape⟩ ⟨.inl final.q, final.Tape⟩ := by
  apply (trace.rename_until Sum.inl (fun state => state.2.val ≤ 12)
    (fun state symbol next => TupleLookupMachine.routing_predecessor state next symbol) ?_ early).2
  intro state symbol next action sourceEarly _ command
  obtain ⟨flag, phase⟩ := state
  have different : phase ≠ (13 : Fin 16) := by
    intro equality
    change phase.val ≤ 12 at sourceEarly
    rw [equality] at sourceEarly
    contradiction
  simp [machine, different, command]

/-- Locate a bit using the common router, restore its cursor, and enter the
fixed-width reader at that bit. The tape outside scratch is unchanged. -/
theorem select (counter before after : List Bool) (old : Bool)
    (left right : List Symbol) (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 32 * (counter.length + before.length + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (false, 6)) (3 :: left)
          (word counter ++ 4 :: (marked (before ++ old :: after) ++ right)))
        (Tape.configuration (.inr (.inr (.read 0 (fun _ => false))))
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
  have routed := routing (width := width) trace (by change (6 : ℕ) ≤ 12; decide)
  simp only [List.nil_append, word, List.map_nil] at routed
  have borrow := routing (width := width)
    (borrow_zeros counter.length false (3 :: left)
      (4 :: (word before ++ cursor old :: (word after ++ right))))
    (by change (6 : ℕ) ≤ 12; decide)
  have delimiter := Tape.move_right (machine := machine (width := width))
    (state := .inl (false, 6)) (nextState := .inl (false, 13))
    (List.replicate counter.length (data true) ++ 3 :: left)
    (word before ++ cursor old :: (word after ++ right)) 4 (by rfl)
  have scan := Tape.scan_right (machine := machine (width := width)) (state := .inl (false, 13))
    (word before) (4 :: (List.replicate counter.length (data true) ++ 3 :: left))
    (cursor old :: (word after ++ right)) (by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol
      cases bit <;> rfl)
  have restore := Tape.write (machine := machine (width := width)) (state := .inl (false, 13))
    (nextState := .inr (.inr (.read 0 (fun _ => false))))
    ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: left))
    (word after ++ right) (cursor old) (data old) (by cases old <;> rfl)
  have result := routed.trans (borrow.trans (Tape.Steps.next delimiter
    (scan.trans (Tape.Steps.next restore (.zero _)))))
  refine ⟨ticks + (2 * counter.length + (before.length + 2)), ?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero, List.length_append, List.length_cons] at bound
    rw [indexValue] at bound
    nlinarith
  · simpa [Tape.configuration, configuration, word, List.append_assoc,
      Nat.add_assoc] using result

def reading : FiniteTableMachine.State width width → Prop
  | .read _ _ => True
  | _ => False

theorem reading_predecessor (state next : FiniteTableMachine.State width width)
    (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (command : FiniteTableMachine.machine id state symbol = some (next, action))
    (allowed : reading next) : reading state := by
  cases state with
  | read => trivial
  | halt => simp [FiniteTableMachine.machine] at command
  | rewind remaining bits =>
    simp only [FiniteTableMachine.machine] at command
    split at command
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨equality, _⟩ := command
      rw [← equality] at allowed
      exact allowed
  | emit remaining bits =>
    simp only [FiniteTableMachine.machine] at command
    split at command
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨equality, _⟩ := command
      rw [← equality] at allowed
      exact allowed
  | write position bits =>
    simp only [FiniteTableMachine.machine, Option.some.injEq, Prod.mk.injEq] at command
    obtain ⟨equality, _⟩ := command
    rw [← equality] at allowed
    exact allowed

/-- Fixed-width reading is lifted into the combined finite controller. -/
theorem reads (bits : Fin width → Bool) (left tail : List Symbol) :
    Tape.Steps (machine (width := width)) width
      (Tape.configuration (.inr (.inr (.read 0 (fun _ => false)))) left (word (List.ofFn bits) ++ tail))
      (Tape.configuration (.inr (.inr (.read (Fin.last width) bits)))
        ((word (List.ofFn bits)).reverse ++ left) tail) := by
  have trace := FiniteTableMachine.reads (id : (Fin width → Bool) → (Fin width → Bool)) bits left tail
  apply (trace.rename_until (fun state => (.inr (.inr state) : State width)) reading
    (fun state symbol next => reading_predecessor state next symbol)
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

private def emitting : FiniteTableMachine.State width width → Prop
  | .emit _ _ | .write _ _ | .halt => True
  | _ => False

private theorem emitting_successor (state next : FiniteTableMachine.State width width)
    (symbol : Symbol) (action : Turing.TM0.Stmt Symbol) (allowed : emitting state)
    (command : FiniteTableMachine.machine id state symbol = some (next, action)) : emitting next := by
  cases state with
  | read | rewind => exact allowed.elim
  | halt => simp [FiniteTableMachine.machine] at command
  | emit remaining bits =>
    simp only [FiniteTableMachine.machine] at command
    split at command
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at command
      obtain ⟨equality, _⟩ := command
      rw [← equality]
      trivial
  | write position bits =>
    simp only [FiniteTableMachine.machine, Option.some.injEq, Prod.mk.injEq] at command
    obtain ⟨equality, _⟩ := command
    rw [← equality]
    trivial

/-- Return the field in the reserved output window, preserving its contexts. -/
theorem emits (bits : Fin width → Bool) (reserved left right : List Symbol)
    (length : reserved.length = width) :
    Tape.Steps (machine (width := width)) (2 * width + 1)
      (Tape.configuration (.inr (.inr (.emit (Fin.last width) bits))) (reserved ++ left) right)
      (Tape.configuration (.inr (.inr .halt)) left (word (List.ofFn bits) ++ right)) := by
  have trace := FiniteTableMachine.emit_loop (id : (Fin width → Bool) → (Fin width → Bool))
    bits reserved left right (Fin.last width) length.symm
  have lifted := trace.rename_from (fun state => (.inr (.inr state) : State width)) emitting
    (fun state symbol next => emitting_successor state next symbol)
    (targetMachine := machine) (by
      intro state symbol next action allowed command
      cases state with
      | read | rewind => exact allowed.elim
      | emit | write | halt => simp [machine, command]) trivial
  simpa only [Tape.configuration, Fin.val_last,
    List.take_of_length_le (by simp : (List.ofFn bits).length ≤ width)] using lifted

/-- Return from the selected field to its reserved output window. The machine
uses separators to cross the variable-length array prefix and scratch index. -/
theorem returns (bits : Fin width → Bool) (before : List Bool) (counterWidth : ℕ)
    (reserved left tail : List Symbol) (positive : 0 < width) (length : reserved.length = width) :
    Tape.Steps (machine (width := width)) (counterWidth + before.length + 3 * width + 5)
      (Tape.configuration (.inr (.inr (.read (Fin.last width) bits)))
        ((word (List.ofFn bits)).reverse ++ (word before).reverse ++
          4 :: (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left))) tail)
      (Tape.configuration (.inr (.inr .halt)) left
        (word (List.ofFn bits) ++ 3 :: (List.replicate counterWidth (data true) ++
          4 :: (word before ++ word (List.ofFn bits) ++ tail)))) := by
  have arrayLength : (word (before ++ List.ofFn bits)).length = before.length + width := by simp
  have nonempty : (word (before ++ List.ofFn bits)).reverse ≠ [] := by
    intro empty
    have emptyLength := congrArg List.length empty
    simp only [List.length_reverse, arrayLength, List.length_nil] at emptyLength
    omega
  obtain ⟨last, remaining, reverseEq⟩ := List.exists_cons_of_ne_nil nonempty
  have arrayEq : remaining.reverse ++ [last] = word (before ++ List.ofFn bits) := by
    have reversed := congrArg List.reverse reverseEq
    simpa using reversed.symm
  have move := Tape.move_left_list (machine := machine (width := width))
    (state := .inr (.inr (.read (Fin.last width) bits)))
    (nextState := .inr (.inl (false, bits)))
    (remaining ++ 4 :: (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left)))
    tail last (by intro symbol; simp [machine])
  have back := Tape.scan_left (machine := machine (width := width))
    (state := .inr (.inl (false, bits))) remaining
    (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left)) tail 4 last (by
      intro symbol member
      have inArray : symbol ∈ word (before ++ List.ofFn bits) := by
        apply List.mem_reverse.mp
        rw [reverseEq]
        exact member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp inArray
      subst symbol
      cases bit <;> rfl)
  have switch := Tape.write (machine := machine (width := width))
    (state := .inr (.inl (false, bits))) (nextState := .inr (.inl (true, bits)))
    (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left))
    (word before ++ word (List.ofFn bits) ++ tail) 4 4 (by rfl)
  have indexBack := Tape.scan_left (machine := machine (width := width))
    (state := .inr (.inl (true, bits))) (List.replicate counterWidth (data true))
    (reserved ++ left) (word before ++ word (List.ofFn bits) ++ tail) 3 4 (by
      intro symbol member
      simp only [List.mem_cons, List.mem_replicate] at member
      rcases member with equality | ⟨_, equality⟩
      · subst symbol; rfl
      · subst symbol; rfl)
  have enter := Tape.write (machine := machine (width := width))
    (state := .inr (.inl (true, bits)))
    (nextState := .inr (.inr (.emit (Fin.last width) bits))) (reserved ++ left)
    (List.replicate counterWidth (data true) ++ 4 :: (word before ++ word (List.ofFn bits) ++ tail))
    3 3 (by rfl)
  have emit := emits bits reserved left
    (3 :: (List.replicate counterWidth (data true) ++ 4 ::
      (word before ++ word (List.ofFn bits) ++ tail))) length
  have remainingLength : remaining.length + 1 = before.length + width := by
    have equality := congrArg List.length reverseEq
    simpa [Nat.add_comm] using equality.symm
  have back' : Tape.Steps (machine (width := width)) (remaining.length + 1)
      (Tape.configuration (.inr (.inl (false, bits)))
        (remaining ++ 4 :: (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left)))
        (last :: tail))
      (Tape.configuration (.inr (.inl (false, bits)))
        (List.replicate counterWidth (data true) ++ 3 :: (reserved ++ left))
        (4 :: (word before ++ word (List.ofFn bits) ++ tail))) := by
    have rightEq : remaining.reverse ++ last :: tail =
        word before ++ word (List.ofFn bits) ++ tail := by
      calc
        _ = (remaining.reverse ++ [last]) ++ tail := (List.append_assoc _ _ _).symm
        _ = _ := by rw [arrayEq, word_append, List.append_assoc]
    rw [rightEq] at back
    exact back
  simp only [List.reverse_replicate] at indexBack
  have result := Tape.Steps.next move (back'.trans (Tape.Steps.next switch
    (indexBack.trans (Tape.Steps.next enter emit))))
  have leftEq : (word (List.ofFn bits)).reverse ++ (word before).reverse = last :: remaining := by
    simpa [word_append, List.reverse_append] using reverseEq
  convert result using 1
  · simp only [List.length_replicate] at *
    omega
  · simp only [Tape.configuration, leftEq, List.cons_append]

/-- Read a complete fixed-width field into a reserved output window. The
array and both caller-owned contexts are preserved; only index scratch changes. -/
theorem lookup_prepared (bits : Fin width → Bool) (counter before after : List Bool)
    (reserved left right : List Symbol) (positive : 0 < width)
    (length : reserved.length = width) (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 64 * (counter.length + before.length + width + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (false, 6)) (3 :: (reserved ++ left))
          (word counter ++ 4 :: (marked (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr .halt)) left
          (word (List.ofFn bits) ++ 3 :: (List.replicate counter.length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  let first : Fin width := ⟨0, positive⟩
  have split : List.ofFn bits = bits first :: (List.ofFn bits).drop 1 := by
    have result := List.drop_eq_getElem_cons (l := List.ofFn bits) (i := 0) (by simpa using positive)
    rw [List.getElem_ofFn] at result
    simpa [first] using result
  obtain ⟨selectTicks, selectBound, selected⟩ := select (width := width) counter before
    ((List.ofFn bits).drop 1 ++ after) (bits first) (reserved ++ left) right indexValue
  have read := reads bits
    ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: (reserved ++ left)))
    (word after ++ right)
  have returned := returns bits before counter.length reserved left (word after ++ right) positive length
  have selected' : Tape.Steps (machine (width := width)) selectTicks
      (Tape.configuration (.inl (false, 6)) (3 :: (reserved ++ left))
        (word counter ++ 4 :: (marked (before ++ List.ofFn bits ++ after) ++ right)))
      (Tape.configuration (.inr (.inr (.read 0 (fun _ => false))))
        ((word before).reverse ++ 4 :: (List.replicate counter.length (data true) ++ 3 :: (reserved ++ left)))
        (word (List.ofFn bits) ++ word after ++ right)) := by
    have arraySplit : before ++ List.ofFn bits ++ after =
        before ++ bits first :: ((List.ofFn bits).drop 1 ++ after) := by
      exact (congrArg (fun middle => before ++ middle ++ after) split).trans
        (by simp only [List.append_assoc, List.cons_append])
    have packed : word (List.ofFn bits) = data (bits first) :: word ((List.ofFn bits).drop 1) := by
      simpa only [word, List.map_cons] using congrArg word split
    simpa only [arraySplit, word_append, packed, List.cons_append, List.append_assoc] using selected
  simp only [List.append_assoc] at selected' read returned
  have result := selected'.trans (read.trans returned)
  refine ⟨selectTicks + (width + (counter.length + before.length + 3 * width + 5)), ?_, ?_⟩
  · have tailLength : ((List.ofFn bits).drop 1).length + 1 = width := by
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

/-- Prepare the cursor from ordinary binary index and array bits, then read
and return the complete field. The reserved output window may contain old data. -/
theorem lookup (bits : Fin width → Bool) (counter before after : List Bool)
    (reserved left right : List Symbol) (positive : 0 < width)
    (length : reserved.length = width) (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 96 * (counter.length + before.length + width + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (false, 1)) (reserved ++ left)
          (data false :: word counter ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr .halt)) left
          (word (List.ofFn bits) ++ 3 :: (List.replicate counter.length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  have nonempty : before ++ List.ofFn bits ++ after ≠ [] := by
    intro empty
    have sizes := congrArg List.length empty
    simp only [List.length_append, List.length_ofFn, List.length_nil] at sizes
    omega
  obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil nonempty
  have prepared := routing (width := width)
    (TupleMachine.prepare counter rest first false (reserved ++ left) right)
    (by change (6 : ℕ) ≤ 12; decide)
  obtain ⟨ticks, bound, trace⟩ := lookup_prepared bits counter before after reserved left right
    positive length indexValue
  rw [split] at trace
  have result := prepared.trans trace
  refine ⟨2 * counter.length + 7 + ticks, ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa [Tape.configuration, configuration, word, split, marked] using result

/-- Read using an already prepared binary counter and its start marker.
The first-entry cursor is installed by this routine. -/
theorem lookup_from_marker (bits : Fin width → Bool) (counter before after : List Bool)
    (reserved left right : List Symbol) (positive : 0 < width)
    (length : reserved.length = width) (indexValue : Binary.value counter = before.length) :
    ∃ ticks, ticks ≤ 96 * (counter.length + before.length + width + after.length + 2) ^ 2 ∧
      Tape.Steps (machine (width := width)) ticks
        (Tape.configuration (.inl (false, 2)) (reserved ++ left)
          (3 :: word counter ++ 4 :: (word (before ++ List.ofFn bits ++ after) ++ right)))
        (Tape.configuration (.inr (.inr .halt)) left
          (word (List.ofFn bits) ++ 3 :: (List.replicate counter.length (data true) ++
            4 :: (word before ++ word (List.ofFn bits) ++ word after ++ right)))) := by
  have nonempty : before ++ List.ofFn bits ++ after ≠ [] := by
    intro empty
    have sizes := congrArg List.length empty
    simp only [List.length_append, List.length_ofFn, List.length_nil] at sizes
    omega
  obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil nonempty
  have prepared := routing (width := width)
    (TupleMachine.prepare_cursor counter rest first false (reserved ++ left) right)
    (by change (6 : ℕ) ≤ 12; decide)
  obtain ⟨ticks, bound, trace⟩ := lookup_prepared bits counter before after reserved left right
    positive length indexValue
  rw [split] at trace
  have result := prepared.trans trace
  refine ⟨2 * counter.length + 6 + ticks, ?_, ?_⟩
  · ring_nf at bound ⊢
    nlinarith
  · simpa [Tape.configuration, configuration, word, split, marked] using result

@[simp] theorem halt (symbol : Symbol) :
    machine (width := width) (.inr (.inr .halt)) symbol = none := rfl

end Polytime.BlockLookupMachine
