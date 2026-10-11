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

import Polytime1.Binary
import Polytime1.Tape

/-! # Indexed Boolean tuple lookup and update on a finite tape machine

The controller has 32 states and eight symbols, independent of tuple length.
A run returns the old selected bit and replaces it with the supplied bit.
The binary index is scratch and is consumed by borrow propagation.
-/

namespace Polytime1.TupleMachine

abbrev Symbol := Fin 8
abbrev State := Bool × Fin 16

instance : Inhabited Symbol := ⟨0⟩
instance : Inhabited State := ⟨(false, 0)⟩

/-- Alphabet: 0 blank, 1/2 data, 3 start, 4 separator, 5/6 cursor, 7 end. -/
def data (bit : Bool) : Symbol := if bit then 2 else 1
def cursor (bit : Bool) : Symbol := if bit then 6 else 5

def word (bits : List Bool) : List Symbol := bits.map data

def configuration (flag : Bool) (phase : Fin 16) (left right : List Symbol) :=
  Tape.configuration (flag, phase) left right

/-- Phases 0–5 prepare the frame; 6–12 route by decrementing the index;
13–15 read, update, and return the head to the output's first bit.
The Boolean state flag stores the replacement, then the selected old bit. -/
def machine : Turing.TM0.Machine Symbol State := fun (flag, phase) symbol =>
  match phase.val with
  | 0 => if symbol = data true then some ((flag, 0), .move .right)
      else if symbol = data false then some ((flag, 1), .move .right) else none
  | 1 => if symbol = data false then some ((false, 2), .write 3)
      else if symbol = data true then some ((true, 2), .write 3) else none
  | 2 => some ((flag, 3), .move .right)
  | 3 => if symbol = 4 then some ((flag, 4), .move .right)
      else some ((flag, 3), .move .right)
  | 4 => if symbol = data false then some ((flag, 5), .write (cursor false))
      else if symbol = data true then some ((flag, 5), .write (cursor true)) else none
  | 5 => if symbol = 3 then some ((flag, 6), .move .right)
      else some ((flag, 5), .move .left)
  | 6 => if symbol = data false then some ((flag, 7), .write (data true))
      else if symbol = data true then some ((flag, 8), .write (data false))
      else if symbol = 4 then some ((flag, 13), .move .right) else none
  | 7 => some ((flag, 6), .move .right)
  | 8 => some ((flag, 9), .move .right)
  | 9 => if symbol = cursor false then some ((flag, 10), .write (data false))
      else if symbol = cursor true then some ((flag, 10), .write (data true))
      else some ((flag, 9), .move .right)
  | 10 => some ((flag, 11), .move .right)
  | 11 => if symbol = data false then some ((flag, 12), .write (cursor false))
      else if symbol = data true then some ((flag, 12), .write (cursor true)) else none
  | 12 => if symbol = 3 then some ((flag, 6), .move .right)
      else some ((flag, 12), .move .left)
  | 13 => if symbol = cursor false then some ((false, 14), .write (data flag))
      else if symbol = cursor true then some ((true, 14), .write (data flag))
      else some ((flag, 13), .move .right)
  | 14 => if symbol = 4 then some ((flag, 15), .write (data flag))
      else some ((flag, 14), .move .left)
  | _ => none

abbrev Steps := Tape.Steps machine

@[simp] theorem word_length (bits : List Bool) : (word bits).length = bits.length := by
  simp [word]

@[simp] theorem word_append (left right : List Bool) : word (left ++ right) = word left ++ word right := by
  simp [word]

@[simp] theorem word_replicate (length : ℕ) (bit : Bool) :
    word (List.replicate length bit) = List.replicate length (data bit) := by simp [word]

/-- A borrow visits each trailing zero with exactly a write and a move. -/
theorem borrow_zeros (zeros : ℕ) (flag : Bool) (left right : List Symbol) :
    Steps (2 * zeros)
      (configuration flag 6 left (List.replicate zeros (data false) ++ right))
      (configuration flag 6 (List.replicate zeros (data true) ++ left) right) := by
  induction zeros generalizing left with
  | zero => exact .zero _
  | succ zeros hypothesis =>
    have first := Tape.write (machine := machine) (state := (flag, 6)) (nextState := (flag, 7))
      left (List.replicate zeros (data false) ++ right) (data false) (data true) (by rfl)
    have second := Tape.move_right (machine := machine) (state := (flag, 7)) (nextState := (flag, 6))
      left (List.replicate zeros (data false) ++ right) (data true) (by rfl)
    have rest := hypothesis (data true :: left)
    have commute : List.replicate zeros (data true) ++ data true :: left =
        data true :: (List.replicate zeros (data true) ++ left) := by
      calc
        _ = (List.replicate zeros (data true) ++ [data true]) ++ left := by simp
        _ = List.replicate (zeros + 1) (data true) ++ left := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa [configuration, List.replicate_succ, Nat.mul_add, Nat.add_assoc, commute]
      using Tape.Steps.next first (Tape.Steps.next second rest)

/-- Borrow stops at the first one and leaves the head on the remaining index bits. -/
theorem borrow_positive (zeros : ℕ) (tail : List Bool) (flag : Bool)
    (left right : List Symbol) :
    Steps (2 * zeros + 2)
      (configuration flag 6 left
        (word (List.replicate zeros false ++ true :: tail) ++ right))
      (configuration flag 9 (data false :: List.replicate zeros (data true) ++ left)
        (word tail ++ right)) := by
  have borrowPrefix := borrow_zeros zeros flag left (data true :: (word tail ++ right))
  have first := Tape.write (machine := machine) (state := (flag, 6)) (nextState := (flag, 8))
    (List.replicate zeros (data true) ++ left) (word tail ++ right) (data true) (data false) (by rfl)
  have second := Tape.move_right (machine := machine) (state := (flag, 8)) (nextState := (flag, 9))
    (List.replicate zeros (data true) ++ left) (word tail ++ right) (data false) (by rfl)
  simpa [word, configuration, List.map_append] using
    borrowPrefix.trans (Tape.Steps.next first (Tape.Steps.next second (.zero _)))

private theorem word_not_start (bits : List Bool) : (3 : Symbol) ∉ word bits := by
  intro member
  obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
  cases bit <;> simp [data] at equality

private theorem scan_word (flag : Bool) (phase : Fin 16)
    (allowed : phase = 3 ∨ phase = 9 ∨ phase = 13)
    (bits : List Bool) (left right : List Symbol) :
    Steps bits.length (configuration flag phase left (word bits ++ right))
      (configuration flag phase ((word bits).reverse ++ left) right) := by
  have trace := Tape.scan_right (machine := machine) (state := (flag, phase)) (word bits) left right
    (by
      intro symbol member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      rcases allowed with rfl | rfl | rfl <;> cases bit <;> rfl)
  simpa [configuration] using trace

private theorem rewind (flag : Bool) (phase : Fin 16) (allowed : phase = 5 ∨ phase = 12)
    (symbols left right : List Symbol) (current : Symbol)
    (safe : ∀ symbol ∈ current :: symbols, symbol ≠ 3) :
    Steps (symbols.length + 2)
      (configuration flag phase (symbols ++ 3 :: left) (current :: right))
      (configuration flag 6 (3 :: left) (symbols.reverse ++ current :: right)) := by
  have scan := Tape.scan_left (machine := machine) (state := (flag, phase)) symbols left right 3 current
    (by
      intro symbol member
      have distinct := safe symbol member
      rcases allowed with rfl | rfl <;> simp [machine, distinct])
  have back := Tape.move_right (machine := machine) (state := (flag, phase)) (nextState := (flag, 6))
    left (symbols.reverse ++ current :: right) 3
    (by rcases allowed with rfl | rfl <;> rfl)
  simpa [configuration, Nat.add_assoc] using scan.trans (Tape.Steps.next back (.zero _))

/-- One routing iteration advances the tuple cursor and decrements its binary
index. Unrelated storage on both sides is preserved. -/
theorem iteration (counter past suffix : List Bool) (old next replacement : Bool)
    (left right : List Symbol) (positive : 0 < Binary.value counter) :
    ∃ ticks, ticks ≤ 6 * (counter.length + past.length + suffix.length + 3) ∧
      Steps ticks
        (configuration replacement 6 (3 :: left)
          (word counter ++ 4 :: (word past ++ cursor old :: data next :: (word suffix ++ right))))
        (configuration replacement 6 (3 :: left)
          (word (Binary.decrement counter) ++ 4 ::
            (word (past ++ [old]) ++ cursor next :: (word suffix ++ right)))) := by
  obtain ⟨zeros, tail, rfl⟩ := Binary.positive_split counter positive
  let changed := List.replicate zeros true ++ false :: tail
  have borrow := borrow_positive zeros tail replacement (3 :: left)
    (4 :: (word past ++ cursor old :: data next :: (word suffix ++ right)))
  have tailScan := scan_word replacement 9 (by simp) tail
    (data false :: List.replicate zeros (data true) ++ (3 :: left))
    (4 :: (word past ++ cursor old :: data next :: (word suffix ++ right)))
  have delimiter := Tape.move_right (machine := machine) (state := (replacement, 9))
    (nextState := (replacement, 9))
    ((word tail).reverse ++ data false :: List.replicate zeros (data true) ++ (3 :: left))
    (word past ++ cursor old :: data next :: (word suffix ++ right)) 4 (by rfl)
  have pastScan := scan_word replacement 9 (by simp) past
    (4 :: ((word tail).reverse ++ data false :: List.replicate zeros (data true) ++ (3 :: left)))
    (cursor old :: data next :: (word suffix ++ right))
  simp only [List.append_assoc] at borrow tailScan delimiter pastScan
  have routed := borrow.trans (tailScan.trans (Tape.Steps.next delimiter pastScan))
  have routed' : Steps (2 * zeros + 2 + (tail.length + (past.length + 1)))
      (configuration replacement 6 (3 :: left)
        (word (List.replicate zeros false ++ true :: tail) ++ 4 ::
          (word past ++ cursor old :: data next :: (word suffix ++ right))))
      (configuration replacement 9 ((word past).reverse ++ 4 :: (word changed).reverse ++ (3 :: left))
        (cursor old :: data next :: (word suffix ++ right))) := by
    simpa [changed, word, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, configuration] using routed
  have unmark := Tape.write (machine := machine) (state := (replacement, 9))
    (nextState := (replacement, 10))
    ((word past).reverse ++ 4 :: (word changed).reverse ++ (3 :: left))
    (data next :: (word suffix ++ right)) (cursor old) (data old)
    (by cases old <;> rfl)
  have advance := Tape.move_right (machine := machine) (state := (replacement, 10))
    (nextState := (replacement, 11))
    ((word past).reverse ++ 4 :: (word changed).reverse ++ (3 :: left))
    (data next :: (word suffix ++ right)) (data old) (by rfl)
  have mark := Tape.write (machine := machine) (state := (replacement, 11))
    (nextState := (replacement, 12))
    (data old :: ((word past).reverse ++ 4 :: (word changed).reverse ++ (3 :: left)))
    (word suffix ++ right) (data next) (cursor next) (by cases next <;> rfl)
  let symbols := data old :: ((word past).reverse ++ 4 :: (word changed).reverse)
  have back := rewind replacement 12 (by simp) symbols left (word suffix ++ right) (cursor next)
    (by
      intro symbol member equality
      subst symbol
      cases next <;> cases old <;> simp [symbols, word_not_start, cursor, data] at member)
  have trace := routed'.trans (Tape.Steps.next unmark
    (Tape.Steps.next advance (Tape.Steps.next mark back)))
  have trace' : Steps
      (2 * zeros + 2 + (tail.length + (past.length + 1)) + (symbols.length + 2 + 1 + 1 + 1))
      (configuration replacement 6 (3 :: left)
        (word (List.replicate zeros false ++ true :: tail) ++ 4 ::
          (word past ++ cursor old :: data next :: (word suffix ++ right))))
      (configuration replacement 6 (3 :: left)
        (word (Binary.decrement (List.replicate zeros false ++ true :: tail)) ++ 4 ::
          (word (past ++ [old]) ++ cursor next :: (word suffix ++ right)))) := by
    simpa [configuration, symbols, changed, Binary.decrement_split, word,
      List.reverse_cons, List.reverse_append, List.reverse_reverse, List.append_assoc] using trace
  refine ⟨_, ?_, trace'⟩
  simp only [symbols, List.length_cons, List.length_append, List.length_reverse,
    word_length, changed, List.length_replicate]
  omega

/-- Exhaustion of the binary counter selects the current entry. The machine
writes the replacement, restores the cursor, and exposes old-bit/tuple output. -/
theorem finish (width : ℕ) (past suffix : List Bool) (old replacement : Bool)
    (left right : List Symbol) :
    Steps (2 * width + 2 * past.length + 4)
      (configuration replacement 6 (3 :: left)
        (List.replicate width (data false) ++ 4 ::
          (word past ++ cursor old :: (word suffix ++ right))))
      (configuration old 15 (List.replicate width (data true) ++ 3 :: left)
        (data old :: (word (past ++ replacement :: suffix) ++ right))) := by
  have borrow := borrow_zeros width replacement (3 :: left)
    (4 :: (word past ++ cursor old :: (word suffix ++ right)))
  have delimiter := Tape.move_right (machine := machine) (state := (replacement, 6))
    (nextState := (replacement, 13)) (List.replicate width (data true) ++ 3 :: left)
    (word past ++ cursor old :: (word suffix ++ right)) 4 (by rfl)
  have scan := scan_word replacement 13 (by simp) past
    (4 :: (List.replicate width (data true) ++ 3 :: left))
    (cursor old :: (word suffix ++ right))
  have replace := Tape.write (machine := machine) (state := (replacement, 13))
    (nextState := (old, 14))
    ((word past).reverse ++ 4 :: (List.replicate width (data true) ++ 3 :: left))
    (word suffix ++ right) (cursor old) (data replacement) (by cases old <;> rfl)
  have back := Tape.scan_left (machine := machine) (state := (old, 14)) (word past).reverse
    (List.replicate width (data true) ++ 3 :: left) (word suffix ++ right) 4 (data replacement)
    (by
      intro symbol member
      have distinct : symbol ≠ (4 : Symbol) := by
        intro equality
        subst symbol
        simp only [List.mem_cons, List.mem_reverse] at member
        rcases member with equality | member
        · cases replacement <;> simp [data] at equality
        · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
          cases bit <;> simp [data] at equality
      simp [machine, distinct])
  have output := Tape.write (machine := machine) (state := (old, 14))
    (nextState := (old, 15)) (List.replicate width (data true) ++ 3 :: left)
    (word past ++ data replacement :: (word suffix ++ right)) 4 (data old) (by rfl)
  simp only [List.reverse_reverse] at back
  have trace := borrow.trans (Tape.Steps.next delimiter (scan.trans
    (Tape.Steps.next replace (back.trans (Tape.Steps.next output (.zero _))))))
  simpa [configuration, word, List.append_assoc, Nat.add_assoc, Nat.two_mul,
    Nat.add_comm, Nat.add_left_comm] using trace

def marked : List Bool → List Symbol
  | [] => []
  | bit :: rest => cursor bit :: word rest

/-- Route to the indexed bit without changing any tuple entry. Only the
binary scratch counter and the cursor position change. -/
theorem route (counter past bits : List Bool) (flag : Bool)
    (left right : List Symbol) (valid : Binary.value counter < bits.length) :
    ∃ ticks before old after,
      bits = before ++ old :: after ∧ before.length = Binary.value counter ∧
      ticks ≤ Binary.value counter * (6 * (counter.length + past.length + bits.length + 1)) ∧
      Steps ticks
        (configuration flag 6 (3 :: left)
          (word counter ++ 4 :: (word past ++ marked bits ++ right)))
        (configuration flag 6 (3 :: left)
          (List.replicate counter.length (data false) ++ 4 ::
            (word (past ++ before) ++ cursor old :: (word after ++ right)))) := by
  induction bits generalizing counter past with
  | nil => simp at valid
  | cons old remaining hypothesis =>
    by_cases zero : Binary.value counter = 0
    · refine ⟨0, [], old, remaining, by simp, by simp [zero], by simp [zero], ?_⟩
      have packed : word counter = List.replicate counter.length (data false) := by
        simpa using congrArg word (Binary.zero_bits counter zero)
      simpa [marked, packed] using (Tape.Steps.zero (machine := machine)
        (configuration flag 6 (3 :: left)
          (word counter ++ 4 :: (word past ++ marked (old :: remaining) ++ right))))
    · have positive : 0 < Binary.value counter := by omega
      have decrease := Binary.decrement_value counter positive
      have nextValid : Binary.value (Binary.decrement counter) < remaining.length := by
        simp only [List.length_cons] at valid
        omega
      cases remaining with
      | nil => simp at nextValid
      | cons next suffix =>
        obtain ⟨firstTicks, firstBound, firstTrace⟩ :=
          iteration counter past suffix old next flag left right positive
        obtain ⟨restTicks, before, selected, after, decomposition, lengthEq, restBound, restTrace⟩ :=
          hypothesis (Binary.decrement counter) (past ++ [old]) nextValid
        refine ⟨firstTicks + restTicks, old :: before, selected, after, ?_, ?_, ?_, ?_⟩
        · simp [decomposition]
        · simp only [List.length_cons, lengthEq]
          omega
        · have firstBound' : firstTicks ≤
              6 * (counter.length + past.length + (old :: next :: suffix).length + 1) := by
            simpa [List.length_cons, Nat.add_assoc] using firstBound
          have restBound' : restTicks ≤ Binary.value (Binary.decrement counter) *
              (6 * (counter.length + past.length + (old :: next :: suffix).length + 1)) := by
            simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using restBound
          nlinarith
        · simp only [marked, List.cons_append, List.append_assoc] at restTrace
          simpa [marked, word, List.append_assoc, List.cons_append] using firstTrace.trans restTrace

/-- Polynomial routing, with the selected old bit and exactly one updated entry.
The bound is in the numeric index and physical frame length; valid tuple indices
make both polynomial in the declared tuple length. -/
theorem loop (counter past bits : List Bool) (replacement : Bool)
    (left right : List Symbol) (valid : Binary.value counter < bits.length) :
    ∃ ticks, ticks ≤ (Binary.value counter + 1) *
      (6 * (counter.length + past.length + bits.length + 1)) ∧
      Steps ticks
        (configuration replacement 6 (3 :: left)
          (word counter ++ 4 :: (word past ++ marked bits ++ right)))
        (configuration (bits.getD (Binary.value counter) false) 15
          (List.replicate counter.length (data true) ++ 3 :: left)
          (data (bits.getD (Binary.value counter) false) ::
            (word (past ++ bits.set (Binary.value counter) replacement) ++ right))) := by
  induction bits generalizing counter past with
  | nil => simp at valid
  | cons old remaining hypothesis =>
    by_cases zero : Binary.value counter = 0
    · have counterEq := Binary.zero_bits counter zero
      have packed : word counter = List.replicate counter.length (data false) := by
        simpa using congrArg word counterEq
      refine ⟨2 * counter.length + 2 * past.length + 4, ?_, ?_⟩
      · simp only [zero, zero_add, one_mul, List.length_cons]
        omega
      · simpa [zero, marked, packed] using
          finish counter.length past remaining old replacement left right
    · have positive : 0 < Binary.value counter := by omega
      have decrease := Binary.decrement_value counter positive
      have nextValid : Binary.value (Binary.decrement counter) < remaining.length := by
        simp only [List.length_cons] at valid
        omega
      cases remaining with
      | nil => simp at nextValid
      | cons next suffix =>
        obtain ⟨firstTicks, firstBound, firstTrace⟩ :=
          iteration counter past suffix old next replacement left right positive
        obtain ⟨restTicks, restBound, restTrace⟩ :=
          hypothesis (Binary.decrement counter) (past ++ [old]) nextValid
        have valueEq : Binary.value counter = Binary.value (Binary.decrement counter) + 1 :=
          decrease.symm
        simp only [marked, List.cons_append, List.append_assoc] at restTrace
        have trace := firstTrace.trans restTrace
        refine ⟨firstTicks + restTicks, ?_, ?_⟩
        · have restBound' : restTicks ≤ (Binary.value (Binary.decrement counter) + 1) *
              (6 * (counter.length + past.length + (old :: next :: suffix).length + 1)) := by
            simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using restBound
          have firstBound' : firstTicks ≤
              6 * (counter.length + past.length + (old :: next :: suffix).length + 1) := by
            simpa [List.length_cons, Nat.add_assoc] using firstBound
          calc
            firstTicks + restTicks ≤ _ := Nat.add_le_add firstBound' restBound'
            _ = _ := by rw [valueEq]; ring
        · simpa [marked, valueEq, List.getD_cons_succ, List.set_cons_succ,
            List.append_assoc, word, configuration] using trace

/-- Install the first-entry cursor when the counter start marker already exists. -/
theorem prepare_cursor (counter suffix : List Bool) (old replacement : Bool)
    (left right : List Symbol) :
    Steps (2 * counter.length + 6)
      (configuration replacement 2 left
        (3 :: (word counter ++ 4 :: data old :: (word suffix ++ right))))
      (configuration replacement 6 (3 :: left)
        (word counter ++ 4 :: (marked (old :: suffix) ++ right))) := by
  have enter := Tape.move_right (machine := machine) (state := (replacement, 2))
    (nextState := (replacement, 3)) left
    (word counter ++ 4 :: data old :: (word suffix ++ right)) 3 (by rfl)
  have scan := scan_word replacement 3 (by simp) counter (3 :: left)
    (4 :: data old :: (word suffix ++ right))
  have delimiter := Tape.move_right (machine := machine) (state := (replacement, 3))
    (nextState := (replacement, 4)) ((word counter).reverse ++ 3 :: left)
    (data old :: (word suffix ++ right)) 4 (by rfl)
  have mark := Tape.write (machine := machine) (state := (replacement, 4))
    (nextState := (replacement, 5)) (4 :: ((word counter).reverse ++ 3 :: left))
    (word suffix ++ right) (data old) (cursor old) (by cases old <;> rfl)
  have back := rewind replacement 5 (by simp) (4 :: (word counter).reverse) left
    (word suffix ++ right) (cursor old)
    (by
      intro symbol member equality
      subst symbol
      cases old <;> simp [word_not_start, cursor] at member)
  have trace := Tape.Steps.next enter
    (scan.trans (Tape.Steps.next delimiter (Tape.Steps.next mark back)))
  simpa [configuration, marked, List.append_assoc, Nat.two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using trace

/-- Preparation creates the start boundary and first-entry cursor from an
unmarked tuple. It does not assume that routing metadata has been supplied. -/
theorem prepare (counter suffix : List Bool) (old replacement : Bool)
    (left right : List Symbol) :
    Steps (2 * counter.length + 7)
      (configuration false 1 left
        (data replacement :: (word counter ++ 4 :: data old :: (word suffix ++ right))))
      (configuration replacement 6 (3 :: left)
        (word counter ++ 4 :: (marked (old :: suffix) ++ right))) := by
  have save := Tape.write (machine := machine) (state := (false, 1)) (nextState := (replacement, 2))
    left (word counter ++ 4 :: data old :: (word suffix ++ right)) (data replacement) 3
    (by cases replacement <;> rfl)
  simpa [configuration, Nat.add_assoc] using
    Tape.Steps.next save (prepare_cursor counter suffix old replacement left right)

/-- A reusable exchange contract on one prepared region. Both surrounding tape
contexts are preserved. Only the binary index scratch and this region change. -/
theorem exchange (counter bits : List Bool) (replacement : Bool)
    (left right : List Symbol) (valid : Binary.value counter < bits.length) :
    ∃ ticks, ticks ≤ 32 * (counter.length + bits.length + 1) ^ 2 ∧
      Steps ticks
        (configuration false 1 left
          (data replacement :: (word counter ++ 4 :: (word bits ++ right))))
        (configuration (bits.getD (Binary.value counter) false) 15
          (List.replicate counter.length (data true) ++ 3 :: left)
          (data (bits.getD (Binary.value counter) false) ::
            (word (bits.set (Binary.value counter) replacement) ++ right))) := by
  cases bits with
  | nil => simp at valid
  | cons old suffix =>
    have preparation := prepare counter suffix old replacement left right
    obtain ⟨ticks, bound, execution⟩ := loop counter [] (old :: suffix) replacement left right valid
    refine ⟨2 * counter.length + 7 + ticks, ?_, ?_⟩
    · simp only [List.length_nil, Nat.add_zero] at bound
      have indexBound := valid
      nlinarith [sq_nonneg (counter.length + (old :: suffix).length + 1)]
    · simpa [marked, word, List.append_assoc, configuration] using preparation.trans execution

/-- Self-delimiting unary size header, replacement bit, padded binary index,
a field separator, dense tuple bits, and end delimiter. This is an explicit
framed external serialization; no start/cursor metadata is present initially. -/
def input (bits : List Bool) (index : Fin bits.length) (replacement : Bool) : List Symbol :=
  List.replicate bits.length (data true) ++ data false :: data replacement ::
    (word (Binary.digits bits.length index.val) ++ 4 :: (word bits ++ [7]))

/-- The complete machine run, including header traversal and frame preparation.
The output is the selected bit followed by the updated dense tuple; the head
is on its first bit and all temporary cursor markers have been removed. -/
theorem realizes (bits : List Bool) (index : Fin bits.length) (replacement : Bool) :
    ∃ ticks, ticks ≤ 32 * (bits.length + 1) ^ 2 ∧
      Steps ticks (Turing.TM0.init (input bits index replacement))
        (configuration (bits.getD index.val false) 15
          (List.replicate bits.length (data true) ++ 3 :: data false ::
            List.replicate bits.length (data true))
          (data (bits.getD index.val false) :: (word (bits.set index.val replacement) ++ [7]))) := by
  have indexFits : index.val < 2 ^ bits.length := index.isLt.trans Nat.lt_two_pow_self
  have indexValue : Binary.value (Binary.digits bits.length index.val) = index.val := by
    simp [Nat.mod_eq_of_lt indexFits]
  have header := Tape.scan_right (machine := machine) (state := (false, 0))
    (List.replicate bits.length (data true)) []
    (data false :: data replacement ::
      (word (Binary.digits bits.length index.val) ++ 4 :: (word bits ++ [7])))
    (by intro symbol member; have equality := List.eq_of_mem_replicate member; subst symbol; rfl)
  have delimiter := Tape.move_right (machine := machine) (state := (false, 0))
    (nextState := (false, 1)) (List.replicate bits.length (data true))
    (data replacement :: (word (Binary.digits bits.length index.val) ++ 4 :: (word bits ++ [7])))
    (data false) (by rfl)
  cases bits with
  | nil => exact Fin.elim0 index
  | cons old suffix =>
    have preparation := prepare (Binary.digits (old :: suffix).length index.val) suffix old replacement
      (data false :: List.replicate (old :: suffix).length (data true)) [7]
    obtain ⟨loopTicks, loopBound, execution⟩ := loop
      (Binary.digits (old :: suffix).length index.val) [] (old :: suffix) replacement
      (data false :: List.replicate (old :: suffix).length (data true)) [7]
      (by rw [indexValue]; exact index.isLt)
    rw [indexValue] at loopBound execution
    simp only [List.reverse_replicate, List.append_nil, List.length_replicate] at header
    simp only [marked, word, List.nil_append, List.append_assoc] at preparation execution
    have trace := header.trans (Tape.Steps.next delimiter (preparation.trans execution))
    refine ⟨(old :: suffix).length +
      (2 * (Binary.digits (old :: suffix).length index.val).length + 7 + loopTicks + 1), ?_, ?_⟩
    · have bound : loopTicks ≤ (index.val + 1) * (6 * (2 * (old :: suffix).length + 1)) := by
        simpa only [Binary.digits_length, List.length_nil, Nat.add_zero, Nat.two_mul] using loopBound
      have indexBound := index.isLt
      simp only [Binary.digits_length]
      nlinarith
    · have initial : Turing.TM0.init (input (old :: suffix) index replacement) =
          configuration false 0 [] (input (old :: suffix) index replacement) := rfl
      rw [initial]
      simpa [input, configuration, word] using trace

@[simp] theorem halt (flag : Bool) (left right : List Symbol) :
    Turing.TM0.step machine (configuration flag 15 left right) = none := by
  simp [Turing.TM0.step, configuration, Tape.configuration, machine]

/-- Running with the proved polynomial budget returns the specified halted tape. -/
theorem run_realizes (bits : List Bool) (index : Fin bits.length) (replacement : Bool) :
    Tape.run machine (32 * (bits.length + 1) ^ 2) (Turing.TM0.init (input bits index replacement)) =
      some (configuration (bits.getD index.val false) 15
        (List.replicate bits.length (data true) ++ 3 :: data false ::
          List.replicate bits.length (data true))
        (data (bits.getD index.val false) :: (word (bits.set index.val replacement) ++ [7]))) := by
  obtain ⟨ticks, bound, trace⟩ := realizes bits index replacement
  exact Tape.run_of_steps trace (halt ..) bound

end Polytime1.TupleMachine
