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

import Polytime2.Wiring
import Polytime2.Binary

/-! # In-place binary scans with finite controller memory

The scan transforms each digit, then restores the head and preserves both
neighboring regions. Binary shifts reuse this scan's navigation proof.
-/

namespace Polytime2.BinaryScan

open MultiTape
open Binary (Symbol data word tape value)

-- memoryLevel: finite memory retained by the controller, never runtime storage.
universe memoryLevel
variable {Memory : Type memoryLevel}

abbrev Alphabet := fun _ : Unit => Symbol
abbrev State (Memory : Type memoryLevel) := Sum Memory (Memory × Bool)

def run (update : Memory → Bool → Memory × Bool) : Memory → List Bool → Memory × List Bool
  | memory, [] => (memory, [])
  | memory, bit :: bits =>
    let next := update memory bit
    let rest := run update next.1 bits
    (rest.1, next.2 :: rest.2)

@[simp] theorem run_length (update : Memory → Bool → Memory × Bool) (memory : Memory) (bits : List Bool) :
    (run update memory bits).2.length = bits.length := by
  induction bits generalizing memory with
  | nil => rfl
  | cons bit bits hypothesis => simpa only [run, List.length_cons] using congrArg Nat.succ (hypothesis _)

def machine (update : Memory → Bool → Memory × Bool) : Machine Alphabet (State Memory)
  | .inl memory, symbols =>
    if symbols () = 0 then some (.inr (memory, false), stationary symbols)
    else
      let next := update memory (symbols () == 2)
      some (.inl next.1, fun _ => (data next.2, some .right))
  | .inr (memory, finished), symbols =>
    if finished then none
    else if symbols () = 3 then some (.inr (memory, true), fun _ => (symbols (), some .right))
    else some (.inr (memory, false), fun _ => (symbols (), some .left))

private theorem forward (update : Memory → Bool → Memory × Bool) (memory : Memory)
    (bits : List Bool) (left right : List Symbol) :
    Steps (machine update) bits.length
      (.inl memory, tape left (word bits ++ right))
      (.inl (run update memory bits).1, tape ((word (run update memory bits).2).reverse ++ left) right) := by
  induction bits generalizing memory left with
  | nil => simpa [run, word] using Steps.zero (machine := machine update) (.inl memory, tape left right)
  | cons bit bits hypothesis =>
    have first : step (machine update) (.inl memory, tape left (word (bit :: bits) ++ right)) =
        some (.inl (update memory bit).1, tape (data (update memory bit).2 :: left) (word bits ++ right)) := by
      have nonblank : data bit ≠ 0 := by cases bit <;> decide
      have digit : (data bit == 2) = bit := by cases bit <;> decide
      simp only [step, machine, MultiTape.read, tape, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank, ↓reduceIte,
        digit, Option.map_some]
      congr 2
    have rest := hypothesis (update memory bit).1 (data (update memory bit).2 :: left)
    simpa [run, word, List.reverse_cons, List.append_assoc] using Steps.next first rest

private theorem rewind (update : Memory → Bool → Memory × Bool) (memory : Memory)
    (bits : List Bool) (current : Symbol) (nonboundary : current ≠ 3) (left right : List Symbol) :
    Steps (machine update) (bits.length + 2)
      (.inr (memory, false), tape (word bits ++ 3 :: left) (current :: right))
      (.inr (memory, true), tape (3 :: left) ((word bits).reverse ++ current :: right)) := by
  induction bits generalizing current right with
  | nil =>
    have first : step (machine update) (.inr (memory, false), tape (3 :: left) (current :: right)) =
        some (.inr (memory, false), tape left (3 :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, nonboundary, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
    have second : step (machine update) (.inr (memory, false), tape left (3 :: current :: right)) =
        some (.inr (memory, true), tape (3 :: left) (current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    have first : step (machine update)
        (.inr (memory, false), tape (word (bit :: bits) ++ 3 :: left) (current :: right)) =
        some (.inr (memory, false), tape (word bits ++ 3 :: left) (data bit :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, nonboundary, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
    have dataNotBoundary : data bit ≠ 3 := by cases bit <;> decide
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Steps.next first (hypothesis (data bit) dataNotBoundary (current :: right))

/-- Exact linear runtime, with the final finite memory retained at exit. -/
theorem steps (update : Memory → Bool → Memory × Bool) (memory : Memory)
    (bits : List Bool) (left right : List Symbol) :
    Steps (machine update) (2 * bits.length + 3)
      (.inl memory, tape (3 :: left) (word bits ++ 0 :: right))
      (.inr ((run update memory bits).1, true),
        tape (3 :: left) (word (run update memory bits).2 ++ 0 :: right)) := by
  have scanned := forward update memory bits (3 :: left) (0 :: right)
  have finish : step (machine update)
      (.inl (run update memory bits).1, tape ((word (run update memory bits).2).reverse ++ 3 :: left) (0 :: right)) =
      some (.inr ((run update memory bits).1, false),
        tape ((word (run update memory bits).2).reverse ++ 3 :: left) (0 :: right)) := by
    simp [step, machine, MultiTape.read, tape]
  have restored := rewind update (run update memory bits).1 (run update memory bits).2.reverse
    0 (by decide) left right
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse,
    run_length] at scanned restored finish ⊢
  convert scanned.trans (Steps.next finish restored) using 1
  omega

/-- Shift toward higher binary places, retaining the discarded high bit. -/
def shift (previous bit : Bool) : Bool × Bool := (bit, previous)

/-- Clear an existing digit region without changing its capacity. -/
def clear (_memory : Unit) (_bit : Bool) : Unit × Bool := ((), false)

@[simp] theorem clear_run (bits : List Bool) : run clear () bits = ((), List.replicate bits.length false) := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => simp [run, clear, hypothesis, List.replicate_succ]

theorem shift_equation (previous : Bool) (bits : List Bool) :
    value (run shift previous bits).2 + 2 ^ bits.length * (run shift previous bits).1.toNat =
      previous.toNat + 2 * value bits := by
  induction bits generalizing previous with
  | nil => simp [run, value]
  | cons bit bits hypothesis =>
    have rest := hypothesis bit
    simp only [run, shift, value, List.length_cons, pow_succ]
    nlinarith

/-- In the absence of overflow, the shift computes exactly `2*x + bit`. -/
theorem shift_value (previous : Bool) (bits : List Bool)
    (fits : previous.toNat + 2 * value bits < 2 ^ bits.length) :
    value (run shift previous bits).2 = previous.toNat + 2 * value bits ∧
      (run shift previous bits).1 = false := by
  have equation := shift_equation previous bits
  cases last : (run shift previous bits).1 with
  | false =>
    simp only [last, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at equation
    exact ⟨equation, rfl⟩
  | true =>
    simp only [last, Bool.toNat_true, Nat.mul_one] at equation
    omega

end Polytime2.BinaryScan
