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

import Polytime2.Binary

/-! # Mathematical binary scans with finite memory

These digit folds describe the standard separate-input/output scan controllers.
Binary shifting and clearing reuse the same mathematical recurrence.
-/

namespace Polytime2.BinaryScan

open Binary (value)

-- memoryLevel: finite memory retained by the controller, never runtime storage.
universe memoryLevel
variable {Memory : Type memoryLevel}

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

/-- Add a carry to one binary digit, retaining any carry for the next digit. -/
def increment (carry bit : Bool) : Bool × Bool := (carry && bit, carry != bit)

/-- Fixed-width increment retains the discarded carry in finite control. -/
theorem increment_equation (carry : Bool) (bits : List Bool) :
    value (run increment carry bits).2 + 2 ^ bits.length * (run increment carry bits).1.toNat =
      carry.toNat + value bits := by
  induction bits generalizing carry with
  | nil => simp [run, value]
  | cons bit bits hypothesis =>
    have rest := hypothesis (carry && bit)
    cases carry <;> cases bit <;>
      simp [run, increment, value, pow_succ] at rest ⊢ <;> nlinarith

/-- Increment is modular in the word's fixed capacity, including width zero. -/
theorem increment_value (bits : List Bool) :
    value (run increment true bits).2 = (value bits + 1) % 2 ^ bits.length := by
  have equation := congrArg (fun number => number % 2 ^ bits.length) (increment_equation true bits)
  have bounded : value (run increment true bits).2 < 2 ^ bits.length := by
    simpa using Binary.value_lt_pow_length (run increment true bits).2
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt bounded, Nat.add_comm] using equation

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
