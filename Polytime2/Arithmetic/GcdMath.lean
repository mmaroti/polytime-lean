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

import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-! # Euclidean gcd with a bit-length progress measure

One Euclidean reduction forms a logical step. A bit-length measure counts both
operands and a possible initial swap, so the iteration bound depends on binary
capacity rather than numeric magnitude.
-/

namespace Polytime2.Gcd

/-- Working operands; capacities and physical scratch belong to representations. -/
abbrev Value := ℕ × ℕ

def condition (value : Value) : Bool := decide (value.2 ≠ 0)

def advance (value : Value) : Value := (value.2, value.1 % value.2)

def answer (value : Value) : ℕ := Nat.gcd value.1 value.2

def measure (value : Value) : ℕ :=
  Nat.size value.1 + Nat.size value.2 + if value.1 < value.2 then 1 else 0

/-- When no initial swap is needed, a remainder loses at least one digit. -/
theorem remainder_half (left right : ℕ) (positive : 0 < right) (ordered : right ≤ left) :
    2 * (left % right) < left := by
  by_cases small : 2 * right ≤ left
  · have bounded := Nat.mod_lt left positive
    omega
  · have quotientOne : left / right = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have identity := Nat.mod_add_div left right
    rw [quotientOne] at identity
    omega

/-- Halving a nonzero natural removes exactly one magnitude bit. -/
theorem size_half (number : ℕ) (nonzero : number ≠ 0) :
    Nat.size (number / 2) + 1 = Nat.size number := by
  induction number using Nat.binaryRec' with
  | zero => contradiction
  | bit bit rest nonzeroBit _ =>
    rw [Nat.bit_div_two, Nat.size_bit (Nat.bit_ne_zero_iff.mpr nonzeroBit)]

/-- Progress is measured in bits, including a possible initial operand swap. -/
theorem decreases (value : Value) (active : condition value = true) :
    measure (advance value) < measure value := by
  have positive : 0 < value.2 := by simpa [condition, Nat.pos_iff_ne_zero] using active
  have remainderBound := Nat.mod_lt value.1 positive
  by_cases swapped : value.1 < value.2
  · simp only [measure, advance, Nat.mod_eq_of_lt swapped, swapped, ↓reduceIte]
    have reverse : ¬value.2 < value.1 := by omega
    simp only [reverse, ↓reduceIte]
    omega
  · have ordered : value.2 ≤ value.1 := by omega
    have firstPositive : 0 < value.1 := by omega
    have halved := remainder_half value.1 value.2 positive ordered
    have sizeBound := Nat.size_le_size (show value.1 % value.2 ≤ value.1 / 2 by omega)
    have halvedSize := size_half value.1 (Nat.ne_of_gt firstPositive)
    have smaller : Nat.size (value.1 % value.2) < Nat.size value.1 := by omega
    have reverse : ¬value.2 < value.1 % value.2 := by omega
    simp only [measure, advance, swapped, reverse, ↓reduceIte]
    omega

/-- One Euclidean reduction preserves the mathematical gcd. -/
theorem conserves (value : Value) : answer (advance value) = answer value := by
  exact (Nat.gcd_comm _ _).trans ((Nat.gcd_rec value.2 value.1).symm.trans (Nat.gcd_comm _ _))

/-- At the stopping state the first operand is the gcd. -/
theorem terminal (value : Value) (stopped : condition value = false) : answer value = value.1 := by
  have zero : value.2 = 0 := by simpa [condition] using stopped
  simp [answer, zero]

/-- Both operands remain within the original binary capacity. -/
theorem preserves (bits : ℕ) (value : Value)
    (bounded : value.1 < 2 ^ bits ∧ value.2 < 2 ^ bits)
    (active : condition value = true) :
    (advance value).1 < 2 ^ bits ∧ (advance value).2 < 2 ^ bits := by
  have positive : 0 < value.2 := by simpa [condition, Nat.pos_iff_ne_zero] using active
  have remainderBound := Nat.mod_lt value.1 positive
  exact ⟨bounded.2, remainderBound.trans bounded.2⟩

/-- The loop measure is bounded by twice the binary capacity plus one. -/
theorem measure_bound (bits : ℕ) (value : Value)
    (bounded : value.1 < 2 ^ bits ∧ value.2 < 2 ^ bits) :
    measure value ≤ 2 * bits + 1 := by
  have first := Nat.size_le.mpr bounded.1
  have second := Nat.size_le.mpr bounded.2
  unfold measure
  split <;> omega

/-- Executable mathematical gcd; the stopping guard determines execution. -/
def run (value : Value) : ℕ :=
  if _active : condition value = true then run (advance value) else value.1
termination_by measure value
decreasing_by exact decreases value _active

theorem run_correct (value : Value) : run value = answer value := by
  rw [run]
  split
  · rw [run_correct (advance value), conserves]
  · rename_i stopped
    exact (terminal value (by cases tested : condition value <;> simp_all)).symm
termination_by measure value
decreasing_by exact decreases value (by assumption)

/-- Number of logical iterations, each containing one remainder call. -/
def iterations (value : Value) : ℕ :=
  if active : condition value = true then iterations (advance value) + 1 else 0
termination_by measure value
decreasing_by exact decreases value active

theorem iterations_bound (value : Value) : iterations value ≤ measure value := by
  rw [iterations]
  split
  · rename_i active
    have rest := iterations_bound (advance value)
    have progress := decreases value active
    omega
  · exact Nat.zero_le _
termination_by measure value
decreasing_by exact decreases value (by assumption)

theorem iterations_capacity (bits : ℕ) (value : Value)
    (bounded : value.1 < 2 ^ bits ∧ value.2 < 2 ^ bits) :
    iterations value ≤ 2 * bits + 1 := (iterations_bound value).trans (measure_bound bits value bounded)

end Polytime2.Gcd
