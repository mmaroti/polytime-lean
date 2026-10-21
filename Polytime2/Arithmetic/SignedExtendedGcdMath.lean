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

import Polytime2.Arithmetic.GcdMath
import Mathlib.Data.Int.GCD

/-! # Extended Euclid with polynomial coefficient capacities

The mathematical input is a pair of natural remainders and two integer
coefficient rows. Each row expresses its remainder as a linear combination of
the original signed inputs. Euclidean reduction preserves those identities and
returns a nonnegative gcd together with actual Bézout coefficients.

A bit-length progress measure bounds the number of steps. The coefficient
capacity is derived from the input magnitude width, including `(0,0)`; no
numeric-magnitude iteration bound or unit-cost integer arithmetic is assumed.
-/

namespace Polytime2.ExtendedGcd

/-- Remainders and their two ordinary mathematical coefficient rows. -/
abbrev Value := (ℕ × ℕ) × ((ℤ × ℤ) × (ℤ × ℤ))

def advance (value : Value) : Value :=
  let quotient : ℤ := (value.1.1 / value.1.2 : ℕ)
  ((value.1.2, value.1.1 % value.1.2),
    (value.2.2, (value.2.1.1 - quotient * value.2.2.1,
      value.2.1.2 - quotient * value.2.2.2)))

def run (value : Value) : Value :=
  if _active : Gcd.condition value.1 = true then run (advance value) else value
termination_by Gcd.measure value.1
decreasing_by exact Gcd.decreases value.1 _active

theorem run_step (value : Value) (active : Gcd.condition value.1 = true) :
    run (advance value) = run value := by
  conv_rhs => rw [run]
  simp only [active, ↓reduceDIte]

theorem run_gcd (value : Value) : (run value).1.1 = Nat.gcd value.1.1 value.1.2 := by
  rw [run]
  split
  · rw [run_gcd (advance value)]
    exact Gcd.conserves value.1
  · rename_i stopped
    have zero : value.1.2 = 0 := by simpa [Gcd.condition] using stopped
    simp [zero]
termination_by Gcd.measure value.1
decreasing_by exact Gcd.decreases value.1 (by assumption)

/-- Both remainder rows represent the same fixed pair of mathematical inputs. -/
def represents (left right : ℤ) (value : Value) : Prop :=
  value.2.1.1 * left + value.2.1.2 * right = value.1.1 ∧
    value.2.2.1 * left + value.2.2.2 * right = value.1.2

theorem advance_represents (left right : ℤ) (value : Value) (valid : represents left right value) :
    represents left right (advance value) := by
  refine ⟨valid.2, ?_⟩
  have division := Nat.mod_add_div value.1.1 value.1.2
  have identity : ((value.1.1 % value.1.2 : ℕ) : ℤ) +
      (value.1.2 : ℤ) * (value.1.1 / value.1.2 : ℕ) = value.1.1 := by
    exact_mod_cast division
  dsimp only [advance]
  calc
    _ = (value.2.1.1 * left + value.2.1.2 * right) -
        (value.1.1 / value.1.2 : ℕ) * (value.2.2.1 * left + value.2.2.2 * right) := by ring
    _ = (value.1.1 : ℤ) - (value.1.1 / value.1.2 : ℕ) * (value.1.2 : ℤ) := by rw [valid.1, valid.2]
    _ = ((value.1.1 % value.1.2 : ℕ) : ℤ) := by linarith

theorem run_represents (left right : ℤ) (value : Value) (valid : represents left right value) :
    represents left right (run value) := by
  rw [run]
  split
  · exact run_represents left right (advance value) (advance_represents left right value valid)
  · exact valid
termination_by Gcd.measure value.1
decreasing_by exact Gcd.decreases value.1 (by assumption)

/-- One coefficient update increases its bit bound by at most `width+1`. -/
theorem coefficient_step_bound (width exponent quotient : ℕ) (left right : ℤ)
    (quotientBound : quotient < 2 ^ width)
    (leftBound : left.natAbs < 2 ^ exponent) (rightBound : right.natAbs < 2 ^ exponent) :
    (left - (quotient : ℤ) * right).natAbs < 2 ^ (exponent + (width + 1)) := by
  have triangle := Int.natAbs_sub_le left ((quotient : ℤ) * right)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at triangle
  have product := Nat.mul_le_mul_left quotient rightBound.le
  have factor : quotient + 1 ≤ 2 ^ (width + 1) := by
    rw [pow_succ]
    omega
  have expanded : 2 ^ (exponent + (width + 1)) = 2 ^ exponent * 2 ^ (width + 1) := pow_add _ _ _
  rw [expanded]
  have scaled := Nat.mul_le_mul_left (2 ^ exponent) factor
  nlinarith

/-- Every stored coefficient obeys one common magnitude bound. -/
def coefficientsBounded (exponent : ℕ) (value : Value) : Prop :=
  value.2.1.1.natAbs < 2 ^ exponent ∧ value.2.1.2.natAbs < 2 ^ exponent ∧
    value.2.2.1.natAbs < 2 ^ exponent ∧ value.2.2.2.natAbs < 2 ^ exponent

theorem advance_coefficientsBounded (width exponent : ℕ) (value : Value)
    (firstBound : value.1.1 < 2 ^ width) (bounded : coefficientsBounded exponent value) :
    coefficientsBounded (exponent + (width + 1)) (advance value) := by
  have quotientBound := (Nat.div_le_self value.1.1 value.1.2).trans_lt firstBound
  have monotone : 2 ^ exponent ≤ 2 ^ (exponent + (width + 1)) :=
    pow_le_pow_right₀ (by decide) (by omega)
  exact ⟨bounded.2.2.1.trans_le monotone, bounded.2.2.2.trans_le monotone,
    coefficient_step_bound width exponent _ _ _ quotientBound bounded.1 bounded.2.2.1,
    coefficient_step_bound width exponent _ _ _ quotientBound bounded.2.1 bounded.2.2.2⟩

/-- Available coefficient bits grow with the consumed Euclidean bit measure. -/
def exponent (width : ℕ) (value : Value) : ℕ :=
  (2 * width + 1 - Gcd.measure value.1) * (width + 1) + 1

def admissible (width : ℕ) (value : Value) : Prop :=
  (value.1.1 < 2 ^ width ∧ value.1.2 < 2 ^ width) ∧
    coefficientsBounded (exponent width value) value

theorem advance_admissible (width : ℕ) (value : Value) (valid : admissible width value)
    (active : Gcd.condition value.1 = true) : admissible width (advance value) := by
  have smaller := Gcd.decreases value.1 active
  have measureBound := Gcd.measure_bound width value.1 valid.1
  have coefficientBound := advance_coefficientsBounded width (exponent width value) value valid.1.1 valid.2
  have growth : exponent width value + (width + 1) ≤ exponent width (advance value) := by
    change (2 * width + 1 - Gcd.measure value.1) * (width + 1) + 1 + (width + 1) ≤
      (2 * width + 1 - Gcd.measure (Gcd.advance value.1)) * (width + 1) + 1
    have gap : 2 * width + 1 - Gcd.measure value.1 + 1 ≤
        2 * width + 1 - Gcd.measure (Gcd.advance value.1) := by omega
    have product := Nat.mul_le_mul_right (width + 1) gap
    nlinarith
  have powerBound : 2 ^ (exponent width value + (width + 1)) ≤ 2 ^ exponent width (advance value) :=
    pow_le_pow_right₀ (by decide) growth
  exact ⟨Gcd.preserves width value.1 valid.1 active,
    coefficientBound.1.trans_le powerBound, coefficientBound.2.1.trans_le powerBound,
    coefficientBound.2.2.1.trans_le powerBound, coefficientBound.2.2.2.trans_le powerBound⟩

theorem run_admissible (width : ℕ) (value : Value) (valid : admissible width value) :
    admissible width (run value) := by
  rw [run]
  split
  · exact run_admissible width (advance value) (advance_admissible width value valid (by assumption))
  · exact valid
termination_by Gcd.measure value.1
decreasing_by exact Gcd.decreases value.1 (by assumption)

/-- A polynomial bit capacity covers all live and final coefficient rows. -/
def coefficientWidth (width : ℕ) : ℕ := (2 * width + 1) * (width + 1) + 1

theorem coefficient_capacity (width : ℕ) (value : Value) (valid : admissible width value) :
    coefficientsBounded (coefficientWidth width) value := by
  have bound : exponent width value ≤ coefficientWidth width := by
    dsimp [exponent, coefficientWidth]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) 1
  have powerBound : 2 ^ exponent width value ≤ 2 ^ coefficientWidth width := pow_le_pow_right₀ (by decide) bound
  exact ⟨valid.2.1.trans_le powerBound, valid.2.2.1.trans_le powerBound,
    valid.2.2.2.1.trans_le powerBound, valid.2.2.2.2.trans_le powerBound⟩

/-- Initialize the coefficient rows directly from the signs of signed inputs. -/
def initial (left right : ℤ) : Value :=
  ((left.natAbs, right.natAbs), ((left.sign, 0), (0, right.sign)))

theorem initial_represents (left right : ℤ) : represents left right (initial left right) := by
  simp [represents, initial]

theorem initial_admissible (width : ℕ) (left right : ℤ)
    (leftBound : left.natAbs < 2 ^ width) (rightBound : right.natAbs < 2 ^ width) :
    admissible width (initial left right) := by
  have positive : 1 ≤ exponent width (initial left right) := by dsimp [exponent]; omega
  have two : 2 ≤ 2 ^ exponent width (initial left right) := by
    exact (show 2 ^ 1 ≤ 2 ^ exponent width (initial left right) from pow_le_pow_right₀ (by decide) positive)
  have signBound (value : ℤ) : value.sign.natAbs < 2 ^ exponent width (initial left right) := by
    rw [Int.natAbs_sign]
    split <;> omega
  exact ⟨⟨leftBound, rightBound⟩, signBound left, by simp [initial], by simp [initial], signBound right⟩

/-- The actual mathematical output contains a gcd and two Bézout coefficients. -/
def result (left right : ℤ) : ℕ × ℤ × ℤ :=
  let final := run (initial left right)
  (final.1.1, final.2.1)

theorem result_correct (left right : ℤ) :
    (result left right).1 = Int.gcd left right ∧
      (result left right).2.1 * left + (result left right).2.2 * right = (result left right).1 := by
  exact ⟨run_gcd (initial left right),
    (run_represents left right (initial left right) (initial_represents left right)).1⟩

theorem result_bounds (width : ℕ) (left right : ℤ)
    (leftBound : left.natAbs < 2 ^ width) (rightBound : right.natAbs < 2 ^ width) :
    (result left right).1 < 2 ^ width ∧
      (result left right).2.1.natAbs < 2 ^ coefficientWidth width ∧
      (result left right).2.2.natAbs < 2 ^ coefficientWidth width := by
  have valid := run_admissible width (initial left right) (initial_admissible width left right leftBound rightBound)
  have coefficients := coefficient_capacity width (run (initial left right)) valid
  exact ⟨valid.1.1, coefficients.1, coefficients.2.1⟩

end Polytime2.ExtendedGcd
