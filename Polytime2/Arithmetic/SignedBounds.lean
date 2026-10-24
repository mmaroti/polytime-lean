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

import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! # Derived magnitude bounds for signed arithmetic -/

namespace Polytime2.IntegerArithmetic

/-- Independent operand widths bound a multiply-add by the larger summand width. -/
theorem multiplyAdd_bound_of_three_widths (firstWidth coefficientWidth secondWidth : ℕ)
    (first coefficient second : ℤ) (firstBound : first.natAbs < 2 ^ firstWidth)
    (coefficientBound : coefficient.natAbs < 2 ^ coefficientWidth)
    (secondBound : second.natAbs < 2 ^ secondWidth) :
    (first + coefficient * second).natAbs <
      2 ^ (max firstWidth (coefficientWidth + secondWidth) + 1) := by
  have productBound := Nat.mul_lt_mul'' coefficientBound secondBound
  rw [← pow_add] at productBound
  have firstLe : 2 ^ firstWidth ≤ 2 ^ max firstWidth (coefficientWidth + secondWidth) :=
    pow_le_pow_right₀ (by decide) (le_max_left _ _)
  have productLe : 2 ^ (coefficientWidth + secondWidth) ≤
      2 ^ max firstWidth (coefficientWidth + secondWidth) :=
    pow_le_pow_right₀ (by decide) (le_max_right _ _)
  have sumBound := Int.natAbs_add_le first (coefficient * second)
  rw [Int.natAbs_mul] at sumBound
  rw [pow_succ]
  omega

/-- A multiply-add accepts independent coefficient and value widths. -/
theorem multiplyAdd_bound_of_widths (coefficientWidth valueWidth : ℕ) (first coefficient second : ℤ)
    (firstBound : first.natAbs < 2 ^ valueWidth)
    (coefficientBound : coefficient.natAbs < 2 ^ coefficientWidth)
    (secondBound : second.natAbs < 2 ^ valueWidth) :
    (first + coefficient * second).natAbs < 2 ^ (coefficientWidth + valueWidth + 1) := by
  simpa only [max_eq_right (Nat.le_add_left valueWidth coefficientWidth)] using
    multiplyAdd_bound_of_three_widths valueWidth coefficientWidth valueWidth first coefficient second
      firstBound coefficientBound secondBound

/-- A common input word bound specializes the independent-width bound. -/
theorem multiplyAdd_bound (width : ℕ) (first coefficient second : ℤ)
    (firstBound : first.natAbs < 2 ^ width)
    (coefficientBound : coefficient.natAbs < 2 ^ width)
    (secondBound : second.natAbs < 2 ^ width) :
    (first + coefficient * second).natAbs < 2 ^ (2 * width + 1) := by
  simpa only [two_mul] using multiplyAdd_bound_of_widths width width first coefficient second
    firstBound coefficientBound secondBound


/-- A two-term integer linear combination has a linear derived magnitude width. -/
theorem twoProducts_bound_of_widths (coefficientWidth valueWidth : ℕ) (first firstValue second secondValue : ℤ)
    (firstBound : first.natAbs < 2 ^ coefficientWidth) (firstValueBound : firstValue.natAbs < 2 ^ valueWidth)
    (secondBound : second.natAbs < 2 ^ coefficientWidth) (secondValueBound : secondValue.natAbs < 2 ^ valueWidth) :
    (first * firstValue + second * secondValue).natAbs < 2 ^ (coefficientWidth + valueWidth + 1) := by
  have firstProduct := Nat.mul_lt_mul'' firstBound firstValueBound
  have secondProduct := Nat.mul_lt_mul'' secondBound secondValueBound
  have sumBound := Int.natAbs_add_le (first * firstValue) (second * secondValue)
  simp only [Int.natAbs_mul] at sumBound
  rw [pow_succ, pow_add]
  omega

/-- The common-width specialization reuses the heterogeneous bound. -/
theorem twoProducts_bound (width : ℕ) (first firstValue second secondValue : ℤ)
    (firstBound : first.natAbs < 2 ^ width) (firstValueBound : firstValue.natAbs < 2 ^ width)
    (secondBound : second.natAbs < 2 ^ width) (secondValueBound : secondValue.natAbs < 2 ^ width) :
    (first * firstValue + second * secondValue).natAbs < 2 ^ (2 * width + 1) := by
  simpa only [two_mul] using twoProducts_bound_of_widths width width _ _ _ _
    firstBound firstValueBound secondBound secondValueBound

end Polytime2.IntegerArithmetic
