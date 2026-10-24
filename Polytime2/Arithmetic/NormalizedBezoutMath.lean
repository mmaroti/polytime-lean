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

import Polytime2.Arithmetic.SignedExtendedGcdMath
import Polytime2.Arithmetic.SignedBounds

/-! # Normalized Bézout coefficients for integer matrix elimination

For integers `a,b`, return actual coefficients `x,y` with `a*x+b*y=gcd(a,b)`.
When `b` is nonzero, reduce `x` modulo `b/gcd(a,b)` and recover `y` by exact
integer division. This reuses the existing extended Euclidean computation,
while bounding the returned coefficient widths linearly in the input width.
The zero pair returns `(1,0)`, suitable for an identity matrix operation.
-/

namespace Polytime2.ExtendedGcd

private theorem normalized_numerator_dvd (first second : ℤ) :
    second ∣ (Int.gcd first second : ℤ) -
      first * ((result first second).2.1 % (second / (Int.gcd first second : ℤ))) := by
  let divisor : ℤ := Int.gcd first second
  let left := (result first second).2.1
  let right := (result first second).2.2
  have bezout : left * first + right * second = divisor := by
    have correct := (result_correct first second).2
    rw [(result_correct first second).1] at correct
    exact correct
  have firstExact : first / divisor * divisor = first :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
  have secondExact : second / divisor * divisor = second :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
  have cross : first * (second / divisor) = second * (first / divisor) := by
    calc
      first * (second / divisor) = (first / divisor * divisor) * (second / divisor) := by rw [firstExact]
      _ = (second / divisor * divisor) * (first / divisor) := by ring
      _ = second * (first / divisor) := by rw [secondExact]
  have division : left - left % (second / divisor) = (second / divisor) * (left / (second / divisor)) := by
    have identity := Int.emod_add_mul_ediv left (second / divisor)
    omega
  refine ⟨(first / divisor) * (left / (second / divisor)) + right, ?_⟩
  change divisor - first * (left % (second / divisor)) = _
  calc
    _ = first * (left - left % (second / divisor)) + second * right := by nlinarith [bezout]
    _ = first * ((second / divisor) * (left / (second / divisor))) + second * right := by rw [division]
    _ = second * ((first / divisor) * (left / (second / divisor)) + right) := by
      linear_combination (left / (second / divisor)) * cross

/-- Normalize a certified extended-gcd result for a bounded matrix operation. -/
def normalizedCoefficients (first second : ℤ) : ℤ × ℤ :=
  if second = 0 then (if first = 0 then 1 else first.sign, 0)
  else
    let divisor : ℤ := Int.gcd first second
    let left := (result first second).2.1 % (second / divisor)
    (left, (divisor - first * left) / second)

theorem normalizedCoefficients_correct (first second : ℤ) :
    first * (normalizedCoefficients first second).1 +
      second * (normalizedCoefficients first second).2 = Int.gcd first second := by
  unfold normalizedCoefficients
  split
  · rename_i zero
    subst second
    by_cases firstZero : first = 0
    · simp [firstZero]
    · simp [firstZero, Int.mul_sign_self]
  · dsimp only
    rw [Int.mul_ediv_cancel' (normalized_numerator_dvd first second)]
    ring


theorem gcd_quotient_ne_zero_right (first second : ℤ) (nonzero : second ≠ 0) :
    second / (Int.gcd first second : ℤ) ≠ 0 := by
  intro zero
  have exactSecond := Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
  rw [zero, zero_mul] at exactSecond
  exact nonzero exactSecond.symm

theorem normalized_remainder_bound (width : ℕ) (first second : ℤ)
    (secondBound : second.natAbs < 2 ^ width) (nonzero : second ≠ 0) :
    ((result first second).2.1 % (second / (Int.gcd first second : ℤ))).natAbs < 2 ^ width := by
  have quotientNonzero := gcd_quotient_ne_zero_right first second nonzero
  have remainderSmall : ((result first second).2.1 % (second / (Int.gcd first second : ℤ))).natAbs <
      (second / (Int.gcd first second : ℤ)).natAbs := by
    have nonnegative := Int.emod_nonneg (result first second).2.1 quotientNonzero
    have small := Int.emod_lt (result first second).2.1 quotientNonzero
    have represented := Int.natAbs_of_nonneg nonnegative
    omega
  exact remainderSmall.trans_le ((Int.natAbs_ediv_le_natAbs _ _).trans secondBound.le)

theorem normalized_numerator_bound (width : ℕ) (first second : ℤ)
    (firstBound : first.natAbs < 2 ^ width) (secondBound : second.natAbs < 2 ^ width)
    (nonzero : second ≠ 0) :
    ((Int.gcd first second : ℤ) - first *
      ((result first second).2.1 % (second / (Int.gcd first second : ℤ)))).natAbs < 2 ^ (2 * width + 1) := by
  have gcdBound : (Int.gcd first second : ℤ).natAbs < 2 ^ width := by
    simpa only [(result_correct first second).1, Int.natAbs_natCast] using
      (result_bounds width first second firstBound secondBound).1
  simpa only [sub_eq_add_neg, neg_mul] using
    IntegerArithmetic.multiplyAdd_bound width (Int.gcd first second : ℤ) (-first)
      ((result first second).2.1 % (second / (Int.gcd first second : ℤ))) gcdBound
      (by simpa using firstBound) (normalized_remainder_bound width first second secondBound nonzero)

/-- The returned coefficients need only a linear derived magnitude width. -/
theorem normalizedCoefficients_bound (width : ℕ) (first second : ℤ)
    (firstBound : first.natAbs < 2 ^ width) (secondBound : second.natAbs < 2 ^ width) :
    (normalizedCoefficients first second).1.natAbs < 2 ^ (2 * width + 1) ∧
      (normalizedCoefficients first second).2.natAbs < 2 ^ (2 * width + 1) := by
  unfold normalizedCoefficients
  split
  · by_cases zero : first = 0
    · simp [zero]
    · simp only [zero, ↓reduceIte, Int.natAbs_sign]
      exact ⟨Nat.one_lt_two_pow (by omega), by simp⟩
  · rename_i nonzero
    have remainderBound := normalized_remainder_bound width first second secondBound nonzero
    have numeratorBound := normalized_numerator_bound width first second firstBound secondBound nonzero
    have wider : width ≤ 2 * width + 1 := by omega
    refine ⟨remainderBound.trans_le (pow_le_pow_right₀ (by decide) wider), ?_⟩
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt numeratorBound

end Polytime2.ExtendedGcd
