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

import Polytime2.Encoding.Integers

/-! # Euclidean correction of unsigned division on integer magnitudes

For nonzero `b`, unsigned division of `|a|` by `|b|` produces `q₀,r₀`.
If `a < 0` and `r₀ ≠ 0`, use magnitude `q₀+1` and remainder `|b|-r₀`.
Otherwise retain both magnitudes. Opposite operand signs negate the quotient.
The resulting integer pair satisfies the ordinary Euclidean contract.
-/

namespace Polytime2.Computation.Realizable.Internal.SignedDivision

open EncodedDomain

def adjust (dividend : ℤ) (remainder : ℕ) : Bool := decide (dividend < 0 ∧ remainder ≠ 0)

def quotientMagnitude (dividend divisor : ℤ) : ℕ :=
  dividend.natAbs / divisor.natAbs +
    if adjust dividend (dividend.natAbs % divisor.natAbs) then 1 else 0

def remainderMagnitude (dividend divisor : ℤ) : ℕ :=
  if adjust dividend (dividend.natAbs % divisor.natAbs) then
    divisor.natAbs - dividend.natAbs % divisor.natAbs else dividend.natAbs % divisor.natAbs

def quotientValue (dividend divisor : ℤ) : ℤ :=
  if SignedEncoding.negative dividend != SignedEncoding.negative divisor then
    -(quotientMagnitude dividend divisor : ℤ) else (quotientMagnitude dividend divisor : ℤ)

theorem correct (dividend divisor : ℤ) (nonzero : divisor ≠ 0) :
    quotientValue dividend divisor = dividend / divisor ∧
      (remainderMagnitude dividend divisor : ℤ) = dividend % divisor := by
  have divisorPositive : 0 < divisor.natAbs := Int.natAbs_pos.mpr nonzero
  have modulusBound := Nat.mod_lt dividend.natAbs divisorPositive
  have division : (divisor.natAbs : ℤ) * (dividend.natAbs / divisor.natAbs : ℕ) +
      (dividend.natAbs % divisor.natAbs : ℕ) = (dividend.natAbs : ℤ) := by
    exact_mod_cast Nat.div_add_mod dividend.natAbs divisor.natAbs
  have dividendMagnitude := SignedEncoding.magnitude_value dividend
  have divisorMagnitude := SignedEncoding.magnitude_value divisor
  have subtraction : ((divisor.natAbs - dividend.natAbs % divisor.natAbs : ℕ) : ℤ) =
      (divisor.natAbs : ℤ) - (dividend.natAbs % divisor.natAbs : ℕ) :=
    Int.natCast_sub modulusBound.le
  have equation : (remainderMagnitude dividend divisor : ℤ) + divisor * quotientValue dividend divisor = dividend := by
    by_cases dividendNegative : dividend < 0 <;> by_cases divisorNegative : divisor < 0 <;>
      by_cases exactDivision : dividend.natAbs % divisor.natAbs = 0
    all_goals
      simp only [dividendNegative, divisorNegative, ↓reduceIte] at dividendMagnitude divisorMagnitude
      simp only [remainderMagnitude, quotientValue, quotientMagnitude, adjust, SignedEncoding.negative,
        dividendNegative, divisorNegative, exactDivision, subtraction, true_and, false_and,
        not_true_eq_false, not_false_eq_true, ne_self_iff_false, decide_eq_true_eq, decide_true, decide_false, Bool.bne_true, Bool.bne_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self_iff_true, ↓reduceIte,
        Nat.add_zero, Int.natCast_add, Int.natCast_zero, Int.natCast_one]
      try simp only [exactDivision, Int.natCast_zero, add_zero] at division
      simp only [dividendMagnitude, divisorMagnitude] at division ⊢
      first
      | nlinarith [division]
      | split_ifs <;>
          simp only [subtraction, Int.natCast_add, Int.natCast_one, dividendMagnitude, divisorMagnitude] <;>
          first | omega | nlinarith [division]
  have remainderBound : 0 ≤ (remainderMagnitude dividend divisor : ℤ) ∧
      (remainderMagnitude dividend divisor : ℤ) < (divisor.natAbs : ℤ) := by
    by_cases correction : adjust dividend (dividend.natAbs % divisor.natAbs) = true
    · have active : dividend < 0 ∧ dividend.natAbs % divisor.natAbs ≠ 0 := of_decide_eq_true correction
      simp only [remainderMagnitude, correction, ↓reduceIte]
      refine ⟨Int.natCast_nonneg _, ?_⟩
      exact_mod_cast (show divisor.natAbs - dividend.natAbs % divisor.natAbs < divisor.natAbs by omega)
    · have inactive := Bool.eq_false_iff.mpr correction
      simp only [remainderMagnitude, inactive, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Int.natCast_nonneg _, by exact_mod_cast modulusBound⟩
  by_cases divisorNegative : divisor < 0
  · have unique := (Int.ediv_emod_unique' (a := dividend) (b := divisor) divisorNegative).mpr
      ⟨equation, remainderBound.1, by
        have magnitude := SignedEncoding.magnitude_value divisor
        simp only [divisorNegative, ↓reduceIte] at magnitude
        omega⟩
    exact ⟨unique.1.symm, unique.2.symm⟩
  · have positive : 0 < divisor := by omega
    have unique := (Int.ediv_emod_unique (a := dividend) (b := divisor) positive).mpr
      ⟨equation, remainderBound.1, by
        have magnitude := SignedEncoding.magnitude_value divisor
        simp only [divisorNegative, ↓reduceIte] at magnitude
        omega⟩
    exact ⟨unique.1.symm, unique.2.symm⟩

theorem quotient_magnitude (dividend divisor : ℤ) (nonzero : divisor ≠ 0) :
    quotientMagnitude dividend divisor = (dividend / divisor).natAbs := by
  rw [← (correct dividend divisor nonzero).1]
  unfold quotientValue
  split <;> simp

theorem quotient_modular (width : ℕ) (dividend divisor : ℤ) (nonzero : divisor ≠ 0)
    (fits : dividend.natAbs < 2 ^ width) :
    (if adjust dividend (dividend.natAbs % divisor.natAbs) then
      (dividend.natAbs / divisor.natAbs + 1) % 2 ^ width else dividend.natAbs / divisor.natAbs) =
        quotientMagnitude dividend divisor := by
  have bound : quotientMagnitude dividend divisor < 2 ^ width := by
    rw [quotient_magnitude dividend divisor nonzero]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt fits
  cases correction : adjust dividend (dividend.natAbs % divisor.natAbs)
  · simp only [correction, Bool.false_eq_true, ↓reduceIte, quotientMagnitude, Nat.add_zero]
  · have incrementFits : dividend.natAbs / divisor.natAbs + 1 < 2 ^ width := by
      simpa only [quotientMagnitude, correction, ↓reduceIte] using bound
    simp only [correction, ↓reduceIte, quotientMagnitude, Nat.mod_eq_of_lt incrementFits]

theorem remainder_bound (dividend divisor : ℤ) (nonzero : divisor ≠ 0) :
    remainderMagnitude dividend divisor ≤ divisor.natAbs := by
  unfold remainderMagnitude
  split
  · exact Nat.sub_le _ _
  · exact (Nat.mod_lt _ (Int.natAbs_pos.mpr nonzero)).le

theorem quotient_sign (dividend divisor : ℤ) (nonzero : divisor ≠ 0) :
    ((SignedEncoding.negative dividend != SignedEncoding.negative divisor) &&
      decide (0 < quotientMagnitude dividend divisor)) = SignedEncoding.negative (dividend / divisor) := by
  rw [← (correct dividend divisor nonzero).1]
  unfold quotientValue
  cases sign : (SignedEncoding.negative dividend != SignedEncoding.negative divisor) <;>
    simp [SignedEncoding.negative, sign]

end Polytime2.Computation.Realizable.Internal.SignedDivision
