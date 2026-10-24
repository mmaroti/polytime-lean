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

import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! # Bit budgets for genuine gcd pivot changes

If a positive pivot does not divide the next entry, replacing it by their gcd
at least halves it. This shared estimate supplies progress for Hermite pivot
changes and weighted diagonal cleanup.
-/

namespace Polytime2.ExtendedGcd

/-- A proper gcd divides the positive pivot with quotient at least two. -/
theorem gcd_halves_of_not_dvd (first second : ℕ) (positive : 0 < first)
    (notDivides : ¬first ∣ second) : 2 * Nat.gcd first second ≤ first := by
  obtain ⟨quotient, firstEq⟩ := Nat.gcd_dvd_left first second
  have quotientLarge : 2 ≤ quotient := by
    by_contra small
    have cases : quotient = 0 ∨ quotient = 1 := by omega
    rcases cases with zero | one
    · simp [zero] at firstEq
      omega
    · have same : Nat.gcd first second = first := by simpa [one] using firstEq.symm
      exact notDivides (Nat.gcd_eq_left_iff_dvd.mp same)
  nlinarith

/-- The gcd decrease applies to signed entries and a positive integer pivot. -/
theorem int_gcd_halves_of_not_dvd (first second : ℤ) (positive : 0 < first)
    (notDivides : ¬first ∣ second) : 2 * (Int.gcd first second : ℤ) ≤ first := by
  have firstAbs : (first.natAbs : ℤ) = first := Int.natAbs_of_nonneg (le_of_lt positive)
  have firstPositive : 0 < first.natAbs := Int.natAbs_pos.mpr (ne_of_gt positive)
  have notAbsDivides : ¬first.natAbs ∣ second.natAbs := by
    simpa only [Int.natAbs_dvd_natAbs] using notDivides
  have result := gcd_halves_of_not_dvd first.natAbs second.natAbs firstPositive notAbsDivides
  have castResult : 2 * (Nat.gcd first.natAbs second.natAbs : ℤ) ≤ (first.natAbs : ℤ) := by exact_mod_cast result
  simpa only [firstAbs, ← Int.gcd_eq_natAbs] using castResult

end Polytime2.ExtendedGcd

namespace Polytime2.IntegerArithmetic

/-- Preserving a pair product and halving its earlier factor halves every strictly weighted pair. -/
theorem weightedPair_halves_of_product (exponent gap first second nextFirst nextSecond : ℕ)
    (gapPositive : 0 < gap) (product : nextFirst * nextSecond = first * second)
    (halved : 2 * nextFirst ≤ first) :
    2 * (nextFirst ^ (exponent + gap) * nextSecond ^ exponent) ≤
      first ^ (exponent + gap) * second ^ exponent := by
  have twoLe : 2 ≤ 2 ^ gap := by
    simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (show 1 ≤ gap by omega)
  have powerHalved : 2 * nextFirst ^ gap ≤ first ^ gap := by
    calc
      _ ≤ 2 ^ gap * nextFirst ^ gap := Nat.mul_le_mul_right _ twoLe
      _ = (2 * nextFirst) ^ gap := (mul_pow _ _ _).symm
      _ ≤ first ^ gap := Nat.pow_le_pow_left halved gap
  calc
    2 * (nextFirst ^ (exponent + gap) * nextSecond ^ exponent) =
        (2 * nextFirst ^ gap) * (nextFirst * nextSecond) ^ exponent := by
      rw [pow_add, mul_pow]
      ring
    _ ≤ first ^ gap * (nextFirst * nextSecond) ^ exponent := Nat.mul_le_mul_right _ powerHalved
    _ = first ^ (exponent + gap) * second ^ exponent := by
      rw [product, pow_add, mul_pow]
      ring

end Polytime2.IntegerArithmetic
