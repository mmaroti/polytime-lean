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

import Polytime2.Arithmetic.NormalizedBezoutMath
import Polytime2.Matrices.IntegerOperationsMath

/-! # Bounded unimodular Bézout elimination

A pair of integers is transformed to its nonnegative gcd and zero by an actual
integer two-by-two matrix of determinant one. The zero pair uses the identity.
The matrix entries have a linear derived bit-width bound, independently of the
larger workspace used by extended Euclid. This is the local elimination step
needed by the Hermite sweeps of Smith reduction.
-/

namespace Polytime2.IntegerMatrix

/-- The actual determinant-one matrix for a Bézout elimination step. -/
def bezoutMatrix (first second : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if Int.gcd first second = 0 then 1
  else
    let coefficients := ExtendedGcd.normalizedCoefficients first second
    !![coefficients.1, coefficients.2;
      -(second / (Int.gcd first second : ℤ)), first / (Int.gcd first second : ℤ)]

theorem bezoutMatrix_det (first second : ℤ) : (bezoutMatrix first second).det = 1 := by
  by_cases zero : Int.gcd first second = 0
  · simp [bezoutMatrix, zero]
  · have divisorNonzero : (Int.gcd first second : ℤ) ≠ 0 := by exact_mod_cast zero
    apply mul_right_cancel₀ divisorNonzero
    simp only [bezoutMatrix, zero, ↓reduceIte, Matrix.det_fin_two, one_mul]
    change ((ExtendedGcd.normalizedCoefficients first second).1 * (first / (Int.gcd first second : ℤ)) -
      (ExtendedGcd.normalizedCoefficients first second).2 * -(second / (Int.gcd first second : ℤ))) *
        (Int.gcd first second : ℤ) = (Int.gcd first second : ℤ)
    calc
      _ = (ExtendedGcd.normalizedCoefficients first second).1 *
            (first / (Int.gcd first second : ℤ) * (Int.gcd first second : ℤ)) +
          (ExtendedGcd.normalizedCoefficients first second).2 *
            (second / (Int.gcd first second : ℤ) * (Int.gcd first second : ℤ)) := by ring
      _ = (Int.gcd first second : ℤ) := by
        rw [Int.ediv_mul_cancel (Int.gcd_dvd_left first second),
          Int.ediv_mul_cancel (Int.gcd_dvd_right first second)]
        nlinarith [ExtendedGcd.normalizedCoefficients_correct first second]

theorem bezoutMatrix_eliminates (first second : ℤ) :
    (bezoutMatrix first second).mulVec ![first, second] = ![(Int.gcd first second : ℤ), 0] := by
  by_cases zero : Int.gcd first second = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp zero
    simp [bezoutMatrix]
  · have firstExact := Int.ediv_mul_cancel (Int.gcd_dvd_left first second)
    have secondExact := Int.ediv_mul_cancel (Int.gcd_dvd_right first second)
    have cross : -(second / (Int.gcd first second : ℤ)) * first +
        first / (Int.gcd first second : ℤ) * second = 0 := by
      calc
        _ = -(second / (Int.gcd first second : ℤ)) *
              (first / (Int.gcd first second : ℤ) * (Int.gcd first second : ℤ)) +
            first / (Int.gcd first second : ℤ) *
              (second / (Int.gcd first second : ℤ) * (Int.gcd first second : ℤ)) := by
          rw [firstExact, secondExact]
        _ = 0 := by ring
    ext row
    fin_cases row
    · simpa [bezoutMatrix, zero, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm] using
        ExtendedGcd.normalizedCoefficients_correct first second
    · simpa [bezoutMatrix, zero, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using cross

/-- The coefficients written to the matrix have linear magnitude width. -/
theorem bezoutMatrix_bound (width : ℕ) (first second : ℤ)
    (firstBound : first.natAbs < 2 ^ width) (secondBound : second.natAbs < 2 ^ width) :
    ∀ row column, (bezoutMatrix first second row column).natAbs < 2 ^ (2 * width + 1) := by
  have oneBound : 1 < 2 ^ (2 * width + 1) := Nat.one_lt_two_pow (by omega)
  have coefficients := ExtendedGcd.normalizedCoefficients_bound width first second firstBound secondBound
  have wider : 2 ^ width ≤ 2 ^ (2 * width + 1) := pow_le_pow_right₀ (by decide) (by omega)
  have firstQuotient := (Int.natAbs_ediv_le_natAbs first (Int.gcd first second : ℤ)).trans_lt
    (firstBound.trans_le wider)
  have secondQuotient := (Int.natAbs_ediv_le_natAbs second (Int.gcd first second : ℤ)).trans_lt
    (secondBound.trans_le wider)
  intro row column
  by_cases zero : Int.gcd first second = 0
  · fin_cases row <;> fin_cases column <;> simp [bezoutMatrix, zero, oneBound]
  · fin_cases row <;> fin_cases column
    · simpa [bezoutMatrix, zero] using coefficients.1
    · simpa [bezoutMatrix, zero] using coefficients.2
    · simpa [bezoutMatrix, zero] using secondQuotient
    · simpa [bezoutMatrix, zero] using firstQuotient

end Polytime2.IntegerMatrix
