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

import Polytime2.Arithmetic.GcdProgressMath
import Polytime2.Matrices.BezoutMath
import Polytime2.Matrices.SmithMath

/-! # Unimodular normalization of two diagonal entries

The input is a pair of integer diagonal entries. The existing Bézout matrix
and an explicit determinant-one right transformation replace them by their
nonnegative gcd and `a / gcd(a,b) * b`. For positive entries this is the positive
gcd/lcm pair needed to repair divisibility in a Smith diagonal. The coefficient
widths are derived from the original entry width, independently of iteration.
-/

namespace Polytime2.IntegerArithmetic

/-- Halving a positive natural measure decreases its binary length. -/
theorem size_lt_of_double_le (smaller larger : ℕ) (positive : 0 < smaller)
    (halved : 2 * smaller ≤ larger) : smaller.size < larger.size := by
  have doubled : (2 * smaller).size = smaller.size + 1 := by
    simpa [Nat.shiftLeft_eq, mul_comm] using Nat.size_shiftLeft (Nat.ne_of_gt positive) 1
  have decrease := Nat.size_le_size halved
  rw [doubled] at decrease
  exact decrease

end Polytime2.IntegerArithmetic

namespace Polytime2.IntegerMatrix

/-- The right transformation paired with the existing Bézout left transformation. -/
def diagonalPairRight (first second : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  let coefficients := bezoutMatrix first second
  !![1, coefficients 0 1 * coefficients 1 0; 1, coefficients 0 0 * coefficients 1 1]

theorem diagonalPairRight_det (first second : ℤ) :
    (diagonalPairRight first second).det = 1 := by
  simpa [diagonalPairRight, Matrix.det_fin_two] using bezoutMatrix_det first second

/-- Both actual transformations are unimodular, including for the zero pair. -/
theorem diagonalPair_equation (first second : ℤ) :
    bezoutMatrix first second * !![first, 0; 0, second] * diagonalPairRight first second =
      !![(Int.gcd first second : ℤ), 0; 0, first / (Int.gcd first second : ℤ) * second] := by
  by_cases zero : Int.gcd first second = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp zero
    ext row column
    fin_cases row <;> fin_cases column <;> simp [bezoutMatrix, diagonalPairRight]
  · let divisor : ℤ := Int.gcd first second
    let left := (ExtendedGcd.normalizedCoefficients first second).1
    let right := (ExtendedGcd.normalizedCoefficients first second).2
    let firstQuotient := first / divisor
    let secondQuotient := second / divisor
    have firstExact : first = firstQuotient * divisor :=
      (Int.ediv_mul_cancel (Int.gcd_dvd_left first second)).symm
    have secondExact : second = secondQuotient * divisor :=
      (Int.ediv_mul_cancel (Int.gcd_dvd_right first second)).symm
    have reduced : left * firstQuotient + right * secondQuotient = 1 := by
      have determinant := bezoutMatrix_det first second
      simpa [bezoutMatrix, zero, Matrix.det_fin_two, left, right, firstQuotient,
        secondQuotient, divisor] using determinant
    simp only [diagonalPairRight, bezoutMatrix, zero, ↓reduceIte]
    change !![left, right; -secondQuotient, firstQuotient] * !![first, 0; 0, second] *
      !![1, right * -secondQuotient; 1, left * firstQuotient] =
        !![divisor, 0; 0, firstQuotient * second]
    rw [firstExact, secondExact]
    ext row column
    fin_cases row <;> fin_cases column
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · linear_combination divisor * reduced
    · ring
    · ring
    · linear_combination firstQuotient * secondQuotient * divisor * reduced

/-- The right coefficients have linear magnitude width in the input width. -/
theorem diagonalPairRight_bound (width : ℕ) (first second : ℤ)
    (firstBound : first.natAbs < 2 ^ width) (secondBound : second.natAbs < 2 ^ width) :
    ∀ row column, (diagonalPairRight first second row column).natAbs < 2 ^ (2 * (2 * width + 1)) := by
  have coefficientBound := bezoutMatrix_bound width first second firstBound secondBound
  have productBound (a b c d : Fin 2) :
      ((bezoutMatrix first second a b) * bezoutMatrix first second c d).natAbs <
        2 ^ (2 * (2 * width + 1)) := by
    rw [Int.natAbs_mul, two_mul, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (coefficientBound a b) (coefficientBound c d)
  intro row column
  fin_cases row <;> fin_cases column
  · simp [diagonalPairRight]
  · simpa [diagonalPairRight] using productBound 0 1 1 0
  · simp [diagonalPairRight]
  · simpa [diagonalPairRight] using productBound 0 0 1 1

/-- Dividing by the gcd before multiplying gives the natural lcm, including at zero. -/
theorem diagonalPair_lcm (first second : ℕ) :
    first / Nat.gcd first second * second = Nat.lcm first second := by
  by_cases zero : Nat.gcd first second = 0
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp zero
    simp
  · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero zero)
    calc
      Nat.gcd first second * (first / Nat.gcd first second * second) =
          (first / Nat.gcd first second * Nat.gcd first second) * second := by ring
      _ = first * second := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left first second)]
      _ = Nat.gcd first second * Nat.lcm first second := (Nat.gcd_mul_lcm first second).symm

/-- On natural entries the output is exactly the nonnegative gcd/lcm diagonal. -/
theorem diagonalPair_nat_equation (first second : ℕ) :
    bezoutMatrix first second * !![(first : ℤ), 0; 0, (second : ℤ)] *
      diagonalPairRight first second = !![(Nat.gcd first second : ℤ), 0; 0, (Nat.lcm first second : ℤ)] := by
  simpa only [Int.gcd_natCast_natCast, ← Int.natCast_ediv, ← Nat.cast_mul, diagonalPair_lcm] using
    diagonalPair_equation first second

/-- Repairing divisibility halves every adjacent weighted-product factor. -/
theorem diagonalPair_weighted_progress (exponent first second : ℕ) (firstPositive : 0 < first)
    (notDivides : ¬first ∣ second) :
    2 * (Nat.gcd first second ^ (exponent + 1) * Nat.lcm first second ^ exponent) ≤
      first ^ (exponent + 1) * second ^ exponent := by
  exact IntegerArithmetic.weightedPair_halves_of_product exponent 1 first second
    (Nat.gcd first second) (Nat.lcm first second) (by decide) (Nat.gcd_mul_lcm first second)
    (ExtendedGcd.gcd_halves_of_not_dvd first second firstPositive notDivides)

/-- The two-entry weighted product is the smallest nontrivial instance. -/
theorem diagonalPair_progress (first second : ℕ) (firstPositive : 0 < first)
    (notDivides : ¬first ∣ second) :
    2 * (Nat.gcd first second ^ 2 * Nat.lcm first second) ≤ first ^ 2 * second := by
  simpa using diagonalPair_weighted_progress 1 first second firstPositive notDivides

/-- The initial weighted-product bit length is linear in the pair's input width. -/
theorem diagonalPair_initial_size_bound (width first second : ℕ)
    (firstBound : first < 2 ^ width) (secondBound : second < 2 ^ width) :
    (first ^ 2 * second).size ≤ 3 * width := by
  apply Nat.size_le.mpr
  have bound := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt firstBound firstBound) secondBound
  simpa only [pow_two, ← pow_add, show width + width + width = 3 * width by omega] using bound

/-- A failed divisibility relation strictly decreases the weighted-product bit length. -/
theorem diagonalPair_size_decreases (first second : ℕ) (firstPositive : 0 < first)
    (secondPositive : 0 < second) (notDivides : ¬first ∣ second) :
    (Nat.gcd first second ^ 2 * Nat.lcm first second).size < (first ^ 2 * second).size := by
  let updated := Nat.gcd first second ^ 2 * Nat.lcm first second
  have positive : 0 < updated :=
    Nat.mul_pos (pow_pos (Nat.gcd_pos_of_pos_left second firstPositive) 2)
      (Nat.lcm_pos firstPositive secondPositive)
  exact IntegerArithmetic.size_lt_of_double_le updated _ positive
    (diagonalPair_progress first second firstPositive notDivides)

/-- The two-entry cleanup meets the same Smith contract as the full rectangular algorithm. -/
theorem diagonalPair_isSmithForm (first second : ℕ) (firstPositive : 0 < first)
    (secondPositive : 0 < second) :
    IsSmithForm !![(first : ℤ), 0; 0, (second : ℤ)]
      !![(Nat.gcd first second : ℤ), 0; 0, (Nat.lcm first second : ℤ)]
      (bezoutMatrix first second) (diagonalPairRight first second) 2 := by
  have gcdPositive : (0 : ℤ) < Nat.gcd first second := by
    exact_mod_cast Nat.gcd_pos_of_pos_left second firstPositive
  have lcmPositive : (0 : ℤ) < Nat.lcm first second := by
    exact_mod_cast Nat.lcm_pos firstPositive secondPositive
  refine ⟨diagonalPair_nat_equation first second, ?_, ?_, ?_⟩
  · rw [bezoutMatrix_det]
    exact isUnit_one
  · rw [diagonalPairRight_det]
    exact isUnit_one
  · refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · intro row column different
      fin_cases row <;> fin_cases column <;> simp_all
    · intro row column inactive
      have bounded := row.isLt
      omega
    · intro row column same active
      fin_cases row <;> fin_cases column <;> simp_all
    · intro lower upper consecutive active
      fin_cases lower <;> fin_cases upper <;> simp_all [diagonalEntry]
      exact_mod_cast (Nat.gcd_dvd_left first second).trans (Nat.dvd_lcm_left first second)

end Polytime2.IntegerMatrix
