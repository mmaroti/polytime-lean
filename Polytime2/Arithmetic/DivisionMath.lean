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

import Polytime2.Arithmetic.BinaryDivisionStep
import Polytime2.Arithmetic.BitFold

/-! # Mathematical binary division with quotient and remainder

For width `w`, the public inputs are `a b : Fin (2^w)` with `0 < b`.
The output is `(q, r) : Fin (2^w) × Fin (2^w)`, satisfying
`a = b*q + r` and `r < b`. Thus width zero has no admissible inputs.
The machine will prepare an extra working bit privately.

The recurrence below reads dividend bits from high to low. Its ordinary pair
contains the quotient and remainder words; no private scratch is represented.
-/

namespace Polytime2.StandardBinaryDivision

open Binary (value)

/-- The subtraction decision supplies the next quotient bit. -/
def quotientBit (bit : Bool) (remainder divisor : List Bool) : Bool :=
  !(BinarySubtraction.ripple false
    (StandardBinaryDivisionStep.shifted bit remainder) divisor).2

/-- Append one quotient bit and update the remainder using the shared step. -/
def next (bit : Bool) (divisor : List Bool) (current : List Bool × List Bool) :
    List Bool × List Bool :=
  ((BinaryScan.run BinaryScan.shift (quotientBit bit current.2 divisor) current.1).2,
    StandardBinaryDivisionStep.next bit current.2 divisor)

theorem next_lengths (bit : Bool) (divisor : List Bool) (current : List Bool × List Bool)
    (quotientLength : current.1.length = divisor.length)
    (remainderLength : current.2.length = divisor.length) :
    (next bit divisor current).1.length = divisor.length ∧
      (next bit divisor current).2.length = divisor.length := by
  refine ⟨(BinaryScan.run_length _ _ _).trans quotientLength, ?_⟩
  have shiftedLength := StandardBinaryDivisionStep.shifted_length bit current.2
  have differenceLength := BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false (StandardBinaryDivisionStep.shifted bit current.2) divisor (by omega)
  dsimp only [next, StandardBinaryDivisionStep.next, StandardBinaryReduce.reduced]
  split
  · exact shiftedLength.trans remainderLength
  · exact differenceLength.trans (shiftedLength.trans remainderLength)

/-- The division invariant supplies both exact quotient shifting and reduction. -/
theorem next_equation (bit : Bool) (divisor : List Bool) (current : List Bool × List Bool)
    (quotientLength : current.1.length = divisor.length)
    (remainderLength : current.2.length = divisor.length)
    (bounded : value current.2 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length)
    (fits : bit.toNat + 2 * (value divisor * value current.1 + value current.2) <
      2 ^ divisor.length) :
    value divisor * value (next bit divisor current).1 + value (next bit divisor current).2 =
        bit.toNat + 2 * (value divisor * value current.1 + value current.2) ∧
      value (next bit divisor current).2 < value divisor := by
  let shifted := StandardBinaryDivisionStep.shifted bit current.2
  have sameLength : divisor.length = shifted.length := by
    simp [shifted, remainderLength]
  have bitBound : bit.toNat ≤ 1 := by cases bit <;> decide
  have shiftedFits : bit.toNat + 2 * value current.2 < 2 ^ current.2.length := by
    rw [remainderLength]
    omega
  have shiftedValue : value shifted = bit.toNat + 2 * value current.2 :=
    (BinaryScan.shift_value bit current.2 shiftedFits).1
  have small : value shifted < 2 * value divisor := by omega
  have reduced := StandardBinaryDivisionStep.next_value bit current.2 divisor
    remainderLength.symm bounded (by simpa [remainderLength] using capacity)
  have digitEquation : value divisor * (quotientBit bit current.2 divisor).toNat +
      value (StandardBinaryDivisionStep.next bit current.2 divisor) = value shifted := by
    cases borrowed : (BinarySubtraction.ripple false shifted divisor).2 with
    | false =>
      have nonnegative : value divisor ≤ value shifted := by
        have comparison := BinarySubtraction.underflow_iff shifted divisor sameLength
        rw [borrowed] at comparison
        simp only [Bool.false_eq_true, false_iff] at comparison
        omega
      have difference := BinarySubtraction.difference_of_no_borrow shifted divisor sameLength nonnegative
      simpa only [quotientBit, shifted, borrowed, Bool.not_false, Bool.toNat_true,
        Nat.mul_one, StandardBinaryDivisionStep.next, StandardBinaryReduce.reduced,
        Bool.false_eq_true, ↓reduceIte, difference] using
        (Nat.add_sub_of_le nonnegative)
    | true =>
      simp only [quotientBit, shifted, borrowed, Bool.not_true, Bool.toNat_false,
        Nat.mul_zero, StandardBinaryDivisionStep.next, StandardBinaryReduce.reduced,
        ↓reduceIte, Nat.zero_add]
  have quotientFits : (quotientBit bit current.2 divisor).toNat + 2 * value current.1 <
      2 ^ current.1.length := by
    rw [quotientLength]
    nlinarith
  have quotientValue := (BinaryScan.shift_value
    (quotientBit bit current.2 divisor) current.1 quotientFits).1
  refine ⟨?_, ?_⟩
  · change value divisor * value (BinaryScan.run BinaryScan.shift _ current.1).2 + _ = _
    rw [quotientValue]
    change value divisor * _ + value (StandardBinaryDivisionStep.next bit current.2 divisor) = _
    nlinarith
  · change value (StandardBinaryDivisionStep.next bit current.2 divisor) < _
    rw [reduced]
    exact Nat.mod_lt _ (by omega)

/-- Finish the high-bit-first recurrence from a pair of live words. -/
def finish (divisor bits : List Bool) (current : List Bool × List Bool) : List Bool × List Bool :=
  StandardBitFold.fold (fun bit current => next bit divisor current) bits current

theorem finish_lengths (divisor bits : List Bool) (current : List Bool × List Bool)
    (quotientLength : current.1.length = divisor.length)
    (remainderLength : current.2.length = divisor.length) :
    (finish divisor bits current).1.length = divisor.length ∧
      (finish divisor bits current).2.length = divisor.length := by
  induction bits generalizing current with
  | nil => exact ⟨quotientLength, remainderLength⟩
  | cons bit bits hypothesis =>
    exact hypothesis _ (next_lengths bit divisor current quotientLength remainderLength).1
      (next_lengths bit divisor current quotientLength remainderLength).2

private theorem prefixValue_ge (bits : List Bool) (initial : ℕ) :
    initial ≤ Binary.prefixValue bits initial := by
  induction bits generalizing initial with
  | nil => rfl
  | cons bit bits hypothesis =>
    exact (by omega : initial ≤ bit.toNat + 2 * initial).trans (hypothesis _)

theorem finish_equation (divisor bits : List Bool) (current : List Bool × List Bool)
    (quotientLength : current.1.length = divisor.length)
    (remainderLength : current.2.length = divisor.length)
    (bounded : value current.2 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length)
    (fits : Binary.prefixValue bits (value divisor * value current.1 + value current.2) <
      2 ^ divisor.length) :
    value divisor * value (finish divisor bits current).1 + value (finish divisor bits current).2 =
        Binary.prefixValue bits (value divisor * value current.1 + value current.2) ∧
      value (finish divisor bits current).2 < value divisor := by
  induction bits generalizing current with
  | nil => exact ⟨rfl, bounded⟩
  | cons bit bits hypothesis =>
    have step := next_equation bit divisor current quotientLength remainderLength bounded capacity
      ((prefixValue_ge bits _).trans_lt fits)
    have lengths := next_lengths bit divisor current quotientLength remainderLength
    have continued := hypothesis (next bit divisor current) lengths.1 lengths.2 step.2
      (by simpa only [step.1, Binary.prefixValue, List.foldl_cons] using fits)
    simpa only [finish, StandardBitFold.fold, step.1, Binary.prefixValue, List.foldl_cons] using continued

/-- Division returns the unique quotient and remainder of the original input. -/
theorem result_value (input divisor : List Bool) (positive : 0 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length)
    (fits : value input < 2 ^ divisor.length) :
    let answer := finish divisor input.reverse
      (List.replicate divisor.length false, List.replicate divisor.length false)
    value answer.1 = value input / value divisor ∧
      value answer.2 = value input % value divisor := by
  let initial := (List.replicate divisor.length false, List.replicate divisor.length false)
  have equation := finish_equation divisor input.reverse initial List.length_replicate
    List.length_replicate (by simpa [initial] using positive) capacity
    (by simpa [initial, Binary.prefixValue_reverse] using fits)
  have zero : value divisor * value initial.1 + value initial.2 = 0 := by simp [initial]
  rw [zero, Binary.prefixValue_reverse, Nat.mul_zero, Nat.add_zero] at equation
  change value (finish divisor input.reverse initial).1 = value input / value divisor ∧
    value (finish divisor input.reverse initial).2 = value input % value divisor
  have quotient : value input / value divisor = value (finish divisor input.reverse initial).1 :=
    Nat.div_eq_of_lt_le (by nlinarith [equation.1]) (by nlinarith [equation.1, equation.2])
  have remainder := Nat.div_add_mod (value input) (value divisor)
  exact ⟨quotient.symm, by rw [quotient] at remainder; omega⟩

end Polytime2.StandardBinaryDivision
