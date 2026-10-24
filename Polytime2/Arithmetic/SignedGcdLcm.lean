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

import Polytime2.Arithmetic.SignedGcd
import Polytime2.Arithmetic.SignedDivision
import Polytime2.Arithmetic.SignedMultiplication
import Polytime2.Computation.Conditional

/-! # Certified gcd and signed lcm with derived output widths

Every pair of bounded signed integers is admissible, including the zero pair.
Return the nonnegative gcd and `a / gcd(a,b) * b`, using magnitude widths `w`
and `2*w`. The zero branch avoids division; on nonnegative inputs the second
result is the usual nonnegative lcm. These are the diagonal entries produced
by the unimodular pair-cleanup transformations.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerGcdLcm (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (binaryIntegers width).prod (binaryIntegers (2 * width))
  precondition _ _ := True
  compute sizes arguments :=
    ((integerGcd width).compute sizes arguments,
      ⟨(arguments.val false).val / (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) *
          (arguments.val true).val, by
        have quotientBound := (Int.natAbs_ediv_le_natAbs (arguments.val false).val
          (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ)).trans_lt (arguments.val false).property
        have bound := Nat.mul_lt_mul'' quotientBound (arguments.val true).property
        simpa only [Int.natAbs_mul, map_mul, map_add, MvPolynomial.eval_ofNat, two_mul, pow_add] using bound⟩)

theorem integerGcdLcm_realizable (width : MvPolynomial Parameter ℕ) : (integerGcdLcm width).Realizable := by
  classical
  let computation := integerGcdLcm width
  let inputs := computation.inputDomains
  let condition (_sizes : Parameter → ℕ) (arguments : ∀ name, (inputs name).Carrier _sizes) :=
    decide ((Int.gcd (arguments false).val (arguments true).val : ℤ) = 0)
  have guard := (integerGcd_realizable width).followedBy (integerIsZero_realizable width) rfl (by intros; trivial)
  apply Realizable.ofCases (computation := computation) condition guard
  · let allowed sizes arguments := True ∧ condition sizes arguments = true
    have assembled := ((integerGcd_realizable width).withPrecondition allowed (by intros; trivial)).prodMk ((integerMultiply_realizable width).withPrecondition allowed (by intros; trivial))
    apply assembled.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, trivial⟩) (by intros; trivial)
    intro sizes arguments valid
    have zero : Int.gcd (arguments false).val (arguments true).val = 0 := by
      have castZero := of_decide_eq_true valid.2
      exact_mod_cast castZero
    have secondZero := (Int.gcd_eq_zero_iff.mp zero).2
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (arguments false).val * (arguments true).val = _
      simp only [computation, integerGcdLcm]
      rw [secondZero]
      simp
  · let allowed sizes arguments := True ∧ condition sizes arguments = false
    let divided := (integerQuotient width).onResults inputs allowed
      (fun choice sizes arguments => if choice then
        (integerGcd width).compute sizes ⟨arguments.val, trivial⟩ else arguments.val false)
      (by
        intro sizes arguments
        change (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) ≠ 0
        exact of_decide_eq_false arguments.property.2)
    have dividedReady : divided.Realizable := by
      apply (integerQuotient_realizable width).onResults inputs allowed _ _
      intro choice
      cases choice
      · exact Realizable.argument inputs false allowed
      · exact (integerGcd_realizable width).withPrecondition allowed (by intros; trivial)
    have multiplied := (integerMultiply_realizable width).onResults inputs allowed
      (fun choice sizes arguments => if choice then arguments.val true else divided.compute sizes arguments)
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact dividedReady
        · exact Realizable.argument inputs true allowed)
    have assembled := ((integerGcd_realizable width).withPrecondition allowed (by intros; trivial)).prodMk multiplied
    exact assembled.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, trivial⟩) (by intros; trivial) (by intros; rfl)

/-- The two returned entries retain the product and satisfy divisibility, even at zero. -/
theorem integerGcdLcm_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (integerGcdLcm width).Arguments sizes // True}) :
    let result := (integerGcdLcm width).compute sizes arguments
    0 ≤ result.1.val ∧ result.1.val * result.2.val = (arguments.val false).val * (arguments.val true).val ∧
      result.1.val ∣ result.2.val := by
  refine ⟨Int.natCast_nonneg _, ?_, ?_⟩
  · change (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) *
      ((arguments.val false).val / (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) *
        (arguments.val true).val) = _
    calc
      _ = ((arguments.val false).val / (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) *
          (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ)) * (arguments.val true).val := by ring
      _ = _ := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]
  · exact dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _

end Polytime2.Computation
