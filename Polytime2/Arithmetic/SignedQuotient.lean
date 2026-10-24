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

import Polytime2.Arithmetic.SignedDivision
import Polytime2.Computation.Conditional

/-! # Total signed Euclidean division

Input two signed integers at a common magnitude width. Return their ordinary
Euclidean quotient and remainder at that width. A zero divisor gives quotient
zero and retains the dividend as remainder. The existing quotient caller and
the quotient-coordinate remainder consumer share one certified zero guard.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Total integer division; zero divisors give the pair `(0, dividend)`. -/
noncomputable def integerTotalDivision (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (binaryIntegers width).prod (binaryIntegers width)
  precondition _ _ := True
  compute _ arguments :=
    (⟨(arguments.val false).val / (arguments.val true).val,
      (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments.val false).property⟩,
     ⟨(arguments.val false).val % (arguments.val true).val, by
      by_cases zero : (arguments.val true).val = 0
      · simpa [zero] using (arguments.val false).property
      · have smaller := Int.emod_lt (arguments.val false).val zero
        have magnitude := Int.natAbs_of_nonneg (Int.emod_nonneg (arguments.val false).val zero)
        have bound := (arguments.val true).property
        omega⟩)

/-- One zero test extends the existing certified division to all integer operands. -/
theorem integerTotalDivision_realizable (width : MvPolynomial Parameter ℕ) :
    (integerTotalDivision width).Realizable := by
  let computation := integerTotalDivision width
  let inputs := computation.inputDomains
  let zero (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) := decide ((arguments true).val = 0)
  have tested := (integerIsZero_realizable width).withArguments inputs (MultiTape.oneTape true) (by intros; rfl)
  apply Realizable.ofCases (computation := computation) zero tested
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ zero sizes arguments = true
    have pair := (Realizable.argument inputs true allowed).prodMk (Realizable.argument inputs false allowed)
    apply pair.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    have isZero : (arguments true).val = 0 := of_decide_eq_true valid.2
    apply Prod.ext <;> apply Subtype.ext
    · change (arguments true).val = (arguments false).val / (arguments true).val
      simp [isZero]
    · change (arguments false).val = (arguments false).val % (arguments true).val
      simp [isZero]
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ zero sizes arguments = false
    have divided := (integerDivision_realizable width).withPrecondition allowed (by
      intro sizes arguments valid
      exact of_decide_eq_false valid.2)
    exact divided.withSpecification allowed _ (by intros; trivial) (by intros; rfl)

/-- Ordinary integer division, with zero quotient when the divisor is zero. -/
noncomputable def integerTotalQuotient (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerTotalDivision width).followedBy (pairProjection (binaryIntegers width) (binaryIntegers width) false) rfl (by intros; trivial)

/-- Quotient projection specializes the shared total division. -/
theorem integerTotalQuotient_realizable (width : MvPolynomial Parameter ℕ) :
    (integerTotalQuotient width).Realizable :=
  (integerTotalDivision_realizable width).fst

/-- The quotient projection has the ordinary total integer-division meaning. -/
theorem integerTotalQuotient_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerTotalQuotient width).Arguments sizes) :
    ((integerTotalQuotient width).compute sizes ⟨arguments, trivial⟩).val =
      (arguments false).val / (arguments true).val := rfl

/-- Ordinary Euclidean remainder, retaining the dividend at divisor zero. -/
noncomputable def integerTotalRemainder (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerTotalDivision width).followedBy (pairProjection (binaryIntegers width) (binaryIntegers width) true) rfl (by intros; trivial)

/-- Remainder projection specializes the same certified total division. -/
theorem integerTotalRemainder_realizable (width : MvPolynomial Parameter ℕ) :
    (integerTotalRemainder width).Realizable :=
  (integerTotalDivision_realizable width).snd

end Polytime2.Computation
