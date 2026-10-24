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

import Polytime2.Arithmetic.SignedArithmetic

/-! # Signed comparison through sign and ordinary natural magnitude

At magnitude width `w`, compare any two bounded integers without an additional
precondition. Opposite signs decide immediately; for two negative inputs the
magnitude ordering reverses. Equality and non-strict comparison specialize
this mathematical interface.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

namespace Realizable.Internal

noncomputable def naturalLess (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryNaturalsOfWidth width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).val < (arguments.val true).val)

theorem naturalLess_realizable (width : MvPolynomial Parameter ℕ) :
    (naturalLess width).Realizable := by
  exact (bitsLess_realizable width).reinterpretInputs
    (fun _ => binaryNaturalsOfWidth width) (fun _ _ value => BitVec.ofFin value)
    (by intros; rfl) (fun _ sizes value => binaryNaturalsOfWidth_encode_bits width sizes value)
    (fun _ _ => True) (by intros; trivial)

end Realizable.Internal

noncomputable def integerLess (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).val < (arguments.val true).val)

private theorem signed_comparison (left right : ℤ) :
    (if SignedEncoding.negative left != SignedEncoding.negative right then SignedEncoding.negative left
      else if SignedEncoding.negative left then decide (right.natAbs < left.natAbs)
      else decide (left.natAbs < right.natAbs)) = decide (left < right) := by
  have leftMagnitude := SignedEncoding.magnitude_value left
  have rightMagnitude := SignedEncoding.magnitude_value right
  by_cases leftNegative : left < 0 <;> by_cases rightNegative : right < 0
  all_goals
    simp [SignedEncoding.negative, leftNegative, rightNegative]
    simp only [leftNegative, rightNegative, ↓reduceIte] at leftMagnitude rightMagnitude
    omega

theorem integerLess_realizable (width : MvPolynomial Parameter ℕ) :
    (integerLess width).Realizable := by
  let inputs := (integerLess width).inputDomains
  have sign (name : Bool) :
      (Computation.mk inputs booleans (fun _ _ => True)
        (fun _ arguments => SignedEncoding.negative (arguments.val name).val)).Realizable := by
    exact (integerNegative_realizable width).onArguments inputs (fun _ _ => True)
      (fun _ => name) (by intro _; rfl) (by intros; trivial)
  have magnitudes (reverse : Bool) :
      (Computation.mk inputs booleans (fun _ _ => True)
        (fun _ arguments => decide
          ((arguments.val (if reverse then true else false)).val.natAbs <
           (arguments.val (if reverse then false else true)).val.natAbs))).Realizable := by
    have compared := (Realizable.Internal.naturalLess_realizable width).onResults inputs (fun _ _ => True)
      (fun name _ arguments => ⟨(arguments.val (if reverse then !name else name)).val.natAbs,
        (arguments.val (if reverse then !name else name)).property⟩)
      (by intros; trivial) (by
        intro name
        exact (integerMagnitude_realizable width).onArguments inputs (fun _ _ => True)
          (fun _ => (if reverse then !name else name)) (by intro _; rfl) (by intros; trivial))
    cases reverse <;> exact compared
  have combined := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool × Bool)
    (fun flags => if flags (false, false) != flags (false, true) then flags (false, false)
      else if flags (false, false) then flags (true, true) else flags (true, false))).onResults
    inputs (fun _ _ => True)
    (fun name _ arguments => if name.1 then
      decide ((arguments.val (if name.2 then true else false)).val.natAbs <
        (arguments.val (if name.2 then false else true)).val.natAbs)
      else SignedEncoding.negative (arguments.val name.2).val)
    (by intros; trivial) (by
      rintro ⟨first, second⟩
      cases first
      · exact sign second
      · exact magnitudes second)
  exact combined.withSpecification (fun _ _ => True) (integerLess width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      exact signed_comparison (arguments false).val (arguments true).val)

private theorem integerReverseLess_realizable (width : MvPolynomial Parameter ℕ) :
    (Computation.mk (fun _ : Bool => binaryIntegers width) booleans (fun _ _ => True)
      (fun _ arguments => decide ((arguments.val true).val < (arguments.val false).val))).Realizable := by
  exact (integerLess_realizable width).onArguments (fun _ => binaryIntegers width) (fun _ _ => True)
    (fun name => (!name)) (by intro name; rfl) (by intros; trivial)

noncomputable def integerEqual (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).val = (arguments.val true).val)

theorem integerEqual_realizable (width : MvPolynomial Parameter ℕ) :
    (integerEqual width).Realizable := by
  let inputs := (integerEqual width).inputDomains
  have combined := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool)
    (fun flags => !flags false && !flags true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then decide ((arguments.val true).val < (arguments.val false).val)
      else decide ((arguments.val false).val < (arguments.val true).val))
    (by intros; trivial) (by
      intro name
      cases name
      · exact integerLess_realizable width
      · exact integerReverseLess_realizable width)
  exact combined.withSpecification (fun _ _ => True) (integerEqual width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp [onResults, booleanOperation, integerEqual]
      omega)

noncomputable def integerLessEqual (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).val ≤ (arguments.val true).val)

theorem integerLessEqual_realizable (width : MvPolynomial Parameter ℕ) :
    (integerLessEqual width).Realizable := by
  have inverted := (integerReverseLess_realizable width).followedBy
    (booleanOperation_realizable (Parameter := Parameter) (Argument := Unit) (fun flags => !flags ()))
    rfl (by intros; trivial)
  exact inverted.withSpecification (fun _ _ => True) (integerLessEqual width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp [followedBy, booleanOperation, integerLessEqual])

end Polytime2.Computation
