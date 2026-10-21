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

import Polytime2.Arithmetic.SignedMultiplication
import Polytime2.Arithmetic.SignedAddition
import Polytime2.Arithmetic.SignedWidth

/-! # Private bounded coefficient updates

Extended Euclid needs `a-b*q` at a derived coefficient width. The sole
precondition states that this mathematical answer fits that width. Products
and differences use sufficient internal storage before exact narrowing.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerMultiplySubtract (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers width
  precondition sizes arguments := ((arguments 0).val - (arguments 1).val * (arguments 2).val).natAbs <
    2 ^ MvPolynomial.eval sizes width
  compute _ arguments := ⟨(arguments.val 0).val - (arguments.val 1).val * (arguments.val 2).val, arguments.property⟩

theorem integerMultiplySubtract_realizable (width : MvPolynomial Parameter ℕ) :
    (integerMultiplySubtract width).Realizable := by
  let inputs := (integerMultiplySubtract width).inputDomains
  let allowed := (integerMultiplySubtract width).precondition
  let productValue sizes (arguments : {arguments : (integerMultiplySubtract width).Arguments sizes // allowed sizes arguments}) :=
    (integerMultiply width).compute sizes ⟨(fun name => arguments.val (if name then 2 else 1)), trivial⟩
  have product : (Computation.mk inputs (binaryIntegers (2 * width)) allowed productValue).Realizable :=
    (integerMultiply_realizable width).onResults inputs allowed
      (fun name _ arguments => arguments.val (if name then 2 else 1)) (by intros; trivial)
      (fun name => Realizable.argument inputs (if name then 2 else 1) allowed)
  let widenValue sizes (value : (binaryIntegers width).Carrier sizes) :
      (binaryIntegers (2 * width)).Carrier sizes := ⟨value.val, value.property.trans_le
        (pow_le_pow_right₀ (by decide) (by rw [two_mul, map_add]; omega))⟩
  have widened := (integerWiden_realizable width width).withEncodedOutput (binaryIntegers (2 * width))
    (fun sizes arguments => widenValue sizes (arguments.val ()))
    (by intro sizes; change (binaryIntegers (2 * width)).width sizes = (binaryIntegers (width + width)).width sizes
        rw [two_mul]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      exact binaryIntegers_encode_congr (2 * width) (width + width) (two_mul width) sizes _ _ rfl)
  have first := widened.onResults inputs allowed (fun _ _ arguments => arguments.val 0)
    (by intros; trivial) (fun _ => Realizable.argument inputs 0 allowed)
  have difference := (integerSubtract_realizable (2 * width)).onResults inputs allowed
    (fun name sizes arguments => if name then productValue sizes arguments else widenValue sizes (arguments.val 0))
    (by intros; trivial) (by
      intro name
      cases name
      · exact first
      · exact product)
  have narrowed := difference.followedBy (integerNarrowAtWidths_realizable (2 * width + 1) width
    (by intro sizes; rw [map_add, map_one, two_mul, map_add]; omega)) rfl (by
      intro sizes arguments valid
      exact valid)
  exact narrowed.withSpecification allowed (integerMultiplySubtract width).compute
    (by intros; assumption) (by intros; rfl)

end Polytime2.Computation.Realizable.Internal
