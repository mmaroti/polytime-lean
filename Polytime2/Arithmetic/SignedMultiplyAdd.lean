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

import Polytime2.Arithmetic.SignedMultiplySubtract
import Polytime2.Arithmetic.SignedBounds

/-! # Signed multiply-add with an internally derived result width

The three mathematical integer inputs have magnitude width `w`. Every input is
admissible; the result `first + coefficient * second` has width `2*w+1`.
Realization reuses the existing bounded coefficient update after widening and
negating the coefficient. No new arithmetic controller is introduced.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Exact integer multiply-add, with no public overflow premise. -/
noncomputable def integerMultiplyAdd (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers (2 * width + 1)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val 0).val + (arguments.val 1).val * (arguments.val 2).val, by
    simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
      IntegerArithmetic.multiplyAdd_bound (MvPolynomial.eval sizes width) _ _ _
        (arguments.val 0).property (arguments.val 1).property (arguments.val 2).property⟩

theorem integerMultiplyAdd_realizable (width : MvPolynomial Parameter ℕ) :
    (integerMultiplyAdd width).Realizable := by
  let inputs := (integerMultiplyAdd width).inputDomains
  let capacity := 2 * width + 1
  have widthEqual : capacity = width + (width + 1) := by dsimp [capacity]; ring
  let widen sizes (value : (binaryIntegers width).Carrier sizes) :
      (binaryIntegers capacity).Carrier sizes := ⟨value.val,
        value.property.trans_le (pow_le_pow_right₀ (by decide)
          (by dsimp [capacity]; simp only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat]; omega))⟩
  have wider := Realizable.Internal.integerWidenTo_realizable width (width + 1) capacity widthEqual
  let values (name : Fin 3) sizes
      (arguments : {arguments : (integerMultiplyAdd width).Arguments sizes // True}) :=
    widen sizes (if name = 1 then
      ⟨-(arguments.val name).val, by simpa using (arguments.val name).property⟩
      else arguments.val name)
  have producers (name : Fin 3) :
      (Computation.mk inputs (binaryIntegers capacity) (fun _ _ => True) (values name)).Realizable := by
    by_cases middle : name = 1
    · subst name
      exact ((integerNegate_realizable width).followedBy wider rfl (by intros; trivial)).withArguments
        inputs (MultiTape.oneTape 1) (fun _ => rfl)
    · exact (wider.withArguments inputs (MultiTape.oneTape name) (fun _ => rfl)).withSpecification
        (fun _ _ => True) (values name) (by intros; trivial) (by intros; simp only [values, middle, ↓reduceIte]; rfl)
  have updated := (Realizable.Internal.integerMultiplySubtract_realizable capacity).onResults
    inputs (fun _ _ => True) values (by
      intro sizes arguments
      change ((arguments.val 0).val - -(arguments.val 1).val * (arguments.val 2).val).natAbs < _
      rw [neg_mul, sub_neg_eq_add]
      exact ((integerMultiplyAdd width).compute sizes arguments).property) producers
  exact updated.withSpecification (fun _ _ => True) (integerMultiplyAdd width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (arguments 0).val - -(arguments 1).val * (arguments 2).val = _
      rw [neg_mul, sub_neg_eq_add]
      rfl)

end Polytime2.Computation
