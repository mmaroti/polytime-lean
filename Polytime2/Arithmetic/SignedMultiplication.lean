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
import Polytime2.Arithmetic.NaturalArithmetic

/-! # Signed multiplication with a derived double-width result

All operands at magnitude width `w` are admissible. Unsigned multiplication
uses a private widened first operand and returns at magnitude width `2*w`.
The result sign is normalized at zero; there is no public overflow premise.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem multiplication_sign (left right : ℤ) :
    ((SignedEncoding.negative left != SignedEncoding.negative right) &&
      !decide (left = 0) && !decide (right = 0)) = SignedEncoding.negative (left * right) := by
  apply Bool.eq_iff_iff.mpr
  simp [SignedEncoding.negative, mul_neg_iff]
  omega

theorem integerMultiply_realizable (width : MvPolynomial Parameter ℕ) :
    (integerMultiply width).Realizable := by
  let inputs := (integerMultiply width).inputDomains
  let output := binaryNaturalsOfWidth (2 * width)
  have wider (sizes : Parameter → ℕ) : MvPolynomial.eval sizes width ≤ MvPolynomial.eval sizes (2 * width) := by
    rw [two_mul, map_add]
    omega
  let widened sizes (value : (binaryNaturalsOfWidth width).Carrier sizes) : output.Carrier sizes :=
    ⟨value.val, value.isLt.trans_le (pow_le_pow_right₀ (by decide) (wider sizes))⟩
  have widenReady : (unaryMap (binaryNaturalsOfWidth width) output (fun _ _ => True)
      (fun sizes value => widened sizes value.val)).Realizable := by
    exact (Realizable.Internal.naturalWiden_realizable width width).reinterpretOutput output
      (fun sizes value => ⟨value.val, by simpa only [two_mul] using value.isLt⟩)
      (by intro sizes; change MvPolynomial.eval sizes (2 * width) = MvPolynomial.eval sizes (width + width)
          rw [two_mul])
      (fun sizes value => boundedIndexOfWidth_encode_congr _ _ _ _ (fun _ => le_rfl) (fun _ => le_rfl) sizes
        (by rw [two_mul]) _ _ rfl)
  let magnitude (name : Bool) sizes (arguments : {arguments : (integerMultiply width).Arguments sizes // True}) :
      (binaryNaturalsOfWidth (if name then width else 2 * width)).Carrier sizes :=
    match name with
    | false => widened sizes ⟨(arguments.val false).val.natAbs, (arguments.val false).property⟩
    | true => ⟨(arguments.val true).val.natAbs, (arguments.val true).property⟩
  have magnitudeReady (name : Bool) :
      (Computation.mk inputs (binaryNaturalsOfWidth (if name then width else 2 * width))
        (fun _ _ => True) (magnitude name)).Realizable := by
    cases name
    · exact ((integerMagnitude_realizable width).followedBy widenReady rfl (by intros; trivial)).withArguments
        inputs (MultiTape.oneTape false) (fun _ => rfl)
    · exact (integerMagnitude_realizable width).withArguments inputs (MultiTape.oneTape true) (fun _ => rfl)
  have product := (Realizable.Internal.naturalMultiplyAtWidths_realizable (2 * width) width).onResults
    inputs (fun _ _ => True) magnitude (by
      intro sizes arguments
      change (arguments.val false).val.natAbs * (arguments.val true).val.natAbs < _
      have bound := ((integerMultiply width).compute sizes arguments).property
      simpa only [integerMultiply, Int.natAbs_mul] using bound) magnitudeReady
  have signs := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool × Bool)
    (fun flags => (flags (false, false) != flags (false, true)) &&
      !flags (true, false) && !flags (true, true))).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name.1 then decide ((arguments.val name.2).val = 0)
      else SignedEncoding.negative (arguments.val name.2).val)
    (by intros; trivial) (by
      rintro ⟨testZero, name⟩
      cases testZero
      · exact (integerNegative_realizable width).withArguments inputs (MultiTape.oneTape name) (fun _ => rfl)
      · exact (integerIsZero_realizable width).withArguments inputs (MultiTape.oneTape name) (fun _ => rfl))
  have negative : (Computation.mk inputs booleans (fun _ _ => True)
      (fun _ arguments => SignedEncoding.negative ((arguments.val false).val * (arguments.val true).val))).Realizable := by
    exact signs.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
      intro sizes arguments valid
      exact multiplication_sign (arguments false).val (arguments true).val)
  have constructed := (negative.prodMk product).followedBy (Realizable.Internal.integerOfParts_realizable (2 * width)) rfl (by
    intro sizes arguments valid
    change SignedEncoding.negative ((arguments false).val * (arguments true).val) = true →
      (arguments false).val.natAbs * (arguments true).val.natAbs ≠ 0
    rw [← Int.natAbs_mul]
    intro sign zero
    have strictlyNegative : (arguments false).val * (arguments true).val < 0 := of_decide_eq_true sign
    exact (ne_of_lt strictlyNegative) (Int.natAbs_eq_zero.mp zero))
  exact constructed.withSpecification (fun _ _ => True) (integerMultiply width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (if SignedEncoding.negative ((arguments false).val * (arguments true).val)
        then -(((arguments false).val.natAbs * (arguments true).val.natAbs : ℕ) : ℤ)
        else (((arguments false).val.natAbs * (arguments true).val.natAbs : ℕ) : ℤ)) =
          (arguments false).val * (arguments true).val
      rw [← Int.natAbs_mul]
      exact SignedEncoding.restore _)

end Polytime2.Computation
