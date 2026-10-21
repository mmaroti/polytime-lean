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

import Polytime2.Arithmetic.SignedComparison
import Polytime2.Arithmetic.NaturalArithmetic

/-! # Exact signed addition and subtraction through magnitude arithmetic

Every pair of inputs at magnitude width `w` is admissible. Results have
magnitude width `w+1`; operands are widened privately before unsigned addition.
Opposite signs use the ordered absolute difference, without exposing an
ordering precondition to callers.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

namespace Realizable.Internal

noncomputable def naturalAbsoluteDifference (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryNaturalsOfWidth width
  outputDomain := binaryNaturalsOfWidth width
  precondition _ _ := True
  compute _ arguments :=
    if smaller : (arguments.val false).val < (arguments.val true).val then
      ⟨(arguments.val true).val - (arguments.val false).val,
        (Nat.sub_le _ _).trans_lt (arguments.val true).isLt⟩
    else ⟨(arguments.val false).val - (arguments.val true).val,
      (Nat.sub_le _ _).trans_lt (arguments.val false).isLt⟩

theorem naturalAbsoluteDifference_realizable (width : MvPolynomial Parameter ℕ) :
    (naturalAbsoluteDifference width).Realizable := by
  let inputs : Bool → EncodedDomain Parameter := fun _ => binaryNaturalsOfWidth width
  let minimum sizes (arguments : {arguments : Bool → (binaryNaturalsOfWidth width).Carrier sizes // True}) :=
    if (arguments.val false).val < (arguments.val true).val then arguments.val false else arguments.val true
  let maximum sizes (arguments : {arguments : Bool → (binaryNaturalsOfWidth width).Carrier sizes // True}) :=
    if (arguments.val false).val < (arguments.val true).val then arguments.val true else arguments.val false
  have lower := Realizable.conditional inputs (binaryNaturalsOfWidth width) (fun _ _ => True)
    (fun _ arguments => decide ((arguments.val false).val < (arguments.val true).val))
    (fun _ arguments => arguments.val false) (fun _ arguments => arguments.val true)
    (naturalLess_realizable width) (Realizable.argument inputs false (fun _ _ => True))
    (Realizable.argument inputs true (fun _ _ => True))
  have upper := Realizable.conditional inputs (binaryNaturalsOfWidth width) (fun _ _ => True)
    (fun _ arguments => decide ((arguments.val false).val < (arguments.val true).val))
    (fun _ arguments => arguments.val true) (fun _ arguments => arguments.val false)
    (naturalLess_realizable width) (Realizable.argument inputs true (fun _ _ => True))
    (Realizable.argument inputs false (fun _ _ => True))
  have difference := (naturalSubtract_realizable width).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => if name then minimum sizes arguments else maximum sizes arguments)
    (by
      intro sizes arguments
      change (minimum sizes arguments).val ≤ (maximum sizes arguments).val
      dsimp only [minimum, maximum]
      split <;> simp_all <;> omega)
    (by
      intro name
      cases name
      · change (Computation.mk inputs (binaryNaturalsOfWidth width) (fun _ _ => True) maximum).Realizable
        simpa only [maximum, decide_eq_true_eq] using upper
      · change (Computation.mk inputs (binaryNaturalsOfWidth width) (fun _ _ => True) minimum).Realizable
        simpa only [minimum, decide_eq_true_eq] using lower)
  exact difference.withSpecification (fun _ _ => True) (naturalAbsoluteDifference width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Fin.ext
      change (maximum sizes ⟨arguments, valid⟩).val - (minimum sizes ⟨arguments, valid⟩).val = _
      by_cases smaller : (arguments false).val < (arguments true).val <;>
        simp [maximum, minimum, naturalAbsoluteDifference, smaller])

private theorem sum_magnitude (left right : ℤ) :
    (if SignedEncoding.negative left == SignedEncoding.negative right then left.natAbs + right.natAbs
      else if left.natAbs < right.natAbs then right.natAbs - left.natAbs
      else left.natAbs - right.natAbs) = (left + right).natAbs := by
  have leftMagnitude := SignedEncoding.magnitude_value left
  have rightMagnitude := SignedEncoding.magnitude_value right
  have sumMagnitude := SignedEncoding.magnitude_value (left + right)
  by_cases leftNegative : left < 0 <;> by_cases rightNegative : right < 0 <;>
    by_cases sumNegative : left + right < 0
  all_goals
    simp only [leftNegative, rightNegative, sumNegative, ↓reduceIte] at leftMagnitude rightMagnitude sumMagnitude
    simp [SignedEncoding.negative, leftNegative, rightNegative]
    first | omega | (split_ifs <;> omega)

end Realizable.Internal

theorem integerAdd_realizable (width : MvPolynomial Parameter ℕ) :
    (integerAdd width).Realizable := by
  let inputs := (integerAdd width).inputDomains
  let output := binaryNaturalsOfWidth (width + 1)
  let magnitudeArgument name sizes (arguments : {arguments : (integerAdd width).Arguments sizes // True}) :
      (binaryNaturalsOfWidth width).Carrier sizes :=
    ⟨(arguments.val name).val.natAbs, (arguments.val name).property⟩
  have magnitudes (name : Bool) :
      (Computation.mk inputs (binaryNaturalsOfWidth width) (fun _ _ => True)
        (magnitudeArgument name)).Realizable := by
    exact (integerMagnitude_realizable width).withArguments inputs (MultiTape.oneTape name) (fun _ => rfl)
  let wideMagnitude name sizes arguments := (Realizable.Internal.naturalWiden width 1).compute sizes
    ⟨(fun _ => magnitudeArgument name sizes arguments), trivial⟩
  have wideMagnitudes (name : Bool) :
      (Computation.mk inputs output (fun _ _ => True) (wideMagnitude name)).Realizable := by
    exact (magnitudes name).followedBy (Realizable.Internal.naturalWiden_realizable width 1)
      rfl (by intros; trivial)
  let sum sizes (arguments : {arguments : (integerAdd width).Arguments sizes // True}) : output.Carrier sizes :=
    ⟨(arguments.val false).val.natAbs + (arguments.val true).val.natAbs, by
      have left := (arguments.val false).property
      have right := (arguments.val true).property
      change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
      rw [map_add, map_one, pow_succ]
      omega⟩
  have sumReady : (Computation.mk inputs output (fun _ _ => True) sum).Realizable := by
    exact (Realizable.Internal.naturalAdd_realizable (width + 1)).onResults inputs (fun _ _ => True)
      wideMagnitude (by
        intro sizes arguments
        change (wideMagnitude false sizes arguments).val + (wideMagnitude true sizes arguments).val < _
        exact (sum sizes arguments).isLt) wideMagnitudes
  let difference sizes (arguments : {arguments : (integerAdd width).Arguments sizes // True}) : output.Carrier sizes :=
    if smaller : (arguments.val false).val.natAbs < (arguments.val true).val.natAbs then
      ⟨(arguments.val true).val.natAbs - (arguments.val false).val.natAbs, by
        have bound := (wideMagnitude true sizes arguments).isLt
        change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
        exact (Nat.sub_le _ _).trans_lt bound⟩
    else ⟨(arguments.val false).val.natAbs - (arguments.val true).val.natAbs, by
      have bound := (wideMagnitude false sizes arguments).isLt
      change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
      exact (Nat.sub_le _ _).trans_lt bound⟩
  have differenceReady : (Computation.mk inputs output (fun _ _ => True) difference).Realizable := by
    have small := (Realizable.Internal.naturalAbsoluteDifference_realizable width).onResults
      inputs (fun _ _ => True) magnitudeArgument (by intros; trivial) magnitudes
    have widened := small.followedBy (Realizable.Internal.naturalWiden_realizable width 1)
      rfl (by intros; trivial)
    exact widened.withSpecification (fun _ _ => True) difference (by intros; trivial) (by
      intro sizes arguments valid
      apply Fin.ext
      by_cases smaller : (arguments false).val.natAbs < (arguments true).val.natAbs <;>
        simp [difference, followedBy, Realizable.Internal.naturalWiden, encodingMap, unaryMap,
          onResults, Realizable.Internal.naturalAbsoluteDifference, magnitudeArgument, smaller])
  have signs := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool)
    (fun flags => flags false == flags true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => SignedEncoding.negative (arguments.val name).val)
    (by intros; trivial) (by
      intro name
      exact (integerNegative_realizable width).withArguments inputs (MultiTape.oneTape name) (fun _ => rfl))
  let magnitude sizes (arguments : {arguments : (integerAdd width).Arguments sizes // True}) :=
    if SignedEncoding.negative (arguments.val false).val == SignedEncoding.negative (arguments.val true).val then
      sum sizes arguments else difference sizes arguments
  have magnitudeReady : (Computation.mk inputs output (fun _ _ => True) magnitude).Realizable :=
    Realizable.conditional inputs output (fun _ _ => True) _ sum difference signs sumReady differenceReady
  have magnitudeValue sizes (arguments : {arguments : (integerAdd width).Arguments sizes // True}) :
      (magnitude sizes arguments).val = ((arguments.val false).val + (arguments.val true).val).natAbs := by
    have equation := Realizable.Internal.sum_magnitude (arguments.val false).val (arguments.val true).val
    by_cases same : SignedEncoding.negative (arguments.val false).val = SignedEncoding.negative (arguments.val true).val <;>
      by_cases smaller : (arguments.val false).val.natAbs < (arguments.val true).val.natAbs <;>
      simpa [magnitude, sum, difference, same, smaller] using equation
  have compared := (integerLess_realizable width).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then
      ⟨-(arguments.val true).val, by simpa using (arguments.val true).property⟩ else arguments.val false)
    (by intros; trivial) (by
      intro name
      cases name
      · exact Realizable.argument inputs false (fun _ _ => True)
      · exact (integerNegate_realizable width).withArguments inputs (MultiTape.oneTape true) (fun _ => rfl))
  have negative : (Computation.mk inputs booleans (fun _ _ => True)
      (fun _ arguments => SignedEncoding.negative ((arguments.val false).val + (arguments.val true).val))).Realizable := by
    exact compared.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp [onResults, integerLess, SignedEncoding.negative]
      omega)
  have parts := Realizable.pairOutputs inputs booleans output (fun _ _ => True) _ magnitude negative magnitudeReady
  have constructed := parts.followedBy (Realizable.Internal.integerOfParts_realizable (width + 1)) rfl (by
    intro sizes arguments valid
    change SignedEncoding.negative ((arguments false).val + (arguments true).val) = true →
      (magnitude sizes ⟨arguments, valid⟩).val ≠ 0
    rw [magnitudeValue]
    intro sign zero
    have strictlyNegative : (arguments false).val + (arguments true).val < 0 := of_decide_eq_true sign
    exact (ne_of_lt strictlyNegative) (Int.natAbs_eq_zero.mp zero))
  exact constructed.withSpecification (fun _ _ => True) (integerAdd width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (if SignedEncoding.negative ((arguments false).val + (arguments true).val)
        then -((magnitude sizes ⟨arguments, valid⟩).val : ℤ)
        else ((magnitude sizes ⟨arguments, valid⟩).val : ℤ)) = (arguments false).val + (arguments true).val
      rw [magnitudeValue]
      exact SignedEncoding.restore _)

theorem integerSubtract_realizable (width : MvPolynomial Parameter ℕ) :
    (integerSubtract width).Realizable := by
  let inputs := (integerSubtract width).inputDomains
  have added := (integerAdd_realizable width).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then
      ⟨-(arguments.val true).val, by simpa using (arguments.val true).property⟩ else arguments.val false)
    (by intros; trivial) (by
      intro name
      cases name
      · exact Realizable.argument inputs false (fun _ _ => True)
      · exact (integerNegate_realizable width).withArguments inputs (MultiTape.oneTape true) (fun _ => rfl))
  exact added.withSpecification (fun _ _ => True) (integerSubtract width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      exact (sub_eq_add_neg (arguments false).val (arguments true).val).symm)

end Polytime2.Computation
