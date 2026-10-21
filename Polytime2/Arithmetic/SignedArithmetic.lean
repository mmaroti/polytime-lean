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

import Polytime2.Arithmetic.SignedConstruction
import Polytime2.Arithmetic.BitComparison

/-! # Exact mathematical contracts for signed arithmetic

Inputs have magnitude width `w`. Negation and Euclidean quotient/remainder
retain that width; sums and differences use `w+1`, and products use `2*w`.
All intermediate storage requirements belong to the realization proofs.
Division requires a nonzero divisor and returns the Euclidean remainder,
including when either operand is negative.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Canonical zero testing accepts every bounded integer. -/
noncomputable def integerIsZero (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryIntegers width) booleans (fun _ _ => True)
    (fun _ value => decide (value.val.val = 0))

theorem integerIsZero_realizable (width : MvPolynomial Parameter ℕ) :
    (integerIsZero width).Realizable := by
  have magnitude := (integerMagnitude_realizable width).followedBy
    (Realizable.Internal.naturalNonzero_realizable width) rfl (by intros; trivial)
  have inverted := magnitude.followedBy
    (booleanOperation_realizable (Parameter := Parameter) (Argument := Unit) (fun flags => !flags ()))
    rfl (by intros; trivial)
  exact inverted.withSpecification (fun _ _ => True) (integerIsZero width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp [integerIsZero, followedBy, integerMagnitude, Realizable.Internal.naturalNonzero,
        booleanOperation, unaryMap, Int.natAbs_eq_zero])

noncomputable def integerNegate (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryIntegers width) (binaryIntegers width) (fun _ _ => True)
    (fun _ value => ⟨-value.val.val, by simpa using value.val.property⟩)

theorem integerNegate_realizable (width : MvPolynomial Parameter ℕ) :
    (integerNegate width).Realizable := by
  let inputs := (integerNegate width).inputDomains
  have negative := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool)
    (fun flags => !flags false && !flags true)).onResults inputs (fun _ _ => True)
    (fun name _ arguments => if name then decide ((arguments.val ()).val = 0)
      else SignedEncoding.negative (arguments.val ()).val)
    (by intros; trivial) (by
      intro name
      cases name
      · exact integerNegative_realizable width
      · exact integerIsZero_realizable width)
  have parts := Realizable.pairOutputs inputs booleans (binaryNaturalsOfWidth width) (fun _ _ => True)
    _ _ negative (integerMagnitude_realizable width)
  have constructed := parts.followedBy (Realizable.Internal.integerOfParts_realizable width) rfl (by
    intro sizes arguments valid
    change (!SignedEncoding.negative (arguments ()).val && !decide ((arguments ()).val = 0)) = true →
      (arguments ()).val.natAbs ≠ 0
    intro sign zero
    have valueZero := Int.natAbs_eq_zero.mp zero
    simp [valueZero] at sign)
  exact constructed.withSpecification (fun _ _ => True) (integerNegate width).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (if !SignedEncoding.negative (arguments ()).val && !decide ((arguments ()).val = 0)
        then -((arguments ()).val.natAbs : ℤ) else ((arguments ()).val.natAbs : ℤ)) = -(arguments ()).val
      by_cases negative : (arguments ()).val < 0
      · have magnitude := Int.natAbs_of_nonneg (show 0 ≤ -(arguments ()).val by omega)
        simp only [Int.natAbs_neg] at magnitude
        simp [SignedEncoding.negative, negative, magnitude]
      · have magnitude := Int.natAbs_of_nonneg (show 0 ≤ (arguments ()).val by omega)
        by_cases zero : (arguments ()).val = 0
        · simp [zero, SignedEncoding.negative]
        · simp [SignedEncoding.negative, negative, zero, magnitude])

noncomputable def integerAdd (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers (width + 1)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val false).val + (arguments.val true).val, by
    have bound := Int.natAbs_add_le (arguments.val false).val (arguments.val true).val
    have left := (arguments.val false).property
    have right := (arguments.val true).property
    change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
    simp only [map_add, map_one, pow_succ]
    omega⟩

noncomputable def integerSubtract (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers (width + 1)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val false).val - (arguments.val true).val, by
    have bound := Int.natAbs_sub_le (arguments.val false).val (arguments.val true).val
    have left := (arguments.val false).property
    have right := (arguments.val true).property
    change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
    simp only [map_add, map_one, pow_succ]
    omega⟩

noncomputable def integerMultiply (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers (2 * width)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val false).val * (arguments.val true).val, by
    rw [Int.natAbs_mul]
    have bound := Nat.mul_lt_mul'' (arguments.val false).property (arguments.val true).property
    rw [two_mul, map_add, pow_add]
    exact bound⟩

noncomputable def integerDivision (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (binaryIntegers width).prod (binaryIntegers width)
  precondition _ arguments := (arguments true).val ≠ 0
  compute _ arguments :=
    (⟨(arguments.val false).val / (arguments.val true).val,
      (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments.val false).property⟩,
     ⟨(arguments.val false).val % (arguments.val true).val, by
      have smaller := Int.emod_lt (arguments.val false).val arguments.property
      have magnitude := Int.natAbs_of_nonneg (Int.emod_nonneg (arguments.val false).val arguments.property)
      have bound := (arguments.val true).property
      omega⟩)

theorem integerDivision_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerDivision width).Arguments sizes)
    (valid : (integerDivision width).precondition sizes arguments) :
    let answer := (integerDivision width).compute sizes ⟨arguments, valid⟩
    (arguments false).val = (arguments true).val * answer.1.val + answer.2.val ∧
      0 ≤ answer.2.val ∧ answer.2.val < ((arguments true).val.natAbs : ℤ) := by
  exact ⟨by simpa [integerDivision, mul_comm, add_comm] using
      (Int.emod_add_ediv_mul (arguments false).val (arguments true).val).symm,
    Int.emod_nonneg _ valid, Int.emod_lt _ valid⟩

end Polytime2.Computation
