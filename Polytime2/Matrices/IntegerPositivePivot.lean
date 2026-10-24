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

import Polytime2.Matrices.IntegerNegate
import Polytime2.Matrices.HermitePivotMath
import Polytime2.Arithmetic.SignedOperations

/-! # Certified pivot sign normalization with its actual basis

Read the selected matrix entry. If it is negative, negate its row in both the
matrix and the left basis; otherwise retain both. Magnitude widths stay fixed.
The selected entry becomes its absolute value, including at zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Normalize a selected pivot sign, tracking the same row action on the basis. -/
noncomputable def integerPositivePivotWithLeft (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) where
  inputDomains | 0 => boundedIndex rows | 1 => boundedIndex columns
               | 2 => integerMatrices rows columns width | 3 => integerMatrices rows rows width
  outputDomain := (integerMatrices rows columns width).prod (integerMatrices rows rows width)
  precondition _ _ := True
  compute sizes arguments :=
    let result := IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val
    have bound := IntegerMatrix.positivePivotWithLeft_bound (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width)
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
      (arguments.val 2).property (arguments.val 3).property
    (⟨result.1, bound.1⟩, ⟨result.2, bound.2⟩)

/-- The result retains the exact mathematical row action on both matrices. -/
theorem integerPositivePivotWithLeft_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerPositivePivotWithLeft rows columns width).Arguments sizes //
      (integerPositivePivotWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerPositivePivotWithLeft rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.positivePivotWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val := rfl

theorem integerPositivePivotWithLeft_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerPositivePivotWithLeft rows columns width).Realizable := by
  let computation := integerPositivePivotWithLeft rows columns width
  let condition sizes (arguments : computation.Arguments sizes) :=
    decide ((arguments 2).val (arguments 0) (arguments 1) < 0)
  have entry := (integerMatrixEntry_realizable rows columns width).withArguments computation.inputDomains
    (Fin.castLEEmb (by decide : 3 ≤ 4)) (by intro name; fin_cases name <;> rfl)
  have guard := entry.followedBy (integerNegative_realizable width) rfl (by intros; trivial)
  apply Realizable.ofCases condition guard
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have matrix := (integerRowNegate_realizable rows columns width).onResults computation.inputDomains allowed
      (fun choice _ arguments => match choice with | false => arguments.val 0 | true => arguments.val 2)
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact Realizable.argument computation.inputDomains 0 allowed
        · exact Realizable.argument computation.inputDomains 2 allowed)
    have basis := (integerRowNegate_realizable rows rows width).onResults computation.inputDomains allowed
      (fun choice _ arguments => match choice with | false => arguments.val 0 | true => arguments.val 3)
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact Realizable.argument computation.inputDomains 0 allowed
        · exact Realizable.argument computation.inputDomains 3 allowed)
    have paired := Realizable.pairOutputs computation.inputDomains _ _ allowed _ _ matrix basis
    apply paired.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, arguments.property.1⟩) (by intros; assumption)
    intro sizes arguments valid
    have negative : (arguments 2).val (arguments 0) (arguments 1) < 0 := of_decide_eq_true valid.2
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [computation, integerPositivePivotWithLeft, IntegerMatrix.positivePivotWithLeft, ite_eq_left negative,
        integerRowNegate]
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have copied := Realizable.pairOutputs computation.inputDomains _ _ allowed _ _
      (Realizable.argument computation.inputDomains 2 allowed) (Realizable.argument computation.inputDomains 3 allowed)
    apply copied.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, arguments.property.1⟩) (by intros; assumption)
    intro sizes arguments valid
    have nonnegative : ¬ (arguments 2).val (arguments 0) (arguments 1) < 0 := of_decide_eq_false valid.2
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [computation, integerPositivePivotWithLeft, IntegerMatrix.positivePivotWithLeft, ite_eq_right nonnegative]

/-- The selected entry is nonnegative and equals its original absolute value. -/
theorem integerPositivePivotWithLeft_entry (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerPositivePivotWithLeft rows columns width).Arguments sizes //
      (integerPositivePivotWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerPositivePivotWithLeft rows columns width).compute sizes arguments
    result.1.val (arguments.val 0) (arguments.val 1) = |(arguments.val 2).val (arguments.val 0) (arguments.val 1)| :=
  IntegerMatrix.positivePivotWithLeft_entry _ _ _ _

/-- The actual returned basis retains the original presentation and unimodularity. -/
theorem integerPositivePivotWithLeft_preserves (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerPositivePivotWithLeft rows columns width).Arguments sizes //
      (integerPositivePivotWithLeft rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 3).val * original * right = (arguments.val 2).val)
    (unit : IsUnit (arguments.val 3).val.det) :
    let result := (integerPositivePivotWithLeft rows columns width).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det :=
  IntegerMatrix.positivePivotWithLeft_preserves _ _ _ _ _ _ equation unit

end Polytime2.Computation
