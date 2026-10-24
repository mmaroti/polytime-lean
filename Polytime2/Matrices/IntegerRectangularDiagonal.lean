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

import Polytime2.Matrices.RectangularDiagonalMath
import Polytime2.Matrices.Tabulate
import Polytime2.Encoding.IntegerMatrices
import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arrays.Operations

/-! # Constructing rectangular integer diagonal matrices

Input a bounded natural active diagonal and independent full dimensions. Return
the ordinary rectangular integer matrix, with zeros outside that diagonal.
Tabulation uses certified coordinate equality, active-prefix guards, and array
lookup. All output construction costs are included. The constructor is total;
rank bounds are needed only when asserting a full Smith contract.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def zeroWord (width : MvPolynomial Parameter ℕ) :=
  integerBooleanOperationWiden width (Argument := Empty) (fun _ => ⟨0, by decide⟩)

private theorem zeroWord_realizable (width : MvPolynomial Parameter ℕ) : (zeroWord width).Realizable :=
  integerBooleanOperationWiden_realizable width (Argument := Empty) (fun _ => ⟨0, by decide⟩)

private noncomputable def diagonalEntry (rows columns rank width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : ∀ _name : Unit, ((binaryNaturalsOfWidth width).arrayOfLength rank).Carrier sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) (column : Fin (MvPolynomial.eval sizes columns)) :
    (binaryIntegers (width + 1)).Carrier sizes :=
  ⟨IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
    (fun index => (arguments () index).val) row column, by
    apply IntegerMatrix.rectangularDiagonal_bound (MvPolynomial.eval sizes (width + 1)) _ _ row column
    intro index
    exact (arguments () index).isLt.trans_le (pow_le_pow_right₀ (by decide) (by simp only [map_add, map_one]; omega))⟩

private theorem diagonalEntry_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (matrixTabulateStep (fun _ : Unit => (binaryNaturalsOfWidth width).arrayOfLength rank)
      (binaryIntegers (width + 1)) rows columns (diagonalEntry rows columns rank width)).Realizable := by
  let step := matrixTabulateStep (fun _ : Unit => (binaryNaturalsOfWidth width).arrayOfLength rank)
    (binaryIntegers (width + 1)) rows columns (diagonalEntry rows columns rank width)
  let same (_sizes : Parameter → ℕ) (arguments : step.Arguments _sizes) :=
    decide ((arguments (.inr false)).val = (arguments (.inr true)).val)
  have compared := (positionsEqual_realizable rows columns).withArguments step.inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name <;> rfl)
  apply Realizable.ofCases (computation := step) same compared
  · let allowed sizes arguments := step.precondition sizes arguments ∧ same sizes arguments = true
    let active sizes (arguments : step.Arguments sizes) := decide ((arguments (.inr false)).val < MvPolynomial.eval sizes rank)
    have tested := ((positionWithin_realizable rows rank).withArguments step.inputDomains
      (MultiTape.oneTape (.inr false)) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
    apply Realizable.ofCases (computation := step.withPrecondition allowed (fun _ _ valid => valid.1)) active tested
    · let accepted sizes arguments := allowed sizes arguments ∧ active sizes arguments = true
      let inputs (choice : Bool) (sizes : Parameter → ℕ)
          (arguments : {arguments : step.Arguments sizes // accepted sizes arguments}) :
          ((arrayLookupWithIndex (binaryNaturalsOfWidth width) (arrayPosition rows) (fun _ index => index.val) rank).inputDomains choice).Carrier sizes :=
        match choice with
        | false => arguments.val (.inr false)
        | true => arguments.val (.inl ())
      have read := (arrayLookupWithIndex_realizable (binaryNaturalsOfWidth width) (arrayPosition rows)
        (fun _ index => index.val) (arrayPosition_value rows) rank).onResults step.inputDomains accepted inputs
        (by
          intro sizes arguments
          have within := arguments.property.2
          simp only [active, decide_eq_true_eq] at within
          exact within) (by
          intro choice
          cases choice
          · exact Realizable.argument step.inputDomains (.inr false) accepted
          · exact Realizable.argument step.inputDomains (.inl ()) accepted)
      have converted := (read.followedBy (integerOfMagnitude_realizable width) rfl (by intros; trivial)).followedBy
        (integerWiden_realizable width 1) rfl (by intros; trivial)
      apply converted.withSpecification accepted _ (by intros; trivial)
      intro sizes arguments valid
      have equal := of_decide_eq_true valid.1.2
      have within := of_decide_eq_true valid.2
      apply Subtype.ext
      change ((arguments (.inl ()) ⟨(arguments (.inr false)).val, within⟩).val : ℤ) =
        IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
          (fun index => (arguments (.inl ()) index).val) (arguments (.inr false)) (arguments (.inr true))
      simp only [IntegerMatrix.rectangularDiagonal, ite_eq_left equal, dite_eq_left within]
    · let rejected sizes arguments := allowed sizes arguments ∧ active sizes arguments = false
      have zero := (zeroWord_realizable width).onResults step.inputDomains rejected (fun impossible => impossible.elim)
        (by intros; trivial) (fun impossible => impossible.elim)
      apply zero.withSpecification rejected _ (by intros; trivial)
      intro sizes arguments valid
      have outside := of_decide_eq_false valid.2
      apply Subtype.ext
      change (0 : ℤ) = IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        (fun index => (arguments (.inl ()) index).val) (arguments (.inr false)) (arguments (.inr true))
      simp only [IntegerMatrix.rectangularDiagonal, dite_eq_right outside, ite_self]
  · let rejected sizes arguments := step.precondition sizes arguments ∧ same sizes arguments = false
    have zero := (zeroWord_realizable width).onResults step.inputDomains rejected (fun impossible => impossible.elim)
      (by intros; trivial) (fun impossible => impossible.elim)
    apply zero.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    have different := of_decide_eq_false valid.2
    apply Subtype.ext
    change (0 : ℤ) = IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
      (fun index => (arguments (.inl ()) index).val) (arguments (.inr false)) (arguments (.inr true))
    simp only [IntegerMatrix.rectangularDiagonal, ite_eq_right different]

/-- Construct an ordinary rectangular diagonal matrix with zero inactive entries. -/
noncomputable def integerRectangularDiagonal (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (matrixTabulate (fun _ : Unit => (binaryNaturalsOfWidth width).arrayOfLength rank)
    (binaryIntegers (width + 1)) rows columns (diagonalEntry rows columns rank width)).reinterpretOutput
    (integerMatrices rows columns (width + 1))
    (fun sizes => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (width + 1))).symm)

theorem integerRectangularDiagonal_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularDiagonal rows columns rank width).Realizable :=
  (matrixTabulate_realizable (fun _ : Unit => (binaryNaturalsOfWidth width).arrayOfLength rank)
    (binaryIntegers (width + 1)) rows columns (diagonalEntry rows columns rank width)
    (diagonalEntry_realizable rows columns rank width)).reindexOutput
      (integerMatrices rows columns (width + 1)).Carrier
      (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (width + 1)))

/-- The returned matrix is exactly the mathematical rectangular diagonal. -/
theorem integerRectangularDiagonal_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularDiagonal rows columns rank width).Arguments sizes //
      (integerRectangularDiagonal rows columns rank width).precondition sizes arguments}) :
    ((integerRectangularDiagonal rows columns rank width).compute sizes arguments).val =
      IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        (fun index => (arguments.val () index).val) := rfl

end Polytime2.Computation
