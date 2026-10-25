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

import Polytime2.Computation.Specification
import Polytime2.Matrices.RectangularDiagonalMath
import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.Tabulate
import Polytime2.Arrays.PositionArithmetic

/-! # Extending an active integer basis by identity

Input an ordinary bounded square basis and a full dimension containing its
active coordinates. Return the active basis with identity on the complementary
coordinates and zero cross blocks. The output word width is derived internally;
even zero-width active entries allow the complementary identity. Certified
coordinate guards protect active matrix reads, and tabulation constructs the
entire ordinary output matrix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def basisEntry (dimension rank width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ _name : Unit, (integerMatrices rank rank width).Carrier sizes)
    (row column : Fin (MvPolynomial.eval sizes dimension)) : (binaryIntegers (width + 1)).Carrier sizes :=
  ⟨if rowActive : row.val < MvPolynomial.eval sizes rank then
      if columnActive : column.val < MvPolynomial.eval sizes rank then
        (arguments ()).val ⟨row.val, rowActive⟩ ⟨column.val, columnActive⟩ else 0
    else if row.val = column.val then 1 else 0, by
    split_ifs
    · exact ((arguments ()).property _ _).trans_le
        (pow_le_pow_right₀ (by decide) (by simp only [map_add, map_one]; omega))
    · simp
    · simpa only [Int.natAbs_one] using
        (Nat.one_lt_two_pow (show MvPolynomial.eval sizes (width + 1) ≠ 0 by simp only [map_add, map_one]; omega))
    · simp⟩

private theorem basisEntry_realizable (dimension rank width : MvPolynomial Parameter ℕ) :
    (matrixTabulateStep (fun _ : Unit => integerMatrices rank rank width) (binaryIntegers (width + 1))
      dimension dimension (basisEntry dimension rank width)).Realizable := by
  let step := matrixTabulateStep (fun _ : Unit => integerMatrices rank rank width) (binaryIntegers (width + 1))
    dimension dimension (basisEntry dimension rank width)
  let rowActive sizes (arguments : step.Arguments sizes) :=
    decide ((arguments (.inr false)).val < MvPolynomial.eval sizes rank)
  have rowTest := (positionWithin_realizable dimension rank).withArguments step.inputDomains
    (MultiTape.oneTape (.inr false)) (fun _ => rfl)
  apply Realizable.ofCases (computation := step) rowActive rowTest
  · let allowed sizes arguments := step.precondition sizes arguments ∧ rowActive sizes arguments = true
    let columnActive sizes (arguments : step.Arguments sizes) :=
      decide ((arguments (.inr true)).val < MvPolynomial.eval sizes rank)
    have columnTest := ((positionWithin_realizable dimension rank).withArguments step.inputDomains
      (MultiTape.oneTape (.inr true)) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
    apply Realizable.ofCases (computation := step.withPrecondition allowed (fun _ _ valid => valid.1)) columnActive columnTest
    · let accepted sizes arguments := allowed sizes arguments ∧ columnActive sizes arguments = true
      let rowWithin sizes (arguments : {arguments : step.Arguments sizes // accepted sizes arguments}) :
          (arguments.val (.inr false)).val < MvPolynomial.eval sizes rank := by
        have within := arguments.property.1.2
        simpa only [rowActive, decide_eq_true_eq] using within
      let rowInputs (choice : Bool) (sizes : Parameter → ℕ)
          (arguments : {arguments : step.Arguments sizes // accepted sizes arguments}) :
          ((integerMatrixRowWithIndex rank rank width (arrayPosition dimension) (fun _ index => index.val)).inputDomains choice).Carrier sizes :=
        match choice with
        | false => arguments.val (.inr false)
        | true => arguments.val (.inl ())
      have row := (integerMatrixRowWithIndex_realizable rank rank width (arrayPosition dimension)
        (fun _ index => index.val) (arrayPosition_value dimension)).onResults step.inputDomains accepted rowInputs
        (fun sizes arguments => rowWithin sizes arguments) (by
          intro choice
          cases choice
          · exact Realizable.argument step.inputDomains (.inr false) accepted
          · exact Realizable.argument step.inputDomains (.inl ()) accepted)
      let entryInputs (choice : Bool) (sizes : Parameter → ℕ)
          (arguments : {arguments : step.Arguments sizes // accepted sizes arguments}) :
          ((arrayLookupWithIndex (binaryIntegers width) (arrayPosition dimension) (fun _ index => index.val) rank).inputDomains choice).Carrier sizes :=
        match choice with
        | false => arguments.val (.inr true)
        | true => fun column => ⟨(arguments.val (.inl ())).val
            ⟨(arguments.val (.inr false)).val, rowWithin sizes arguments⟩ column,
            (arguments.val (.inl ())).property _ column⟩
      have entry := (arrayLookupWithIndex_realizable (binaryIntegers width) (arrayPosition dimension)
        (fun _ index => index.val) (arrayPosition_value dimension) rank).onResults step.inputDomains accepted entryInputs (by
          intro sizes arguments
          have within := arguments.property.2
          simp only [columnActive, decide_eq_true_eq] at within
          exact within) (by
            intro choice
            cases choice
            · exact Realizable.argument step.inputDomains (.inr true) accepted
            · exact row)
      have widened := entry.followedBy (integerWiden_realizable width 1) rfl (by intros; trivial)
      apply widened.withSpecification accepted _ (by intros; trivial)
      intro sizes arguments valid
      have rowWithin := valid.1.2
      have columnWithin := valid.2
      simp only [rowActive, decide_eq_true_eq] at rowWithin
      simp only [columnActive, decide_eq_true_eq] at columnWithin
      apply Subtype.ext
      change (arguments (.inl ())).val ⟨(arguments (.inr false)).val, rowWithin⟩
        ⟨(arguments (.inr true)).val, columnWithin⟩ = _
      simp only [step, Computation.withPrecondition, matrixTabulateStep, basisEntry,
        dite_eq_left rowWithin, dite_eq_left columnWithin]
    · let rejected sizes arguments := allowed sizes arguments ∧ columnActive sizes arguments = false
      have zero := (integerBooleanOperationWiden_realizable width (Argument := Empty) (fun _ => ⟨0, by decide⟩)).onResults
        step.inputDomains rejected (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
      apply zero.withSpecification rejected _ (by intros; trivial)
      intro sizes arguments valid
      have rowWithin := valid.1.2
      have columnOutside := valid.2
      simp only [rowActive, decide_eq_true_eq] at rowWithin
      simp only [columnActive, decide_eq_false_iff_not] at columnOutside
      apply Subtype.ext
      change (0 : ℤ) = _
      simp only [step, Computation.withPrecondition, matrixTabulateStep, basisEntry,
        dite_eq_left rowWithin, dite_eq_right columnOutside]
  · let rejected sizes arguments := step.precondition sizes arguments ∧ rowActive sizes arguments = false
    let identityValue (flags : Unit → Bool) : {value : ℤ // value.natAbs < 2} :=
      if flags () then ⟨1, by decide⟩ else ⟨0, by decide⟩
    have compared := ((positionsEqual_realizable dimension dimension).withArguments step.inputDomains
      ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name <;> rfl)).withPrecondition rejected (by intros; trivial)
    have identity := compared.followedBy (integerBooleanOperationWiden_realizable width identityValue) rfl (by intros; trivial)
    apply identity.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    have outside := valid.2
    simp only [rowActive, decide_eq_false_iff_not] at outside
    apply Subtype.ext
    change (identityValue (fun _ => decide ((arguments (.inr false)).val = (arguments (.inr true)).val))).val = _
    by_cases equal : (arguments (.inr false)).val = (arguments (.inr true)).val
    · have columnOutside : ¬(arguments (.inr true)).val < MvPolynomial.eval sizes rank := by
        rw [← equal]
        exact outside
      simp [identityValue, equal, step, matrixTabulateStep, basisEntry, outside, columnOutside]
    · simp [identityValue, equal, step, matrixTabulateStep, basisEntry, outside]

/-- Extend a bounded active square basis by identity on the remaining coordinates. -/
private noncomputable def implementation (dimension rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((matrixTabulate (fun _ : Unit => integerMatrices rank rank width) (binaryIntegers (width + 1)) dimension dimension
    (basisEntry dimension rank width)).reinterpretOutput (integerMatrices dimension dimension (width + 1))
      (fun sizes => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (width + 1))).symm)).withPrecondition
    (fun sizes _ => MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes dimension) (by intros; trivial)

private theorem implementation_realizable (dimension rank width : MvPolynomial Parameter ℕ) :
    (implementation dimension rank width).Realizable :=
  ((matrixTabulate_realizable (fun _ : Unit => integerMatrices rank rank width) (binaryIntegers (width + 1)) dimension dimension
    (basisEntry dimension rank width) (basisEntry_realizable dimension rank width)).reindexOutput
      (integerMatrices dimension dimension (width + 1)).Carrier
      (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (width + 1)))).withPrecondition
        (fun sizes _ => MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes dimension) (by intros; trivial)

/-- The ordinary output matrix is the mathematical basis extension. -/
private theorem implementation_correct (dimension rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation dimension rank width).Arguments sizes //
      (implementation dimension rank width).precondition sizes arguments}) :
    ((implementation dimension rank width).compute sizes arguments).val =
      IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes dimension) arguments.property (arguments.val ()).val := by
  ext row column
  rw [IntegerMatrix.extendDiagonalBasis_apply]
  rfl

/-- The ordinary mathematical result, with traversal and codec preparation
kept behind the computation boundary. -/
noncomputable def extendIntegerBasis (dimension rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => integerMatrices rank rank width) (integerMatrices dimension dimension (width + 1))
    (fun sizes _ => MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes dimension) (fun _ result => result.val)
    (fun sizes arguments => IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes dimension) arguments.property (arguments.val ()).val)
    (fun sizes arguments => ⟨(implementation dimension rank width).compute sizes arguments,
      implementation_correct dimension rank width sizes arguments⟩)

theorem extendIntegerBasis_realizable (dimension rank width : MvPolynomial Parameter ℕ) :
    (extendIntegerBasis dimension rank width).Realizable := by
  apply (implementation_realizable dimension rank width).specificationBy
  · intro sizes
    exact Subtype.val_injective
  · intro sizes arguments valid
    exact implementation_correct dimension rank width sizes ⟨arguments, valid⟩

/-- Observe the mathematical result without unfolding its finite traversal. -/
theorem extendIntegerBasis_correct (dimension rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (extendIntegerBasis dimension rank width).Arguments sizes //
      (extendIntegerBasis dimension rank width).precondition sizes arguments}) :
    ((extendIntegerBasis dimension rank width).compute sizes arguments).val =
      IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes dimension) arguments.property (arguments.val ()).val := by
  exact specificationBy_correct _ (extendIntegerBasis dimension rank width).outputDomain _
    (fun _ result => result.val) _ _ sizes arguments

end Polytime2.Computation
