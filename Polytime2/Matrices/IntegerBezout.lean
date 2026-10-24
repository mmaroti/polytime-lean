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

import Polytime2.Matrices.BezoutRows

/-! # Certified Bézout elimination on two integer rows

The input is an ordinary bounded rectangular integer matrix, two distinct row
indices, and a column index. The result replaces the selected column entries
by their nonnegative gcd and zero through a unimodular row operation. All
coefficient storage and the sufficient output magnitude width `4*w+3` are
derived internally. Both new rows read the original matrix.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Eliminate the second selected entry with a bounded unimodular Bézout step. -/
noncomputable def integerBezoutRows (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex rows
      | 2 => boundedIndex columns
      | 3 => integerMatrices rows columns width
    outputDomain := integerMatrices rows columns (2 * (2 * width + 1) + 1)
    precondition := fun _ arguments => arguments 0 ≠ arguments 1
    compute := fun sizes arguments => ⟨IntegerMatrix.rowPair (arguments.val 0) (arguments.val 1)
      (IntegerMatrix.bezoutMatrix ((arguments.val 3).val (arguments.val 0) (arguments.val 2))
        ((arguments.val 3).val (arguments.val 1) (arguments.val 2))) (arguments.val 3).val, by
        have wider : 2 ^ MvPolynomial.eval sizes width ≤ 2 ^ (2 * MvPolynomial.eval sizes width + 1) :=
          pow_le_pow_right₀ (by decide) (by omega)
        simp only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat]
        apply IntegerMatrix.rowPair_bound (Row := Fin (MvPolynomial.eval sizes rows))
          (2 * MvPolynomial.eval sizes width + 1) (arguments.val 0) (arguments.val 1)
        · exact IntegerMatrix.bezoutMatrix_bound (MvPolynomial.eval sizes width) _ _
            ((arguments.val 3).property (arguments.val 0) (arguments.val 2))
            ((arguments.val 3).property (arguments.val 1) (arguments.val 2))
        · exact fun row column => ((arguments.val 3).property row column).trans_le wider⟩ }

theorem integerBezoutRows_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutRows rows columns width).Realizable := by
  classical
  let computation := integerBezoutRows rows columns width
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  have prepared := (Realizable.Internal.BezoutRows.coefficients_realizable rows columns width).withPrecondition
    allowed (by intros; trivial)
  let domains := Sum.elim inputs (fun _ : Unit => Realizable.Internal.BezoutCoefficients.domain width)
  let selection : Fin 4 ↪ Fin 4 ⊕ Unit :=
    ⟨(fun name => match name with | 0 => .inl 0 | 1 => .inl 1 | 2 => .inr () | 3 => .inl 3), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> simp_all⟩
  have transformed := (Realizable.Internal.BezoutRows.application_realizable rows columns width).withArguments
    domains selection (by intro name; fin_cases name <;> rfl)
  have complete := prepared.letThen transformed (fun _ => rfl) rfl (by intros; assumption)
  apply complete.withSpecification allowed computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Subtype.ext
  let coefficientArguments : (Realizable.Internal.BezoutCoefficients.computation width).Arguments sizes :=
    fun choice => ⟨(arguments 3).val (if choice then arguments 1 else arguments 0) (arguments 2),
      (arguments 3).property _ _⟩
  change IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (arguments 0) (arguments 1)
    !![((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 0).val,
      ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 1).val;
      ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 2).val,
      ((Realizable.Internal.BezoutCoefficients.computation width).compute sizes ⟨coefficientArguments, trivial⟩ 3).val]
      (arguments 3).val = _
  erw [Realizable.Internal.BezoutCoefficients.compute_matrix]
  rfl

/-- The selected entries become the gcd and zero. -/
theorem integerBezoutRows_eliminates (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutRows rows columns width).Arguments sizes //
      (integerBezoutRows rows columns width).precondition sizes arguments}) :
    let result := ((integerBezoutRows rows columns width).compute sizes arguments).val
    result (arguments.val 0) (arguments.val 2) =
      (Int.gcd ((arguments.val 3).val (arguments.val 0) (arguments.val 2))
        ((arguments.val 3).val (arguments.val 1) (arguments.val 2)) : ℤ) ∧
      result (arguments.val 1) (arguments.val 2) = 0 := by
  exact IntegerMatrix.rowPair_bezout (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) arguments.property
    (arguments.val 3).val (arguments.val 2)


/-- The column version reuses the same Bézout step through transposition. -/
noncomputable def integerBezoutColumns (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex columns
      | 2 => boundedIndex rows
      | 3 => integerMatrices rows columns width
    outputDomain := integerMatrices rows columns (2 * (2 * width + 1) + 1)
    precondition := fun _ arguments => arguments 0 ≠ arguments 1
    compute := fun sizes arguments =>
      let coefficients := IntegerMatrix.bezoutMatrix ((arguments.val 3).val (arguments.val 2) (arguments.val 0))
        ((arguments.val 3).val (arguments.val 2) (arguments.val 1))
      ⟨(IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes columns))
        (Column := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1) coefficients
        (arguments.val 3).val.transpose).transpose, by
        have wider : 2 ^ MvPolynomial.eval sizes width ≤ 2 ^ (2 * MvPolynomial.eval sizes width + 1) :=
          pow_le_pow_right₀ (by decide) (by omega)
        simp only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat]
        have bound := IntegerMatrix.rowPair_bound (Row := Fin (MvPolynomial.eval sizes columns))
          (2 * MvPolynomial.eval sizes width + 1) (arguments.val 0) (arguments.val 1) coefficients
          (arguments.val 3).val.transpose
          (IntegerMatrix.bezoutMatrix_bound (MvPolynomial.eval sizes width) _ _
            ((arguments.val 3).property (arguments.val 2) (arguments.val 0))
            ((arguments.val 3).property (arguments.val 2) (arguments.val 1)))
          (fun column row => ((arguments.val 3).property row column).trans_le wider)
        exact fun row column => bound column row⟩ }

theorem integerBezoutColumns_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutColumns rows columns width).Realizable := by
  let computation := integerBezoutColumns rows columns width
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  have transposed := ((integerMatrixTranspose_realizable rows columns width).withArguments inputs
    (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  have eliminated := (integerBezoutRows_realizable columns rows width).onResults inputs allowed
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => (integerMatrixTranspose rows columns width).compute sizes ⟨(fun _ => arguments.val 3), trivial⟩)
    (fun _ arguments => arguments.property) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs 0 allowed
      · exact Realizable.argument inputs 1 allowed
      · exact Realizable.argument inputs 2 allowed
      · exact transposed)
  have complete := eliminated.followedBy
    (integerMatrixTranspose_realizable columns rows (2 * (2 * width + 1) + 1)) rfl (by intros; trivial)
  exact complete.withSpecification allowed computation.compute (by intros; assumption) (by intros; rfl)

theorem integerBezoutColumns_eliminates (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutColumns rows columns width).Arguments sizes //
      (integerBezoutColumns rows columns width).precondition sizes arguments}) :
    let result := ((integerBezoutColumns rows columns width).compute sizes arguments).val
    result (arguments.val 2) (arguments.val 0) =
      (Int.gcd ((arguments.val 3).val (arguments.val 2) (arguments.val 0))
        ((arguments.val 3).val (arguments.val 2) (arguments.val 1)) : ℤ) ∧
      result (arguments.val 2) (arguments.val 1) = 0 := by
  exact IntegerMatrix.rowPair_bezout (Row := Fin (MvPolynomial.eval sizes columns))
    (Column := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1) arguments.property
      (arguments.val 3).val.transpose (arguments.val 2)


/-- The row step has an explicit unimodular left transformation. -/
theorem integerBezoutRows_equation (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutRows rows columns width).Arguments sizes //
      (integerBezoutRows rows columns width).precondition sizes arguments}) :
    let coefficients := IntegerMatrix.bezoutMatrix ((arguments.val 3).val (arguments.val 0) (arguments.val 2))
      ((arguments.val 3).val (arguments.val 1) (arguments.val 2))
    let left := IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1) coefficients
      (1 : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    left * (arguments.val 3).val = ((integerBezoutRows rows columns width).compute sizes arguments).val ∧
      IsUnit left.det := by
  constructor
  · exact (IntegerMatrix.rowPair_eq_mul (Row := Fin (MvPolynomial.eval sizes rows))
      (arguments.val 0) (arguments.val 1) _ (arguments.val 3).val).symm
  · exact IntegerMatrix.rowPair_unimodular (Row := Fin (MvPolynomial.eval sizes rows))
      (arguments.val 0) (arguments.val 1) arguments.property _ (IntegerMatrix.bezoutMatrix_det _ _)

/-- The column step has an explicit unimodular right transformation. -/
theorem integerBezoutColumns_equation (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBezoutColumns rows columns width).Arguments sizes //
      (integerBezoutColumns rows columns width).precondition sizes arguments}) :
    let coefficients := IntegerMatrix.bezoutMatrix ((arguments.val 3).val (arguments.val 2) (arguments.val 0))
      ((arguments.val 3).val (arguments.val 2) (arguments.val 1))
    let right := (IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) coefficients
      (1 : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)).transpose
    (arguments.val 3).val * right = ((integerBezoutColumns rows columns width).compute sizes arguments).val ∧
      IsUnit right.det := by
  constructor
  · have equation := IntegerMatrix.rowPair_eq_mul (Row := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1)
      (IntegerMatrix.bezoutMatrix ((arguments.val 3).val (arguments.val 2) (arguments.val 0))
        ((arguments.val 3).val (arguments.val 2) (arguments.val 1))) (arguments.val 3).val.transpose
    simpa only [integerBezoutColumns, Matrix.transpose_mul, Matrix.transpose_transpose] using (congrArg Matrix.transpose equation).symm
  · simp only [Matrix.det_transpose]
    exact IntegerMatrix.rowPair_unimodular (Row := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) arguments.property _ (IntegerMatrix.bezoutMatrix_det _ _)

end Polytime2.Computation
