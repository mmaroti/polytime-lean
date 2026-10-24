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

import Polytime2.Matrices.DiagonalCoefficients
import Polytime2.Encoding.IntegerMatrices
import Polytime2.Arithmetic.SignedGcdLcm

/-! # Certified diagonal-pair transformations as mathematical matrices

Every pair of signed integers at magnitude width `w` is admissible. The output
is the actual pair of two-by-two unimodular matrices that changes the input
diagonal to its gcd and signed lcm. Left and right coefficient widths `2*w+1`
and `2*(2*w+1)` are derived internally. Their canonical row-major encodings
reuse the existing coefficient records through mathematical equivalences. The
complete pair step also returns the gcd and signed lcm at widths `w` and `2*w`,
including the zero pair.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private def boundedMatrixRecordEquiv (bound : ℕ) :
    {matrix : Matrix (Fin 2) (Fin 2) ℤ // ∀ row column, (matrix row column).natAbs < bound} ≃
      (Fin 4 → {value : ℤ // value.natAbs < bound}) :=
  (IntegerMatrix.entryBoundEquiv bound).trans
    ((Equiv.curry (Fin 2) (Fin 2) {value : ℤ // value.natAbs < bound}).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)))

/-- Compute the actual left and right unimodular matrices for a two-entry diagonal. -/
noncomputable def integerDiagonalPairCoefficients (width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (Realizable.Internal.DiagonalCoefficients.computation width).outputDomain.reindex
    (fun sizes =>
      {matrix : Matrix (Fin 2) (Fin 2) ℤ // ∀ row column, (matrix row column).natAbs <
        2 ^ MvPolynomial.eval sizes (2 * width + 1)} ×
      {matrix : Matrix (Fin 2) (Fin 2) ℤ // ∀ row column, (matrix row column).natAbs <
        2 ^ MvPolynomial.eval sizes (2 * (2 * width + 1))})
    (fun sizes => (boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * width + 1))).prodCongr
      (boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * (2 * width + 1)))))
  precondition _ _ := True
  compute sizes arguments :=
    (⟨IntegerMatrix.bezoutMatrix (arguments.val false).val (arguments.val true).val, by
      simpa only [map_add, map_mul, map_one, MvPolynomial.eval_ofNat] using
        IntegerMatrix.bezoutMatrix_bound (MvPolynomial.eval sizes width) _ _
          (arguments.val false).property (arguments.val true).property⟩,
      ⟨IntegerMatrix.diagonalPairRight (arguments.val false).val (arguments.val true).val, by
        simpa only [map_add, map_mul, map_one, MvPolynomial.eval_ofNat] using
          IntegerMatrix.diagonalPairRight_bound (MvPolynomial.eval sizes width) _ _
            (arguments.val false).property (arguments.val true).property⟩)

theorem integerDiagonalPairCoefficients_realizable (width : MvPolynomial Parameter ℕ) :
    (integerDiagonalPairCoefficients width).Realizable := by
  let computation := integerDiagonalPairCoefficients width
  have result := (Realizable.Internal.DiagonalCoefficients.realizable width).reindexOutput
    computation.outputDomain.Carrier
    (fun sizes => (boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * width + 1))).prodCongr
      (boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * (2 * width + 1)))))
  apply result.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  have matrices := Realizable.Internal.DiagonalCoefficients.compute_matrices width sizes ⟨arguments, valid⟩
  apply Prod.ext
  · apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column
    · exact congrFun (congrFun matrices.1 0) 0
    · exact congrFun (congrFun matrices.1 0) 1
    · exact congrFun (congrFun matrices.1 1) 0
    · exact congrFun (congrFun matrices.1 1) 1
  · apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column
    · exact congrFun (congrFun matrices.2 0) 0
    · exact congrFun (congrFun matrices.2 0) 1
    · exact congrFun (congrFun matrices.2 1) 0
    · exact congrFun (congrFun matrices.2 1) 1

/-- The returned matrices transform the input diagonal, including signed and zero entries. -/
theorem integerDiagonalPairCoefficients_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (integerDiagonalPairCoefficients width).Arguments sizes // True}) :
    let result := (integerDiagonalPairCoefficients width).compute sizes arguments
    result.1.val * !![(arguments.val false).val, 0; 0, (arguments.val true).val] * result.2.val =
      !![(Int.gcd (arguments.val false).val (arguments.val true).val : ℤ), 0;
        0, (arguments.val false).val / (Int.gcd (arguments.val false).val (arguments.val true).val : ℤ) *
          (arguments.val true).val] ∧ result.1.val.det = 1 ∧ result.2.val.det = 1 :=
  ⟨IntegerMatrix.diagonalPair_equation _ _, IntegerMatrix.bezoutMatrix_det _ _, IntegerMatrix.diagonalPairRight_det _ _⟩

/-- Return both normalized diagonal entries and the actual left and right transformations. -/
noncomputable def integerDiagonalPair (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains := (integerGcdLcm width).inputDomains
  outputDomain := (integerGcdLcm width).outputDomain.prod (integerDiagonalPairCoefficients width).outputDomain
  precondition _ _ := True
  compute sizes arguments := ((integerGcdLcm width).compute sizes arguments,
    (integerDiagonalPairCoefficients width).compute sizes arguments)

theorem integerDiagonalPair_realizable (width : MvPolynomial Parameter ℕ) : (integerDiagonalPair width).Realizable :=
  Realizable.pairOutputs _ _ _ (fun _ _ => True) _ _
    (integerGcdLcm_realizable width) (integerDiagonalPairCoefficients_realizable width)

/-- The complete step certifies its returned diagonal and both determinant-one witnesses. -/
theorem integerDiagonalPair_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (integerDiagonalPair width).Arguments sizes // True}) :
    let result := (integerDiagonalPair width).compute sizes arguments
    result.2.1.val * !![(arguments.val false).val, 0; 0, (arguments.val true).val] * result.2.2.val =
      !![result.1.1.val, 0; 0, result.1.2.val] ∧ result.2.1.val.det = 1 ∧ result.2.2.val.det = 1 :=
  integerDiagonalPairCoefficients_correct width sizes arguments

/-- Select a mathematical coefficient without exposing the internal record layout. -/
noncomputable def Realizable.Internal.diagonalCoefficientEntry (width : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) (row column : Fin 2) : Computation Parameter Unit where
  inputDomains _ := (integerDiagonalPairCoefficients width).outputDomain
  outputDomain := binaryIntegers (if chooseRight then 2 * (2 * width + 1) else 2 * width + 1)
  precondition _ _ := True
  compute _ arguments := match chooseRight with
    | false => ⟨(arguments.val ()).1.val row column, (arguments.val ()).1.property row column⟩
    | true => ⟨(arguments.val ()).2.val row column, (arguments.val ()).2.property row column⟩

theorem Realizable.Internal.diagonalCoefficientEntry_realizable (width : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) (row column : Fin 2) :
    (diagonalCoefficientEntry width chooseRight row column).Realizable := by
  let computation := diagonalCoefficientEntry width chooseRight row column
  let left := BezoutCoefficients.domain width
  let right := DiagonalCoefficients.rightDomain width
  have selected := (pairProjection_realizable left right chooseRight).followedBy
    (recordProjection_realizable 4
      (fun _ => binaryIntegers (if chooseRight then 2 * (2 * width + 1) else 2 * width + 1))
      (finProdFinEquiv (row, column))) (by cases chooseRight <;> rfl) (by intros; trivial)
  let rawEntry : Computation Parameter Unit := {
    inputDomains := fun _ => left.prod right
    outputDomain := binaryIntegers (if chooseRight then 2 * (2 * width + 1) else 2 * width + 1)
    precondition := fun _ _ => True
    compute := fun _ arguments => match chooseRight with
      | false => (arguments.val ()).1 (finProdFinEquiv (row, column))
      | true => (arguments.val ()).2 (finProdFinEquiv (row, column)) }
  have projected : rawEntry.Realizable := by
    cases chooseRight <;> exact selected
  have interpreted := projected.reinterpretInputs computation.inputDomains
    (fun _ sizes value => ((boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * width + 1))).prodCongr
      (boundedMatrixRecordEquiv (2 ^ MvPolynomial.eval sizes (2 * (2 * width + 1))))) value)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  apply interpreted.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  cases chooseRight <;> fin_cases row <;> fin_cases column <;> rfl

end Polytime2.Computation
