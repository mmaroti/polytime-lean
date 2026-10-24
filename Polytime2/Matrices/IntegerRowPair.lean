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

import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.RowPairMath
import Polytime2.Arithmetic.SignedTwoProducts

/-! # Certified simultaneous integer row and column transformations

The inputs are two row indices, four integer coefficients, and an ordinary
rectangular integer matrix. Coefficient and matrix widths may differ; both new
rows read the original rows. Distinct row indices are required. The sufficient
output width is the sum of the two input widths plus one. The original
common-width interface specializes this rule without changing its codec.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def integerRowsLinear (columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) where
  inputDomains | 0 | 1 => (binaryIntegers matrixWidth).arrayOfLength columns
               | 2 | 3 => binaryIntegers coefficientWidth
  outputDomain := (binaryIntegers (coefficientWidth + matrixWidth + 1)).arrayOfLength columns
  precondition _ _ := True
  compute sizes arguments column := ⟨(arguments.val 2).val * (arguments.val 0 column).val +
    (arguments.val 3).val * (arguments.val 1 column).val, by
      simpa only [map_add, map_one] using
        IntegerArithmetic.twoProducts_bound_of_widths (MvPolynomial.eval sizes coefficientWidth)
          (MvPolynomial.eval sizes matrixWidth) _ _ _ _
          (arguments.val 2).property (arguments.val 0 column).property
          (arguments.val 3).property (arguments.val 1 column).property⟩

private theorem integerRowsLinear_realizable (columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerRowsLinear columns coefficientWidth matrixWidth).Realizable := by
  let computation := integerRowsLinear columns coefficientWidth matrixWidth
  let context := fun _ : Bool => binaryIntegers coefficientWidth
  let operation sizes (coefficients : ∀ name, (context name).Carrier sizes)
      (first second : (binaryIntegers matrixWidth).Carrier sizes) :=
    (integerTwoProductsAtWidths coefficientWidth matrixWidth).compute sizes ⟨(fun name => match name with
      | 0 => coefficients false | 1 => first | 2 => coefficients true | 3 => second), trivial⟩
  let step := arrayZipWithStep context (binaryIntegers matrixWidth) (binaryIntegers matrixWidth)
    (binaryIntegers (coefficientWidth + matrixWidth + 1)) operation
  have scalar : step.Realizable := (integerTwoProductsAtWidths_realizable coefficientWidth matrixWidth).onResults
    step.inputDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inl false)
      | 1 => arguments.val (.inr false)
      | 2 => arguments.val (.inl true)
      | 3 => arguments.val (.inr true)) (by intros; trivial) (by
        intro name
        fin_cases name
        · exact Realizable.argument step.inputDomains (.inl false) (fun _ _ => True)
        · exact Realizable.argument step.inputDomains (.inr false) (fun _ _ => True)
        · exact Realizable.argument step.inputDomains (.inl true) (fun _ _ => True)
        · exact Realizable.argument step.inputDomains (.inr true) (fun _ _ => True))
  exact (arrayZipWith_realizable context (binaryIntegers matrixWidth) (binaryIntegers matrixWidth)
    (binaryIntegers (coefficientWidth + matrixWidth + 1)) columns operation scalar).onResults computation.inputDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | .inl false => arguments.val 2
      | .inl true => arguments.val 3
      | .inr false => arguments.val 0
      | .inr true => arguments.val 1) (by intros; trivial) (by
        intro name
        cases name with
        | inl choice =>
          cases choice
          · exact Realizable.argument computation.inputDomains 2 (fun _ _ => True)
          · exact Realizable.argument computation.inputDomains 3 (fun _ _ => True)
        | inr choice =>
          cases choice
          · exact Realizable.argument computation.inputDomains 0 (fun _ _ => True)
          · exact Realizable.argument computation.inputDomains 1 (fun _ _ => True))


end Polytime2.Computation.Realizable.Internal

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Simultaneously apply four integer coefficients to two original rows. -/
noncomputable def integerRowPairAtWidths (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 7) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex rows
      | 2 | 3 | 4 | 5 => binaryIntegers coefficientWidth
      | 6 => integerMatrices rows columns matrixWidth
    outputDomain := integerMatrices rows columns (coefficientWidth + matrixWidth + 1)
    precondition := fun _ arguments => arguments 0 ≠ arguments 1
    compute := fun sizes arguments => ⟨IntegerMatrix.rowPair (arguments.val 0) (arguments.val 1)
      !![(arguments.val 2).val, (arguments.val 3).val; (arguments.val 4).val, (arguments.val 5).val]
      (arguments.val 6).val, by
        simp only [map_add, map_one]
        apply IntegerMatrix.rowPair_bound_of_widths (Row := Fin (MvPolynomial.eval sizes rows))
          (MvPolynomial.eval sizes coefficientWidth) (MvPolynomial.eval sizes matrixWidth) (arguments.val 0) (arguments.val 1) _ (arguments.val 6).val
        · intro row column
          fin_cases row <;> fin_cases column
          · exact (arguments.val 2).property
          · exact (arguments.val 3).property
          · exact (arguments.val 4).property
          · exact (arguments.val 5).property
        · exact (arguments.val 6).property⟩ }

theorem integerRowPairAtWidths_realizable (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerRowPairAtWidths rows columns coefficientWidth matrixWidth).Realizable := by
  classical
  let computation := integerRowPairAtWidths rows columns coefficientWidth matrixWidth
  let inputs := computation.inputDomains
  let capacity := coefficientWidth + matrixWidth + 1
  have widthEqual : capacity = matrixWidth + (coefficientWidth + 1) := by dsimp [capacity]; ring
  have original := (Realizable.Internal.integerMatrixWidenForRows_realizable
    rows columns matrixWidth (coefficientWidth + 1) capacity widthEqual).withArguments inputs (MultiTape.oneTape 6) (fun _ => rfl)
  let selected (choice : Bool) sizes (arguments : {arguments : computation.Arguments sizes // True}) :=
    (Realizable.Internal.integerMatrixRow rows columns matrixWidth).compute sizes
      ⟨(fun name => match name with
        | false => if choice then arguments.val 1 else arguments.val 0
        | true => arguments.val 6), trivial⟩
  have selectedReady (choice : Bool) : (Computation.mk inputs
      ((binaryIntegers matrixWidth).arrayOfLength columns) (fun _ _ => True) (selected choice)).Realizable :=
    (Realizable.Internal.integerMatrixRow_realizable rows columns matrixWidth).onResults inputs (fun _ _ => True)
      (fun name _ arguments => match name with
        | false => if choice then arguments.val 1 else arguments.val 0
        | true => arguments.val 6) (by intros; trivial) (by
          intro name
          cases name
          · cases choice
            · exact Realizable.argument inputs 0 (fun _ _ => True)
            · exact Realizable.argument inputs 1 (fun _ _ => True)
          · exact Realizable.argument inputs 6 (fun _ _ => True))
  let combined (choice : Bool) sizes (arguments : {arguments : computation.Arguments sizes // True}) :=
    (Realizable.Internal.integerRowsLinear columns coefficientWidth matrixWidth).compute sizes
      ⟨(fun name => match name with
        | 0 => selected false sizes arguments
        | 1 => selected true sizes arguments
        | 2 => if choice then arguments.val 4 else arguments.val 2
        | 3 => if choice then arguments.val 5 else arguments.val 3), trivial⟩
  have combinedReady (choice : Bool) : (Computation.mk inputs
      ((binaryIntegers capacity).arrayOfLength columns) (fun _ _ => True) (combined choice)).Realizable :=
    (Realizable.Internal.integerRowsLinear_realizable columns coefficientWidth matrixWidth).onResults inputs (fun _ _ => True)
      (fun name sizes arguments => match name with
        | 0 => selected false sizes arguments
        | 1 => selected true sizes arguments
        | 2 => if choice then arguments.val 4 else arguments.val 2
        | 3 => if choice then arguments.val 5 else arguments.val 3) (by intros; trivial) (by
          intro name
          fin_cases name
          · exact selectedReady false
          · exact selectedReady true
          · cases choice
            · exact Realizable.argument inputs 2 (fun _ _ => True)
            · exact Realizable.argument inputs 4 (fun _ _ => True)
          · cases choice
            · exact Realizable.argument inputs 3 (fun _ _ => True)
            · exact Realizable.argument inputs 5 (fun _ _ => True))
  let widened sizes (arguments : {arguments : computation.Arguments sizes // True}) :=
    (Realizable.Internal.integerMatrixWidenForRows rows columns matrixWidth (coefficientWidth + 1) capacity widthEqual).compute sizes
      ⟨(fun _ => arguments.val 6), trivial⟩
  let firstUpdate sizes (arguments : {arguments : computation.Arguments sizes // True}) :=
    Function.update (widened sizes arguments) (arguments.val 0) (combined false sizes arguments)
  have firstReady := (arrayUpdate_realizable ((binaryIntegers capacity).arrayOfLength columns) rows).onResults
    inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => widened sizes arguments
      | 2 => combined false sizes arguments) (by intros; trivial) (by
        intro name
        fin_cases name
        · exact Realizable.argument inputs 0 (fun _ _ => True)
        · exact original
        · exact combinedReady false)
  have updated := (arrayUpdate_realizable ((binaryIntegers capacity).arrayOfLength columns) rows).onResults
    inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 1
      | 1 => firstUpdate sizes arguments
      | 2 => combined true sizes arguments) (by intros; trivial) (by
        intro name
        fin_cases name
        · exact Realizable.argument inputs 1 (fun _ _ => True)
        · exact firstReady
        · exact combinedReady true)
  have result := updated.reinterpretOutput computation.outputDomain
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes capacity)).symm value)
    (fun sizes => integerMatrices_nested_width rows columns capacity sizes)
    (fun sizes value => integerMatrices_of_nested_encode_bits rows columns capacity sizes value)
  apply result.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Subtype.ext
  funext row column
  dsimp only [Computation.reinterpretOutput, Computation.onResults, arrayUpdate]
  erw [IntegerMatrix.entryBoundEquiv_symm_apply]
  dsimp only [firstUpdate]
  by_cases atSecond : row = arguments 1
  · subst row
    erw [Function.update_self]
    simp only [combined, selected, Realizable.Internal.integerRowsLinear,
      Realizable.Internal.integerMatrixRow, computation, integerRowPairAtWidths, IntegerMatrix.rowPair]
    erw [Matrix.updateRow_self]
    simp
  · erw [Function.update_of_ne atSecond]
    by_cases atFirst : row = arguments 0
    · subst row
      erw [Function.update_self]
      simp only [combined, selected, Realizable.Internal.integerRowsLinear,
        Realizable.Internal.integerMatrixRow, computation, integerRowPairAtWidths, IntegerMatrix.rowPair]
      erw [Matrix.updateRow_ne atSecond, Matrix.updateRow_self]
      simp
    · erw [Function.update_of_ne atFirst]
      simp [computation, integerRowPairAtWidths, IntegerMatrix.rowPair,
        Matrix.updateRow_ne atSecond, Matrix.updateRow_ne atFirst]
      rfl

/-- The common-width specialization preserves the original interface and codec. -/
noncomputable def integerRowPair (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 7) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex rows
      | 2 | 3 | 4 | 5 => binaryIntegers width
      | 6 => integerMatrices rows columns width
    outputDomain := integerMatrices rows columns (2 * width + 1)
    precondition := fun _ arguments => arguments 0 ≠ arguments 1
    compute := fun sizes arguments => ⟨IntegerMatrix.rowPair (arguments.val 0) (arguments.val 1)
      !![(arguments.val 2).val, (arguments.val 3).val; (arguments.val 4).val, (arguments.val 5).val]
      (arguments.val 6).val, by
        simp only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat]
        apply IntegerMatrix.rowPair_bound (Row := Fin (MvPolynomial.eval sizes rows))
          (MvPolynomial.eval sizes width) (arguments.val 0) (arguments.val 1) _ (arguments.val 6).val
        · intro row column
          fin_cases row <;> fin_cases column
          · exact (arguments.val 2).property
          · exact (arguments.val 3).property
          · exact (arguments.val 4).property
          · exact (arguments.val 5).property
        · exact (arguments.val 6).property⟩ }

theorem integerRowPair_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowPair rows columns width).Realizable := by
  let computation := integerRowPair rows columns width
  have sameWidth : width + width + 1 = 2 * width + 1 := by ring
  have general := (integerRowPairAtWidths_realizable rows columns width width).withArguments
    computation.inputDomains (Function.Embedding.refl _) (by intro name; fin_cases name <;> rfl)
  have converted := general.reinterpretOutput computation.outputDomain
    (fun _ value => ⟨value.val, by simpa only [sameWidth] using value.property⟩)
    (fun sizes => congrArg (fun resultWidth => (integerMatrices rows columns resultWidth).width sizes) sameWidth.symm)
    (fun sizes value => integerMatrices_encode_congr rows columns _ _ sameWidth.symm sizes _ value rfl)
  exact converted.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; apply Subtype.ext; rfl)

/-- Apply a right transformation to two columns, with independent coefficient and matrix widths. -/
noncomputable def integerColumnPairAtWidths (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 7) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex columns
      | 2 | 3 | 4 | 5 => binaryIntegers coefficientWidth
      | 6 => integerMatrices rows columns matrixWidth
    outputDomain := integerMatrices rows columns (coefficientWidth + matrixWidth + 1)
    precondition := fun _ arguments => arguments 0 ≠ arguments 1
    compute := fun sizes arguments => ⟨IntegerMatrix.columnPair (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1)
      !![(arguments.val 2).val, (arguments.val 3).val; (arguments.val 4).val, (arguments.val 5).val]
      (arguments.val 6).val, by
        simp only [map_add, map_one]
        have bound := IntegerMatrix.rowPair_bound_of_widths (Row := Fin (MvPolynomial.eval sizes columns))
          (MvPolynomial.eval sizes coefficientWidth) (MvPolynomial.eval sizes matrixWidth) (arguments.val 0) (arguments.val 1)
          (!![(arguments.val 2).val, (arguments.val 3).val; (arguments.val 4).val, (arguments.val 5).val]).transpose
          (arguments.val 6).val.transpose (by
            intro row column
            fin_cases row <;> fin_cases column
            · exact (arguments.val 2).property
            · exact (arguments.val 4).property
            · exact (arguments.val 3).property
            · exact (arguments.val 5).property)
          (fun column row => (arguments.val 6).property row column)
        exact fun row column => bound column row⟩ }

theorem integerColumnPairAtWidths_realizable (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerColumnPairAtWidths rows columns coefficientWidth matrixWidth).Realizable := by
  let computation := integerColumnPairAtWidths rows columns coefficientWidth matrixWidth
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  have transposed := ((integerMatrixTranspose_realizable rows columns matrixWidth).withArguments inputs
    (MultiTape.oneTape 6) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  have transformed := (integerRowPairAtWidths_realizable columns rows coefficientWidth matrixWidth).onResults inputs allowed
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => arguments.val 4
      | 4 => arguments.val 3
      | 5 => arguments.val 5
      | 6 => (integerMatrixTranspose rows columns matrixWidth).compute sizes ⟨(fun _ => arguments.val 6), trivial⟩)
    (fun _ arguments => arguments.property) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs 0 allowed
      · exact Realizable.argument inputs 1 allowed
      · exact Realizable.argument inputs 2 allowed
      · exact Realizable.argument inputs 4 allowed
      · exact Realizable.argument inputs 3 allowed
      · exact Realizable.argument inputs 5 allowed
      · exact transposed)
  have result := transformed.followedBy
    (integerMatrixTranspose_realizable columns rows (coefficientWidth + matrixWidth + 1)) rfl (by intros; trivial)
  exact result.withSpecification allowed computation.compute (by intros; assumption) (by intros; rfl)

end Polytime2.Computation
