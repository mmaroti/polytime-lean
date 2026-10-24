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

import Polytime2.Matrices.IntegerOperationsMath
import Polytime2.Encoding.IntegerMatrices
import Polytime2.Matrices.Map
import Polytime2.Matrices.Transpose
import Polytime2.Arrays.ZipWith
import Polytime2.Arrays.Operations
import Polytime2.Arithmetic.SignedMultiplyAdd

/-! # Certified row and column addition on bounded integer matrices

The input consists of target and source row indices, a bounded integer
coefficient, and an ordinary rectangular integer matrix. Every input is
admissible; the result adds the coefficient times the source row to the target
and derives magnitude width `2*w+1` internally. Distinct rows give a unimodular
transformation by the independent mathematical theorem.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Read a bounded matrix row through any canonically encoded numeric index. -/
noncomputable def integerMatrixRowWithIndex (rows columns width : MvPolynomial Parameter ℕ)
    (indexDomain : EncodedDomain Parameter) (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ) :
    Computation Parameter Bool where
  inputDomains | false => indexDomain | true => integerMatrices rows columns width
  outputDomain := (binaryIntegers width).arrayOfLength columns
  precondition sizes arguments := toNat sizes (arguments false) < MvPolynomial.eval sizes rows
  compute sizes arguments := fun column =>
    ⟨(arguments.val true).val ⟨toNat sizes (arguments.val false), arguments.property⟩ column,
      (arguments.val true).property _ column⟩

theorem integerMatrixRowWithIndex_realizable (rows columns width : MvPolynomial Parameter ℕ)
    (indexDomain : EncodedDomain Parameter) (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (numeric : ∀ sizes index, Binary.value (ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index) :
    (integerMatrixRowWithIndex rows columns width indexDomain toNat).Realizable := by
  exact (arrayLookupWithIndex_realizable ((binaryIntegers width).arrayOfLength columns) indexDomain toNat numeric rows).reinterpretInputs
    (integerMatrixRowWithIndex rows columns width indexDomain toNat).inputDomains
    (fun name sizes => match name with
      | false => id
      | true => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (by intro name sizes; cases name; rfl; exact integerMatrices_nested_width rows columns width sizes)
    (by intro name sizes value; cases name; rfl; exact integerMatrices_nested_encode_bits rows columns width sizes value)
    (integerMatrixRowWithIndex rows columns width indexDomain toNat).precondition (by intros; assumption)

noncomputable def integerMatrixRow (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains | false => boundedIndex rows | true => integerMatrices rows columns width
  outputDomain := (binaryIntegers width).arrayOfLength columns
  precondition _ _ := True
  compute _sizes arguments := fun column =>
    ⟨(arguments.val true).val (arguments.val false) column,
      (arguments.val true).property (arguments.val false) column⟩

theorem integerMatrixRow_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerMatrixRow rows columns width).Realizable := by
  exact (integerMatrixRowWithIndex_realizable rows columns width (boundedIndex rows)
    (fun _ index => index.val) (boundedIndex_value rows)).withSpecification (fun _ _ => True)
    (integerMatrixRow rows columns width).compute (by intro sizes arguments valid; exact (arguments false).isLt)
    (by intros; rfl)

/-- Read one entry of a bounded ordinary integer matrix using separate coordinates. -/
noncomputable def integerMatrixEntry (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains | 0 => boundedIndex rows | 1 => boundedIndex columns | 2 => integerMatrices rows columns width
  outputDomain := binaryIntegers width
  precondition _ _ := True
  compute _ arguments := ⟨(arguments.val 2).val (arguments.val 0) (arguments.val 1), (arguments.val 2).property _ _⟩

theorem integerMatrixEntry_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerMatrixEntry rows columns width).Realizable := by
  let computation := integerMatrixEntry rows columns width
  have row := (integerMatrixRow_realizable rows columns width).onArguments computation.inputDomains computation.precondition
    (fun choice => match choice with | false => 0 | true => 2) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  exact (arrayLookup_realizable (binaryIntegers width) columns).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => arguments.val 1
      | true => (integerMatrixRow rows columns width).compute sizes
          ⟨(fun rowName => match rowName with | false => arguments.val 0 | true => arguments.val 2), trivial⟩)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact row)

private noncomputable def integerRowCombine (columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) where
  inputDomains | 0 | 1 => (binaryIntegers width).arrayOfLength columns | 2 => binaryIntegers width
  outputDomain := (binaryIntegers (2 * width + 1)).arrayOfLength columns
  precondition _ _ := True
  compute sizes arguments := fun column =>
    ⟨(arguments.val 0 column).val + (arguments.val 2).val * (arguments.val 1 column).val, by
      simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
        IntegerArithmetic.multiplyAdd_bound (MvPolynomial.eval sizes width) _ _ _
          (arguments.val 0 column).property (arguments.val 2).property (arguments.val 1 column).property⟩

private theorem integerRowCombine_realizable (columns width : MvPolynomial Parameter ℕ) :
    (integerRowCombine columns width).Realizable := by
  let computation := integerRowCombine columns width
  let context := fun _ : Unit => binaryIntegers width
  let operation sizes (coefficients : ∀ name, (context name).Carrier sizes)
      (first second : (binaryIntegers width).Carrier sizes) :=
    (integerMultiplyAdd width).compute sizes ⟨![first, coefficients (), second], trivial⟩
  let step := arrayZipWithStep context (binaryIntegers width) (binaryIntegers width)
    (binaryIntegers (2 * width + 1)) operation
  have scalar : step.Realizable := (integerMultiplyAdd_realizable width).onArguments step.inputDomains (fun _ _ => True)
    (fun name => match name with
      | 0 => (.inr false)
      | 1 => (.inl ())
      | 2 => (.inr true)) (by intro name; fin_cases name <;> rfl) (by intros; trivial)
  exact (arrayZipWith_realizable context (binaryIntegers width) (binaryIntegers width)
    (binaryIntegers (2 * width + 1)) columns operation scalar).onArguments computation.inputDomains (fun _ _ => True)
      (fun name => match name with
      | .inl () => 2
      | .inr false => 0
      | .inr true => 1) (by
        intro name
        cases name with
        | inl singleton => cases singleton; rfl
        | inr choice =>
          cases choice
          · rfl
          · rfl) (by intros; trivial)


/-- Widen matrix entries before reusing whole-row array operations. -/
noncomputable def integerMatrixWidenForRows (rows columns width extra capacity : MvPolynomial Parameter ℕ)
    (widthEqual : capacity = width + extra) : Computation Parameter Unit where
  inputDomains _ := integerMatrices rows columns width
  outputDomain := ((binaryIntegers capacity).arrayOfLength columns).arrayOfLength rows
  precondition _ _ := True
  compute sizes arguments row column := ⟨(arguments.val ()).val row column, by
    rw [widthEqual]
    exact ((arguments.val ()).property row column).trans_le (pow_le_pow_right₀ (by decide)
      (by simp only [map_add]; omega))⟩

theorem integerMatrixWidenForRows_realizable (rows columns width extra capacity : MvPolynomial Parameter ℕ)
    (widthEqual : capacity = width + extra) :
    (integerMatrixWidenForRows rows columns width extra capacity widthEqual).Realizable := by
  have wider := integerWidenTo_realizable width extra capacity widthEqual
  let widen sizes (value : (binaryIntegers width).Carrier sizes) :=
    (⟨value.val, by
      rw [widthEqual]
      exact value.property.trans_le (pow_le_pow_right₀ (by decide)
        (by simp only [map_add]; omega))⟩ : (binaryIntegers capacity).Carrier sizes)
  have scalar : (unaryMap (binaryIntegers width) (binaryIntegers capacity) (fun _ _ => True)
      (fun sizes value => widen sizes value.val)).Realizable := wider
  have mapped := matrixMap_realizable (binaryIntegers width) (binaryIntegers capacity)
    rows columns widen scalar
  have bounded := mapped.reinterpretInputs (fun _ : Unit => integerMatrices rows columns width)
    (fun _ sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  have nested := bounded.reinterpretOutput
    (((binaryIntegers capacity).arrayOfLength columns).arrayOfLength rows) (fun _ value => value)
    (fun sizes => (integerMatrices_nested_width rows columns capacity sizes).symm)
    (fun sizes value => (matrix_nested_encode_bits (binaryIntegers capacity) rows columns sizes value).symm)
  exact nested

/-- Reassemble the widened entries as an ordinary bounded integer matrix. -/
noncomputable def integerMatrixWiden (rows columns width extra capacity : MvPolynomial Parameter ℕ)
    (widthEqual : capacity = width + extra) : Computation Parameter Unit :=
  (integerMatrixWidenForRows rows columns width extra capacity widthEqual).reinterpretOutput
    (integerMatrices rows columns capacity)
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes capacity)).symm value)

theorem integerMatrixWiden_realizable (rows columns width extra capacity : MvPolynomial Parameter ℕ)
    (widthEqual : capacity = width + extra) :
    (integerMatrixWiden rows columns width extra capacity widthEqual).Realizable :=
  (integerMatrixWidenForRows_realizable rows columns width extra capacity widthEqual).reinterpretOutput
    (integerMatrices rows columns capacity)
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes capacity)).symm value)
    (fun sizes => integerMatrices_nested_width rows columns capacity sizes)
    (fun sizes value => integerMatrices_of_nested_encode_bits rows columns capacity sizes value)

end Polytime2.Computation.Realizable.Internal

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Add a bounded integer multiple of a row, deriving sufficient output width. -/
noncomputable def integerRowAdd (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex rows | 2 => binaryIntegers width
      | 3 => integerMatrices rows columns width
    outputDomain := integerMatrices rows columns (2 * width + 1)
    precondition := fun _ _ => True
    compute := fun sizes arguments => ⟨IntegerMatrix.rowAdd (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val, by
        simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
          IntegerMatrix.rowAdd_bound (Row := Fin (MvPolynomial.eval sizes rows))
            (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
            (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
            (arguments.val 2).property (arguments.val 3).property⟩ }

/-- Row addition is realized by row lookup, scalar composition, and row update. -/
theorem integerRowAdd_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowAdd rows columns width).Realizable := by
  classical
  let computation := integerRowAdd rows columns width
  let inputs := computation.inputDomains
  let capacity := 2 * width + 1
  have widthEqual : capacity = width + (width + 1) := by dsimp [capacity]; ring
  let widen sizes (value : (binaryIntegers width).Carrier sizes) :=
    (⟨value.val, by
      rw [widthEqual]
      exact value.property.trans_le (pow_le_pow_right₀ (by decide)
        (by simp only [map_add]; omega))⟩ : (binaryIntegers capacity).Carrier sizes)
  have original := (Realizable.Internal.integerMatrixWidenForRows_realizable
    rows columns width (width + 1) capacity widthEqual).withArguments inputs (MultiTape.oneTape 3) (fun _ => rfl)
  have selected (name : Fin 2) := (Realizable.Internal.integerMatrixRow_realizable rows columns width).onArguments
    inputs (fun _ _ => True)
    (fun choice => match choice with | false => if name = 0 then 0 else 1 | true => 3)
    (by intro choice; cases choice <;> fin_cases name <;> rfl) (by intros; trivial)
  have combined := (Realizable.Internal.integerRowCombine_realizable columns width).onResults
    inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => (Realizable.Internal.integerMatrixRow rows columns width).compute sizes
          ⟨(fun choice => match choice with | false => arguments.val 0 | true => arguments.val 3), trivial⟩
      | 1 => (Realizable.Internal.integerMatrixRow rows columns width).compute sizes
          ⟨(fun choice => match choice with | false => arguments.val 1 | true => arguments.val 3), trivial⟩
      | 2 => arguments.val 2) (by intros; trivial) (by
        intro name
        fin_cases name
        · exact selected 0
        · exact selected 1
        · exact Realizable.argument inputs 2 (fun _ _ => True))
  have updated := (arrayUpdate_realizable ((binaryIntegers capacity).arrayOfLength columns) rows).onResults
    inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => (fun row column => widen sizes ⟨(arguments.val 3).val row column, (arguments.val 3).property row column⟩)
      | 2 => (Realizable.Internal.integerRowCombine columns width).compute sizes
          ⟨(fun name => match name with
            | 0 => fun column => ⟨(arguments.val 3).val (arguments.val 0) column, (arguments.val 3).property (arguments.val 0) column⟩
            | 1 => fun column => ⟨(arguments.val 3).val (arguments.val 1) column, (arguments.val 3).property (arguments.val 1) column⟩
            | 2 => arguments.val 2), trivial⟩)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs 0 (fun _ _ => True)
      · exact original
      · exact combined)
  have result := updated.reinterpretOutput computation.outputDomain
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes capacity)).symm value)
    (fun sizes => integerMatrices_nested_width rows columns capacity sizes)
    (fun sizes value => integerMatrices_of_nested_encode_bits rows columns capacity sizes value)
  apply result.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Subtype.ext
  funext row column
  dsimp only [Computation.reinterpretOutput, Computation.onResults, arrayUpdate]
  erw [IntegerMatrix.entryBoundEquiv_symm_apply]
  by_cases same : row = arguments 0
  · subst row
    simp only [widen, computation,
      integerRowAdd, Realizable.Internal.integerRowCombine, IntegerMatrix.rowAdd]
    erw [Function.update_self, Matrix.updateRow_self]
  · simp only [widen, computation,
      integerRowAdd, Realizable.Internal.integerRowCombine, IntegerMatrix.rowAdd]
    erw [Function.update_of_ne same, Matrix.updateRow_ne same]

/-- Transpose a bounded ordinary integer matrix, preserving its magnitude bound. -/
noncomputable def integerMatrixTranspose (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := integerMatrices rows columns width
  outputDomain := integerMatrices columns rows width
  precondition _ _ := True
  compute _ arguments := ⟨(arguments.val ()).val.transpose,
    fun row column => (arguments.val ()).property column row⟩

theorem integerMatrixTranspose_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerMatrixTranspose rows columns width).Realizable := by
  have transposed := (matrixTranspose_realizable (binaryIntegers width) rows columns).reinterpretInputs
    (integerMatrixTranspose rows columns width).inputDomains
    (fun _ sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  have result := transposed.reinterpretOutput (integerMatrices columns rows width)
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)
    (by intros; rfl) (by
      intro sizes value
      change ArrayEncoding.bits ((matrix (binaryIntegers width) columns rows).encode sizes
        ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
          ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value))) = _
      exact congrArg (fun value => ArrayEncoding.bits
        ((matrix (binaryIntegers width) columns rows).encode sizes value))
        ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).apply_symm_apply value))
  exact result

/-- Add a bounded integer multiple of a column, deriving sufficient width. -/
noncomputable def integerColumnAdd (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 | 1 => boundedIndex columns | 2 => binaryIntegers width
      | 3 => integerMatrices rows columns width
    outputDomain := integerMatrices rows columns (2 * width + 1)
    precondition := fun _ _ => True
    compute := fun sizes arguments => ⟨IntegerMatrix.columnAdd (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val, by
        simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
          IntegerMatrix.columnAdd_bound (Row := Fin (MvPolynomial.eval sizes rows))
            (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
            (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
            (arguments.val 2).property (arguments.val 3).property⟩ }

theorem integerColumnAdd_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnAdd rows columns width).Realizable := by
  let computation := integerColumnAdd rows columns width
  let inputs := computation.inputDomains
  have transposed := (integerMatrixTranspose_realizable rows columns width).withArguments
    inputs (MultiTape.oneTape 3) (fun _ => rfl)
  have added := (integerRowAdd_realizable columns rows width).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => (integerMatrixTranspose rows columns width).compute sizes
          ⟨(fun _ => arguments.val 3), trivial⟩)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs 0 (fun _ _ => True)
      · exact Realizable.argument inputs 1 (fun _ _ => True)
      · exact Realizable.argument inputs 2 (fun _ _ => True)
      · exact transposed)
  have result := added.followedBy (integerMatrixTranspose_realizable columns rows (2 * width + 1))
    rfl (by intros; trivial)
  exact result.withSpecification (fun _ _ => True) computation.compute
    (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
