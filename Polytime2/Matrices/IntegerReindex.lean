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

import Polytime2.Matrices.IntegerGather
import Polytime2.Matrices.PermutationTrackingMath
import Polytime2.Arrays.BoundedPositions

/-! # Gathering a matrix with both transformation bases

Given row and column maps and a bounded presentation, gather both axes of the
matrix, rows of the left basis, and columns of the right basis. Each bound is
preserved independently. For permutation maps this preserves the presentation
and unimodularity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def reindexInputs
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Fin 5 → EncodedDomain Parameter
  | 0 => (boundedIndex rows).arrayOfLength rows
  | 1 => (boundedIndex columns).arrayOfLength columns
  | 2 => integerMatrices rows columns matrixWidth
  | 3 => integerMatrices rows rows leftWidth
  | 4 => integerMatrices columns columns rightWidth

/-- Apply finite maps to a matrix and the corresponding axes of its bases. -/
noncomputable def integerReindexWithBases
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) where
  inputDomains := reindexInputs rows columns matrixWidth leftWidth rightWidth
  outputDomain := (integerMatrices rows columns matrixWidth).prod
    ((integerMatrices rows rows leftWidth).prod
      (integerMatrices columns columns rightWidth))
  precondition _ _ := True
  compute _ arguments :=
    (⟨(arguments.val 2).val.submatrix (arguments.val 0) (arguments.val 1),
      fun _ _ => (arguments.val 2).property _ _⟩,
    ⟨(arguments.val 3).val.submatrix (arguments.val 0) id,
      fun _ _ => (arguments.val 3).property _ _⟩,
    ⟨(arguments.val 4).val.submatrix id (arguments.val 1),
      fun _ _ => (arguments.val 4).property _ _⟩)

/-- Gather all three matrices by composition, retaining their separate widths. -/
theorem integerReindexWithBases_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).Realizable := by
  let computation := integerReindexWithBases rows columns matrixWidth leftWidth rightWidth
  have matrix := (integerMatrixGather_realizable rows columns rows columns matrixWidth).onResults
    computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 2 | 1 => arguments.val 0 | 2 => arguments.val 1)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have left := (integerMatrixGather_realizable rows rows rows rows leftWidth).onResults
    computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 3 | 1 => arguments.val 0 | 2 => id)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 3 computation.precondition
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact (arrayBoundedPositions_realizable rows).onResults _ _
          (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name))
  have right := (integerMatrixGather_realizable columns columns columns columns rightWidth).onResults
    computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 4 | 1 => id | 2 => arguments.val 1)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 4 computation.precondition
      · exact (arrayBoundedPositions_realizable columns).onResults _ _
          (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have bases := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ left right
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ matrix bases

/-- Permutation maps preserve the presentation and both unit determinants. -/
theorem integerReindexWithBases_preserves
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments :
      (integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).Arguments sizes //
      (integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).precondition sizes arguments})
    (rowPermutation : Equiv.Perm (Fin (MvPolynomial.eval sizes rows)))
    (columnPermutation : Equiv.Perm (Fin (MvPolynomial.eval sizes columns)))
    (rowMap : arguments.val 0 = (fun index => rowPermutation index))
    (columnMap : arguments.val 1 = (fun index => columnPermutation index))
    (original : Matrix (Fin (MvPolynomial.eval sizes rows))
      (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 3).val * original * (arguments.val 4).val =
      (arguments.val 2).val)
    (leftUnit : IsUnit (arguments.val 3).val.det)
    (rightUnit : IsUnit (arguments.val 4).val.det) :
    let result := (integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).compute sizes arguments
    result.2.1.val * original * result.2.2.val = result.1.val ∧
      IsUnit result.2.1.val.det ∧ IsUnit result.2.2.val.det := by
  dsimp only [integerReindexWithBases]
  rw [rowMap, columnMap]
  exact IntegerMatrix.permuteWithBases_preserves rowPermutation columnPermutation
    (arguments.val 2).val original (arguments.val 3).val (arguments.val 4).val
    equation leftUnit rightUnit

end Polytime2.Computation
