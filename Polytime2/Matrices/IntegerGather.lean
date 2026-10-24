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
import Polytime2.Matrices.Tabulate

/-! # Gathering integer matrices through ordinary finite maps

Read source entries at a row map and a column map. Target dimensions describe
the mathematical result; repeated selections are allowed. The source entry
bound is preserved, and realization reuses array lookup and matrix tabulation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns targetRows targetColumns width : MvPolynomial Parameter ℕ) : Fin 3 → EncodedDomain Parameter
  | 0 => integerMatrices rows columns width
  | 1 => (boundedIndex rows).arrayOfLength targetRows
  | 2 => (boundedIndex columns).arrayOfLength targetColumns

/-- Gather a rectangular submatrix through supplied row and column maps. -/
noncomputable def integerMatrixGather (rows columns targetRows targetColumns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) where
  inputDomains := inputs rows columns targetRows targetColumns width
  outputDomain := integerMatrices targetRows targetColumns width
  precondition _ _ := True
  compute _ arguments := ⟨(arguments.val 0).val.submatrix (arguments.val 1) (arguments.val 2),
    fun _row _column => (arguments.val 0).property _ _⟩

/-- Two map lookups and an existing entry read supply each tabulated output entry. -/
theorem integerMatrixGather_realizable (rows columns targetRows targetColumns width : MvPolynomial Parameter ℕ) :
    (integerMatrixGather rows columns targetRows targetColumns width).Realizable := by
  let computation := integerMatrixGather rows columns targetRows targetColumns width
  let scalar := binaryIntegers width
  let operation sizes (arguments : computation.Arguments sizes)
      (row : Fin (MvPolynomial.eval sizes targetRows)) (column : Fin (MvPolynomial.eval sizes targetColumns)) : scalar.Carrier sizes :=
    ⟨(arguments 0).val (arguments 1 row) (arguments 2 column), (arguments 0).property _ _⟩
  let step := matrixTabulateStep computation.inputDomains scalar targetRows targetColumns operation
  have row := (arrayLookupWithIndex_realizable (boundedIndex rows) (arrayPosition targetRows) (fun _ index => index.val)
    (arrayPosition_value targetRows) targetRows).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with | false => arguments.val (.inr false) | true => arguments.val (.inl 1))
    (by intro sizes arguments; exact (arguments.val (.inr false)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr false) step.precondition
      · exact Realizable.argument step.inputDomains (.inl 1) step.precondition)
  have column := (arrayLookupWithIndex_realizable (boundedIndex columns) (arrayPosition targetColumns) (fun _ index => index.val)
    (arrayPosition_value targetColumns) targetColumns).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with | false => arguments.val (.inr true) | true => arguments.val (.inl 2))
    (by intro sizes arguments; exact (arguments.val (.inr true)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr true) step.precondition
      · exact Realizable.argument step.inputDomains (.inl 2) step.precondition)
  have entry : step.Realizable := (integerMatrixEntry_realizable rows columns width).onResults step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inl 1) (arguments.val (.inr false))
      | 1 => arguments.val (.inl 2) (arguments.val (.inr true))
      | 2 => arguments.val (.inl 0)) (by intros; trivial) (by
        intro name
        fin_cases name
        · exact row
        · exact column
        · exact Realizable.argument step.inputDomains (.inl 0) step.precondition)
  have tabulated := matrixTabulate_realizable computation.inputDomains scalar targetRows targetColumns operation entry
  have collected := tabulated.reindexOutput computation.outputDomain.Carrier
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
  exact collected.withSpecification computation.precondition computation.compute (by intros; trivial) (by intros; rfl)

/-- Gathering returns exactly the ordinary mathematical submatrix. -/
theorem integerMatrixGather_correct (rows columns targetRows targetColumns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerMatrixGather rows columns targetRows targetColumns width).Arguments sizes //
      (integerMatrixGather rows columns targetRows targetColumns width).precondition sizes arguments}) :
    ((integerMatrixGather rows columns targetRows targetColumns width).compute sizes arguments).val =
      (arguments.val 0).val.submatrix (arguments.val 1) (arguments.val 2) := rfl

end Polytime2.Computation
