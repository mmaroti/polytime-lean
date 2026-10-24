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

import Polytime2.Matrices.IntegerRowDiagonal
import Polytime2.Arrays.IntegerDivides

/-! # Feasibility for a rectangular Smith diagonal

Input an integer matrix and a target vector with independent entry widths.
Return whether the zero-extended diagonal divides the target pointwise. For
a Smith diagonal this is exactly existence of an integer solution. The test
needs no active-rank input and covers singular and empty matrices.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Test the complete diagonal feasibility criterion without exposing runtime rank. -/
noncomputable def integerDiagonalFeasible
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerArrayDivides rows matrixWidth targetWidth).onResults
    (fun choice => if choice then (binaryIntegers targetWidth).arrayOfLength rows
      else integerMatrices rows columns matrixWidth)
    (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (integerMatrixRowDiagonal rows columns matrixWidth).compute sizes
          ⟨fun _ => arguments.val false, trivial⟩
      | true => arguments.val true) (by intros; trivial)

/-- Diagonal reads and the total pointwise divisibility test are certified. -/
theorem integerDiagonalFeasible_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalFeasible rows columns matrixWidth targetWidth).Realizable := by
  apply (integerArrayDivides_realizable rows matrixWidth targetWidth).onResults _ _ _ (by intros; trivial)
  intro choice
  cases choice
  · exact (integerMatrixRowDiagonal_realizable rows columns matrixWidth).withArguments _
      (MultiTape.oneTape false) (by intros; rfl)
  · exact Realizable.argument _ true _

/-- On a Smith diagonal the returned Boolean decides existence of an integer solution. -/
theorem integerDiagonalFeasible_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerDiagonalFeasible rows columns matrixWidth targetWidth).Arguments sizes)
    (rank : ℕ) (smith : IntegerMatrix.IsSmithDiagonal (arguments false).val rank) :
    (integerDiagonalFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  have tested := integerArrayDivides_correct rows matrixWidth targetWidth sizes
    (fun choice => match choice with
      | false => (integerMatrixRowDiagonal rows columns matrixWidth).compute sizes ⟨fun _ => arguments false, trivial⟩
      | true => arguments true)
  exact tested.trans ((IntegerMatrix.diagonalFeasible_iff_rowDiagonal (arguments false).val rank smith
    (fun row => (arguments true row).val)).symm.trans
      (IntegerMatrix.diagonalFeasible_iff (arguments false).val rank smith (fun row => (arguments true row).val)))

end Polytime2.Computation
