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

import Polytime2.Matrices.IntegerDotProduct
import Polytime2.Matrices.IntegerOperations
import Polytime2.Arrays.Tabulate

/-! # Integer matrix-vector multiplication

Input an ordinary rectangular integer matrix and a vector, with independent
entry widths. Return the mathematical matrix-vector product at the derived
width given by the column count plus both input widths. The implementation
reuses row reads, certified dot products, and tabulation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Multiply a bounded rectangular matrix by a bounded integer vector. -/
noncomputable def integerMatrixMulVec
    (rows columns matrixWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then (binaryIntegers valueWidth).arrayOfLength columns
    else integerMatrices rows columns matrixWidth
  outputDomain := (binaryIntegers (columns + matrixWidth + valueWidth)).arrayOfLength rows
  precondition _ _ := True
  compute sizes arguments row := ⟨(arguments.val false).val.mulVec (fun column => (arguments.val true column).val) row, by
    simpa only [map_add, Matrix.mulVec, dotProduct] using
      IntegerMatrix.partial_dotProduct_bound (MvPolynomial.eval sizes matrixWidth) (MvPolynomial.eval sizes valueWidth)
        (fun column => (arguments.val false).val row column) (fun column => (arguments.val true column).val)
        Finset.univ (fun column => (arguments.val false).property row column) (fun column => (arguments.val true column).property)⟩

/-- The complete product reuses scalar dot products at the same derived width. -/
theorem integerMatrixMulVec_realizable
    (rows columns matrixWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixMulVec rows columns matrixWidth valueWidth).Realizable := by
  let computation := integerMatrixMulVec rows columns matrixWidth valueWidth
  let scalar := binaryIntegers (columns + matrixWidth + valueWidth)
  let operation sizes (arguments : computation.Arguments sizes) row :=
    computation.compute sizes ⟨arguments, trivial⟩ row
  let step := arrayTransformStep computation.inputDomains (arrayPosition rows) scalar operation
  have row := (integerMatrixRowWithIndex_realizable rows columns matrixWidth (arrayPosition rows)
    (fun _ index => index.val) (arrayPosition_value rows)).onArguments step.inputDomains step.precondition
      (fun choice => match choice with
      | false => (.inr ()) | true => (.inl false)) (by intro choice; cases choice <;> rfl) (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  let arrays choice sizes (arguments : {arguments : step.Arguments sizes // step.precondition sizes arguments}) :
      ((integerDotProduct columns matrixWidth valueWidth).inputDomains choice).Carrier sizes :=
    match choice with
    | false => fun column => ⟨(arguments.val (.inl false)).val (arguments.val (.inr ())) column,
        (arguments.val (.inl false)).property _ _⟩
    | true => arguments.val (.inl true)
  have dotted := (integerDotProduct_realizable columns matrixWidth valueWidth).onResults
    step.inputDomains step.precondition arrays (by intros; trivial) (by
      intro choice
      cases choice
      · exact row
      · exact Realizable.argument step.inputDomains (.inl true) step.precondition)
  have ready : step.Realizable := by
    apply dotted.withSpecification step.precondition step.compute (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    exact integerDotProduct_correct columns matrixWidth valueWidth sizes
      ⟨fun choice => arrays choice sizes ⟨arguments, valid⟩, trivial⟩
  exact arrayTabulate_realizable computation.inputDomains scalar rows operation ready

end Polytime2.Computation
