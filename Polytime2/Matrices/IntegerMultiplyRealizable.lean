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
import Polytime2.Matrices.Tabulate

/-! # Realizing rectangular integer matrix multiplication

Tabulate each output entry by reading a row and a column, then applying the
fixed-width dot-product fold. Existing transpose and lookup handle navigation;
the output bound includes the shared dimension and both independent widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Matrix multiplication composes row reads, transpose, dot products, and tabulation. -/
theorem integerMatrixMultiply_realizable
    (rows inner columns leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixMultiply rows inner columns leftWidth rightWidth).Realizable := by
  let computation := integerMatrixMultiply rows inner columns leftWidth rightWidth
  let scalar := binaryIntegers (inner + leftWidth + rightWidth)
  let operation sizes (arguments : computation.Arguments sizes)
      (row : Fin (MvPolynomial.eval sizes rows)) (column : Fin (MvPolynomial.eval sizes columns)) : scalar.Carrier sizes :=
    ⟨((arguments false).val * (arguments true).val) row column,
      (computation.compute sizes ⟨arguments, trivial⟩).property row column⟩
  let step := matrixTabulateStep computation.inputDomains scalar rows columns operation
  have row := (integerMatrixRowWithIndex_realizable rows inner leftWidth (arrayPosition rows)
    (fun _ index => index.val) (arrayPosition_value rows)).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr false) | true => arguments.val (.inl false))
    (by intro sizes arguments; exact (arguments.val (.inr false)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr false) step.precondition
      · exact Realizable.argument step.inputDomains (.inl false) step.precondition)
  have transposed := (integerMatrixTranspose_realizable inner columns rightWidth).withArguments
    step.inputDomains (MultiTape.oneTape (.inl true)) (by intros; rfl)
  have column := (integerMatrixRowWithIndex_realizable columns inner rightWidth (arrayPosition columns)
    (fun _ index => index.val) (arrayPosition_value columns)).onResults step.inputDomains step.precondition
    (fun choice sizes arguments => match choice with
      | false => arguments.val (.inr true)
      | true => (integerMatrixTranspose inner columns rightWidth).compute sizes
          ⟨fun _ => arguments.val (.inl true), trivial⟩)
    (by intro sizes arguments; exact (arguments.val (.inr true)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr true) step.precondition
      · exact transposed)
  let arrays choice sizes (arguments : {arguments : step.Arguments sizes // step.precondition sizes arguments}) :
      ((integerDotProduct inner leftWidth rightWidth).inputDomains choice).Carrier sizes :=
    match choice with
    | false => fun index => ⟨(arguments.val (.inl false)).val (arguments.val (.inr false)) index,
        (arguments.val (.inl false)).property _ _⟩
    | true => fun index => ⟨(arguments.val (.inl true)).val index (arguments.val (.inr true)),
        (arguments.val (.inl true)).property _ _⟩
  have dotted := (integerDotProduct_realizable inner leftWidth rightWidth).onResults
    step.inputDomains step.precondition arrays (by intros; trivial) (by
      intro choice
      cases choice
      · exact row
      · exact column)
  have entry : step.Realizable := by
    apply dotted.withSpecification step.precondition step.compute (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    exact integerDotProduct_correct inner leftWidth rightWidth sizes
      ⟨fun choice => arrays choice sizes ⟨arguments, valid⟩, trivial⟩
  have tabulated := matrixTabulate_realizable computation.inputDomains scalar rows columns operation entry
  have collected := tabulated.reindexOutput computation.outputDomain.Carrier
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (inner + leftWidth + rightWidth)))
  exact collected.withSpecification computation.precondition computation.compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
