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

import Polytime2.Matrices.Tabulate
import Polytime2.Arrays.Operations

/-! # Certified matrix transposition

Transposition changes the order of canonical row-major bits. The realization
therefore tabulates the transposed matrix using two certified array lookups.
This includes construction of the output for rectangular and empty matrices.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Transpose an ordinary rectangular matrix without additional preconditions. -/
noncomputable def matrixTranspose (element : EncodedDomain.{0, 0} Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := matrix element rows columns
  outputDomain := matrix element columns rows
  precondition _ _ := True
  compute _ arguments row column := arguments.val () column row

theorem matrixTranspose_realizable (element : EncodedDomain.{0, 0} Parameter)
    (rows columns : MvPolynomial Parameter ℕ) :
    (matrixTranspose element rows columns).Realizable := by
  let context := fun _ : Unit => (element.arrayOfLength columns).arrayOfLength rows
  let operation sizes (arguments : ∀ name, (context name).Carrier sizes) row column :=
    arguments () column row
  let step := matrixTabulateStep context element columns rows operation
  have selected := (Realizable.Internal.arrayLookupWithIndex_realizable
    (element.arrayOfLength columns) (arrayPosition rows) (fun _ index => index.val)
    (arrayPosition_value rows) rows).onResults step.inputDomains (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr true)
      | true => arguments.val (.inl ()))
    (by intro sizes arguments; exact (arguments.val (.inr true)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr true) (fun _ _ => True)
      · exact Realizable.argument step.inputDomains (.inl ()) (fun _ _ => True))
  have entry : step.Realizable := (Realizable.Internal.arrayLookupWithIndex_realizable element
    (arrayPosition columns) (fun _ index => index.val) (arrayPosition_value columns) columns).onResults
    step.inputDomains (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr false)
      | true => arguments.val (.inl ()) (arguments.val (.inr true)))
    (by intro sizes arguments; exact (arguments.val (.inr false)).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr false) (fun _ _ => True)
      · exact selected)
  have tabulated := matrixTabulate_realizable context element columns rows operation entry
  exact tabulated.reinterpretInputs (matrixTranspose element rows columns).inputDomains
    (fun _ _ value => value)
    (fun _ sizes => congrArg (MvPolynomial.eval sizes) (mul_assoc rows columns element.widthPolynomial))
    (fun _ sizes value => matrix_nested_encode_bits element rows columns sizes value)
    (fun _ _ => True) (by intros; trivial)

end Polytime2.Computation
