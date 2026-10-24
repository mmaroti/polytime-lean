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

import Polytime2.Arrays.Tabulate
import Polytime2.Computation.Conditional

/-! # Tabulating ordinary rectangular matrices

A certified operation on mathematical row and column coordinates is lifted to
the whole matrix. Both dimensions and element widths may depend on sizes.
Nested array tabulation and the existing row-major matrix codec provide the
realization, with coordinate generation and all output construction included.
-/

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- A scalar tabulation step has immutable context and two ordinary coordinates.
False names the row and true names the column. -/
noncomputable def matrixTabulateStep (context : Context → EncodedDomain.{0, 0} Parameter)
    (target : EncodedDomain.{0, 0} Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      Fin (MvPolynomial.eval sizes rows) → Fin (MvPolynomial.eval sizes columns) → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun name => EncodedDomain.arrayPosition (if name then columns else rows))
  outputDomain := target
  precondition _ _ := True
  compute sizes arguments := operation sizes (fun name => arguments.val (.inl name))
    (arguments.val (.inr false)) (arguments.val (.inr true))

/-- Tabulate a matrix from its finite coordinates and a shared context. -/
noncomputable def matrixTabulate (context : Context → EncodedDomain.{0, 0} Parameter)
    (target : EncodedDomain.{0, 0} Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      Fin (MvPolynomial.eval sizes rows) → Fin (MvPolynomial.eval sizes columns) → target.Carrier sizes) :
    Computation Parameter Context where
  inputDomains := context
  outputDomain := EncodedDomain.matrix target rows columns
  precondition _ _ := True
  compute sizes arguments := operation sizes arguments.val

theorem matrixTabulate_realizable (context : Context → EncodedDomain.{0, 0} Parameter)
    (target : EncodedDomain.{0, 0} Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      Fin (MvPolynomial.eval sizes rows) → Fin (MvPolynomial.eval sizes columns) → target.Carrier sizes)
    (step : (matrixTabulateStep context target rows columns operation).Realizable) :
    (matrixTabulate context target rows columns operation).Realizable := by
  let innerContext := Sum.elim context (fun _ : Unit => EncodedDomain.arrayPosition rows)
  let innerOperation sizes (arguments : ∀ name, (innerContext name).Carrier sizes) column :=
    operation sizes (fun name => arguments (.inl name)) (arguments (.inr ())) column
  let innerStep := arrayTransformStep innerContext (EncodedDomain.arrayPosition columns) target innerOperation
  have innerReady : innerStep.Realizable := step.onResults innerStep.inputDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | .inl original => arguments.val (.inl (.inl original))
      | .inr false => arguments.val (.inl (.inr ()))
      | .inr true => arguments.val (.inr ())) (by intros; trivial) (by
        intro name
        cases name with
        | inl original => exact Realizable.argument innerStep.inputDomains (.inl (.inl original)) (fun _ _ => True)
        | inr coordinate =>
          cases coordinate
          · exact Realizable.argument innerStep.inputDomains (.inl (.inr ())) (fun _ _ => True)
          · exact Realizable.argument innerStep.inputDomains (.inr ()) (fun _ _ => True))
  have inner := arrayTabulate_realizable innerContext target columns innerOperation innerReady
  have outer := arrayTabulate_realizable context (target.arrayOfLength columns) rows
    (fun sizes arguments row column => operation sizes arguments row column) inner
  exact outer.reinterpretOutput (EncodedDomain.matrix target rows columns) (fun _ value => value)
    (fun sizes => congrArg (MvPolynomial.eval sizes) (mul_assoc rows columns target.widthPolynomial))
    (fun sizes value => EncodedDomain.matrix_nested_encode_bits target rows columns sizes value)

end Polytime2.Computation
