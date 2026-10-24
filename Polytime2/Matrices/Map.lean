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

import Polytime2.Arrays.Transform

/-! # Mapping a certified scalar operation over a rectangular matrix

The mathematical result applies the operation entrywise. Flattening and
unflattening reuse the existing row-major codec; all traversal and output costs
come from the generic array map, including empty dimensions and varying widths.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def matrixMap (source target : EncodedDomain.{0, 0} Parameter)
    (rows columns : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.matrix source rows columns
  outputDomain := EncodedDomain.matrix target rows columns
  precondition _ _ := True
  compute sizes arguments := fun row column => operation sizes (arguments.val () row column)

theorem matrixMap_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (rows columns : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (step : (unaryMap source target (fun _ _ => True)
      (fun sizes value => operation sizes value.val)).Realizable) :
    (matrixMap source target rows columns operation).Realizable := by
  have mapped := (mapArray_realizable source target (rows * columns) operation step).reindexDomains
    (fun _ => EncodedDomain.matrix source rows columns) (EncodedDomain.matrix target rows columns)
    (fun _ sizes => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes)
    (fun sizes => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  apply mapped.withSpecification (fun _ _ => True) (matrixMap source target rows columns operation).compute
    (by intros; trivial)
  intro sizes arguments valid
  apply (EncodedDomain.MatrixEncoding.flattenPolynomial (Carrier := target.Carrier sizes) rows columns sizes).injective
  change (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes)
    ((EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes).symm
      (fun index => operation sizes
        (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes
          (arguments ()) index))) = _
  rw [Equiv.apply_symm_apply]
  funext index
  rfl

end Polytime2.Computation
