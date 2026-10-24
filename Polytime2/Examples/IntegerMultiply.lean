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

import Polytime2.Matrices.IntegerMultiplyRealizable
import Polytime2.TM0.Computation

/-! # Mathematical product bounds for rectangular integer matrices

The product interface accepts independent input widths and needs no overflow
premise. An empty shared dimension returns zero, including when either outer
dimension is empty. Dot-product folds and matrix multiplication also have
standalone TM0 certificates; a signed dot product checks cancellation.
-/

namespace Polytime2.Examples.IntegerMultiply

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter]
    (rows columns leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerMatrixMultiply rows 0 columns leftWidth rightWidth).Arguments sizes //
      (integerMatrixMultiply rows 0 columns leftWidth rightWidth).precondition sizes arguments}) :
    ((integerMatrixMultiply rows 0 columns leftWidth rightWidth).compute sizes arguments).val = 0 := by
  ext row column
  simp [integerMatrixMultiply, Matrix.mul_apply]

example {Parameter : Type} [Fintype Parameter]
    (rows inner columns leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixMultiply rows inner columns leftWidth rightWidth).TM0Realizable :=
  (integerMatrixMultiply_realizable rows inner columns leftWidth rightWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerDotProduct length leftWidth rightWidth).TM0Realizable :=
  (integerDotProduct_realizable length leftWidth rightWidth).tm0

private noncomputable def signedInputs :
    (integerDotProduct (2 : MvPolynomial Empty ℕ) 3 3).Arguments Empty.elim :=
  fun choice index => match choice with
    | false => ⟨if index.val = 0 then -2 else 3, by split_ifs <;> norm_num⟩
    | true => ⟨if index.val = 0 then 4 else -1, by split_ifs <;> norm_num⟩

example : ((integerDotProduct (2 : MvPolynomial Empty ℕ) 3 3).compute Empty.elim
    ⟨signedInputs, trivial⟩).val = -11 := by
  rw [integerDotProduct_correct]
  simp only [signedInputs]
  have dimension : MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ) = 2 := by norm_num
  rw [dimension]
  norm_num [Fin.sum_univ_two]

end Polytime2.Examples.IntegerMultiply
