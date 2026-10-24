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

import Polytime2.Matrices.ExtendIntegerBasis
import Polytime2.TM0.Computation

/-! # Active-block basis extension examples

A nonidentity active block retains its entries and gains an identity tail.
An empty zero-width block still extends to the full identity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.ExtendIntegerBasis

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (dimension rank width : MvPolynomial Parameter ℕ) : (extendIntegerBasis dimension rank width).TM0Realizable :=
  (extendIntegerBasis_realizable dimension rank width).tm0

private noncomputable def arguments : (extendIntegerBasis (Parameter := Empty) 4 2 2).Arguments Empty.elim :=
  fun _ => ⟨(fun row column => if row.val = column.val then 1 else if row.val = 0 then 2 else 0), by
    intro row column
    dsimp only
    split_ifs <;> norm_num⟩

example :
    let result := (extendIntegerBasis (Parameter := Empty) 4 2 2).compute Empty.elim ⟨arguments, by
      change MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ) ≤ MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ)
      norm_num⟩
    result.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 2 ∧
      result.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 ∧
      result.val ⟨3, by norm_num⟩ ⟨3, by norm_num⟩ = 1 ∧
      result.val ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ = 0 ∧
      result.val ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  dsimp only
  rw [extendIntegerBasis_correct]
  norm_num [Polytime2.IntegerMatrix.extendDiagonalBasis_apply, arguments]

example (dimension : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (extendIntegerBasis dimension 0 0).Arguments sizes) :
    ((extendIntegerBasis dimension 0 0).compute sizes ⟨arguments, by
      change MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ) ≤ MvPolynomial.eval sizes dimension
      simp⟩).val = 1 := by
  rw [extendIntegerBasis_correct]
  ext row column
  simp [Polytime2.IntegerMatrix.extendDiagonalBasis_apply, Matrix.one_apply, Fin.ext_iff]

end Polytime2.Examples.ExtendIntegerBasis
