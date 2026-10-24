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

import Polytime2.Matrices.IntegerLeadingBlock
import Polytime2.TM0.Computation

/-! # Leading blocks of signed rectangular matrices

Extraction and square diagonalization have standalone machine certificates.
A signed rectangular input retains its leading entry; rank zero requires no
positivity or triangularity assumptions on the surrounding matrix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerLeadingBlock

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter]
    (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerMatrixLeadingBlock rows columns rank width).TM0Realizable :=
  (integerMatrixLeadingBlock_realizable rows columns rank width).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerLeadingBlockDiagonalize rows columns rank width).TM0Realizable :=
  (integerLeadingBlockDiagonalize_realizable rows columns rank width).tm0

private noncomputable def signedMatrix :
    (integerMatrices (2 : MvPolynomial Empty ℕ) 3 3).Carrier Empty.elim :=
  ⟨fun row column => if row.val = 0 ∧ column.val = 0 then -2 else 0,
    by intro row column; dsimp only; split_ifs <;> norm_num⟩

example : ((integerMatrixLeadingBlock (2 : MvPolynomial Empty ℕ) 3 1 3).compute Empty.elim
    ⟨fun _ => signedMatrix, by constructor <;> norm_num⟩).val
      ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = -2 := by
  rfl

example {Parameter : Type} [Fintype Parameter]
    (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerLeadingBlockDiagonalize rows columns 0 width).Arguments sizes) :
    (integerLeadingBlockDiagonalize rows columns 0 width).precondition sizes arguments := by
  apply integerLeadingBlockDiagonalize_permitted rows columns 0 width sizes arguments (by simp) (by simp)
  · intro row column before
    have impossible := row.isLt
    simp at impossible
  · intro index
    have impossible := index.isLt
    simp at impossible

end Polytime2.Examples.IntegerLeadingBlock
