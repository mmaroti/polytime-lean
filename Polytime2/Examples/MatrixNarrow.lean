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

import Polytime2.Matrices.IntegerResize
import Polytime2.TM0.Computation

/-! # Matrix narrowing preserves values and changes the canonical width

A signed rectangular example fits a smaller bound. Nonzero entries are rejected
by the zero-width precondition, while zero matrices and empty dimensions remain
admissible. Generic machine certificates cover every pair of widths.
-/

namespace Polytime2.Examples.MatrixNarrow

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (rows columns sourceWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixNarrow rows columns sourceWidth targetWidth).TM0Realizable :=
  (integerMatrixResize_realizable rows columns sourceWidth targetWidth).tm0

private def matrixValue (row column : ℕ) : ℤ :=
  if row = 0 then (if column = 0 then 3 else if column = 1 then -2 else 0)
  else if column = 0 then -3 else if column = 1 then 1 else 2

private noncomputable def arguments :
    (integerMatrixNarrow (Parameter := Empty) 2 3 4 2).Arguments Empty.elim := fun _ =>
  ⟨fun row column => matrixValue row.val column.val, by
    intro row column
    dsimp only [matrixValue]
    split_ifs <;> norm_num⟩

private theorem arguments_valid :
    (integerMatrixNarrow (Parameter := Empty) 2 3 4 2).precondition Empty.elim arguments := by
  intro row column
  dsimp [integerMatrixNarrow, arguments, matrixValue]
  split_ifs <;> norm_num

example : ((integerMatrixNarrow (Parameter := Empty) 2 3 4 2).compute Empty.elim
    ⟨arguments, arguments_valid⟩).val = (arguments ()).val := rfl

example : (integerMatrixNarrow (Parameter := Empty) 2 3 4 2).outputDomain.width Empty.elim = 18 := by
  change MvPolynomial.eval Empty.elim ((2 * 3) *
    (Polytime2.EncodedDomain.binaryIntegers (2 : MvPolynomial Empty ℕ)).widthPolynomial) = 18
  rw [map_mul]
  change MvPolynomial.eval Empty.elim (2 * 3 : MvPolynomial Empty ℕ) *
    (Polytime2.EncodedDomain.binaryIntegers (2 : MvPolynomial Empty ℕ)).width Empty.elim = 18
  rw [Polytime2.EncodedDomain.binaryIntegers_width]
  norm_num

example : ¬(integerMatrixNarrow (Parameter := Empty) 2 3 4 0).precondition Empty.elim arguments := by
  intro fits
  have entry := fits ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
  norm_num [integerMatrixNarrow, arguments, matrixValue] at entry

example (columns sourceWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixNarrow 0 columns sourceWidth targetWidth).Arguments sizes) :
    (integerMatrixNarrow 0 columns sourceWidth targetWidth).precondition sizes arguments := by
  intro row column
  have bounded := row.isLt
  norm_num at bounded

example : ((integerMatrixNarrow (Parameter := Empty) 2 3 4 0).compute Empty.elim
    ⟨(fun _ => ⟨0, by intro _row _column; norm_num⟩), by intro _row _column; norm_num⟩).val = 0 := rfl

end Polytime2.Examples.MatrixNarrow
