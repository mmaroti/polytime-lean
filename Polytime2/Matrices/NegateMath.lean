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

import Polytime2.Matrices.IntegerOperationsMath

/-! # Unimodular sign changes of one integer row or column

A single sign change is needed even for a one-by-one negative matrix, where
there is no distinct row or column available for a two-index operation.
Mathlib's elementary row scaling gives the transformation and its determinant.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [Fintype Row]

/-- Negate one row using an ordinary integer elementary matrix. -/
def rowNegate (target : Row) (matrix : Matrix Row Column ℤ) : Matrix Row Column ℤ :=
  Matrix.rowScale target (-1) * matrix

theorem rowNegate_apply (target row : Row) (matrix : Matrix Row Column ℤ) (column : Column) :
    rowNegate target matrix row column = if row = target then -matrix row column else matrix row column := by
  by_cases same : row = target <;>
    simp [rowNegate, Matrix.rowScale_mul, Matrix.updateRow_apply, Matrix.row, same]

/-- Negating a zero entry leaves the whole corresponding column fixed. -/
theorem rowNegate_zero_column (source : Row) (column : Column) (matrix : Matrix Row Column ℤ)
    (zero : matrix source column = 0) (row : Row) :
    rowNegate source matrix row column = matrix row column := by
  rw [rowNegate_apply]
  split_ifs with same
  · subst row; simp only [zero, neg_zero]
  · rfl

theorem rowNegate_unimodular (target : Row) : (Matrix.rowScale target (-1 : ℤ)).det = -1 := by
  simp [Matrix.rowScale]

theorem rowNegate_bound (width : ℕ) (target : Row) (matrix : Matrix Row Column ℤ)
    (bounded : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (rowNegate target matrix row column).natAbs < 2 ^ width := by
  intro row column
  rw [rowNegate_apply]
  split_ifs <;> simpa using bounded row column

end Polytime2.IntegerMatrix
