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

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! # Mathematical row operations and their column prefixes -/

namespace Polytime2.MatrixRows

-- scalarLevel: mathematical entries, independent of any tape presentation.
universe scalarLevel
variable {Scalar : Type scalarLevel} {rows columns : ℕ}

def entryUpdate (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) : Matrix (Fin rows) (Fin columns) Scalar :=
  let output := operation coefficient (matrix source column) (matrix target column)
  let intermediate := if writeSource then
    Function.update matrix source (Function.update (matrix source) column output.1) else matrix
  Function.update intermediate target (Function.update (intermediate target) column output.2)

theorem entryUpdate_apply (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target row : Fin rows) (column position : Fin columns) :
    entryUpdate writeSource operation coefficient matrix source target column row position =
      if row = target ∧ position = column then (operation coefficient (matrix source column) (matrix target column)).2
      else if writeSource = true ∧ row = source ∧ position = column then
        (operation coefficient (matrix source column) (matrix target column)).1 else matrix row position := by
  cases writeSource <;> by_cases isTarget : row = target <;> by_cases isSource : row = source <;>
    by_cases same : position = column <;> simp_all [entryUpdate, Function.update]

/-- Apply the entry operation independently to every column of two rows. -/
def transform (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  entryUpdate writeSource operation coefficient matrix source target column row column

/-- The first `processed` columns have their final values. -/
def processedColumns (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (processed : ℕ) : Matrix (Fin rows) (Fin columns) Scalar := fun row column =>
  if column.val < processed then transform writeSource operation coefficient matrix source target row column else matrix row column

theorem processedColumns_zero (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    processedColumns writeSource operation coefficient matrix source target 0 = matrix := by
  ext row column
  simp [processedColumns]

theorem processedColumns_complete (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows) :
    processedColumns writeSource operation coefficient matrix source target columns = transform writeSource operation coefficient matrix source target := by
  ext row column
  simp [processedColumns, column.isLt]

theorem processedColumns_next (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar)
    (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (column : Fin columns) :
    entryUpdate writeSource operation coefficient
      (processedColumns writeSource operation coefficient matrix source target column.val) source target column =
      processedColumns writeSource operation coefficient matrix source target (column.val + 1) := by
  ext row position
  by_cases same : position = column
  · subst position
    simp [entryUpdate_apply, processedColumns, transform]
  · have unequal : position.val ≠ column.val := by intro equal; exact same (Fin.ext equal)
    have before : position.val < column.val + 1 ↔ position.val < column.val := by omega
    simp [entryUpdate_apply, processedColumns, same, before]

end Polytime2.MatrixRows
