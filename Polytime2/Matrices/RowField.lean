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


import Polytime2.Matrices.RowOperationsMath
import Polytime2.Matrices.Basic

/-! # Finite-field instances of the shared matrix-row traversal

Scaling and addition write only the target. Swapping writes both rows and
also covers coincident indices. Coefficients are preserved runtime scalars.
-/

namespace Polytime2.MatrixRowField

variable {Scalar : Type} [Field Scalar] {rows columns : ℕ}

def scale (coefficient source target : Scalar) : Scalar × Scalar := (source, coefficient * target)
def normalize (coefficient source target : Scalar) : Scalar × Scalar := scale coefficient⁻¹ source target
def add (coefficient source target : Scalar) : Scalar × Scalar := (source, target + coefficient * source)
def swap (_coefficient source target : Scalar) : Scalar × Scalar := (target, source)

theorem scale_transform (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) :
    MatrixRows.transform false scale coefficient matrix source target =
      MatrixOperations.scaleRow matrix target coefficient := by
  ext row column
  by_cases isTarget : row = target <;>
    simp [MatrixRows.transform, MatrixRows.entryUpdate_apply, scale, MatrixOperations.scaleRow, isTarget]

theorem normalize_transform (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) :
    MatrixRows.transform false normalize coefficient matrix source target =
      MatrixOperations.scaleRow matrix target coefficient⁻¹ := by
  ext row column
  by_cases isTarget : row = target <;>
    simp [MatrixRows.transform, MatrixRows.entryUpdate_apply, normalize, scale, MatrixOperations.scaleRow, isTarget]

theorem add_transform (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) :
    MatrixRows.transform false add coefficient matrix source target =
      Function.update matrix target (fun column => matrix target column + coefficient * matrix source column) := by
  ext row column
  by_cases isTarget : row = target <;>
    simp [MatrixRows.transform, MatrixRows.entryUpdate_apply, add, Function.update, isTarget]

omit [Field Scalar] in
theorem swap_transform (coefficient : Scalar) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) :
    MatrixRows.transform true swap coefficient matrix source target = MatrixOperations.swapRows matrix source target := by
  ext row column
  by_cases isSource : row = source <;> by_cases isTarget : row = target <;>
    simp_all [MatrixRows.transform, MatrixRows.entryUpdate_apply, swap,
      MatrixOperations.swapRows, Equiv.swap_apply_def]

end Polytime2.MatrixRowField
