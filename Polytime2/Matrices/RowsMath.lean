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

import Polytime2.Matrices.RowsContract
import Polytime2.Matrices.RowOperationsMath

/-! # Mathematical matrices computed by the standard row controller -/

namespace Polytime2.StandardMatrixRows

open StandardMatrixEntry (index_lt)

-- scalarLevel: mathematical entries of a rectangular matrix.
universe scalarLevel
variable {Carrier : Type scalarLevel}

/-- Row-major coordinates, including the polynomial evaluation's length cast. -/
noncomputable def matrixIndex (sizes : Fin 3 → ℕ) :
    Fin (sizes 1) × Fin (sizes 2) ≃ Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := by
  have sameLength : MvPolynomial.eval sizes StandardMatrixEntry.length = sizes 1 * sizes 2 := by
    simp [StandardMatrixEntry.length]
  exact finProdFinEquiv.trans (finCongr sameLength.symm)

theorem matrixIndex_val (sizes : Fin 3 → ℕ) (row : Fin (sizes 1)) (column : Fin (sizes 2)) :
    (matrixIndex sizes (row, column)).val = row.val * sizes 2 + column.val := by
  simp [matrixIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem matrixIndex_eq (sizes : Fin 3 → ℕ) (row : Fin (sizes 1)) (column : Fin (sizes 2)) :
    matrixIndex sizes (row, column) =
      ⟨row.val * sizes 2 + column.val, index_lt sizes row.val column.val row.isLt column.isLt⟩ :=
  Fin.ext (matrixIndex_val sizes row column)

/-- Mathematical matrices and the row-major arrays used by the controller
have the same coordinates. The bit encoding stays inside the encoded domain. -/
noncomputable def matrixEquiv (sizes : Fin 3 → ℕ) :
    Matrix (Fin (sizes 1)) (Fin (sizes 2)) Carrier ≃
      (Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) → Carrier) where
  toFun matrix index :=
    let coordinate := (matrixIndex sizes).symm index
    matrix coordinate.1 coordinate.2
  invFun array row column := array (matrixIndex sizes (row, column))
  left_inv matrix := by
    funext row column
    exact congrArg (fun coordinate => matrix coordinate.1 coordinate.2) ((matrixIndex sizes).left_inv (row, column))
  right_inv array := by
    funext index
    exact congrArg array ((matrixIndex sizes).right_inv index)

@[simp] theorem matrixEquiv_apply (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Carrier) (row : Fin (sizes 1)) (column : Fin (sizes 2)) :
    matrixEquiv sizes matrix (matrixIndex sizes (row, column)) = matrix row column := by
  change matrix ((matrixIndex sizes).symm (matrixIndex sizes (row, column))).1
    ((matrixIndex sizes).symm (matrixIndex sizes (row, column))).2 = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem matrixEquiv_symm_apply (sizes : Fin 3 → ℕ)
    (array : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) → Carrier)
    (row : Fin (sizes 1)) (column : Fin (sizes 2)) :
    (matrixEquiv sizes).symm array row column = array (matrixIndex sizes (row, column)) := rfl

theorem matrixEquiv_entryUpdate (sizes : Fin 3 → ℕ) (writeSource : Bool)
    (operation : Carrier → Carrier → Carrier → Carrier × Carrier) (coefficient : Carrier)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Carrier)
    (source target : Fin (sizes 1)) (column : Fin (sizes 2)) :
    matrixEquiv sizes (MatrixRows.entryUpdate writeSource operation coefficient matrix source target column) =
      Function.update (Function.update (matrixEquiv sizes matrix) (matrixIndex sizes (source, column))
        (if writeSource then (operation coefficient (matrix source column) (matrix target column)).1 else matrix source column))
        (matrixIndex sizes (target, column)) (operation coefficient (matrix source column) (matrix target column)).2 := by
  apply (matrixEquiv sizes).symm.injective
  funext row position
  simp only [matrixEquiv_symm_apply]
  cases writeSource <;> by_cases isSource : row = source <;> by_cases isTarget : row = target <;>
    by_cases same : position = column <;>
      simp_all [MatrixRows.entryUpdate_apply, Prod.mk.injEq, matrixEquiv_apply]

/-- The traversal invariant is exactly the ordinary matrix prefix invariant:
completed columns have their final row-operation values. -/
theorem processed_eq_matrix (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (sizes : Fin 3 → ℕ) (sourceRow targetRow : Fin (2 ^ sizes 0))
    (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
    (coefficient : scalar.Carrier Empty.elim)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) (scalar.Carrier Empty.elim))
    (count : ℕ) (bounded : count ≤ sizes 2) :
    processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient
        (matrixEquiv sizes matrix) count =
      matrixEquiv sizes (MatrixRows.processedColumns writeSource (operation Empty.elim) coefficient matrix
        ⟨sourceRow.val, sourceValid⟩ ⟨targetRow.val, targetValid⟩ count) := by
  induction count with
  | zero =>
    erw [MatrixRows.processedColumns_zero]
    rfl
  | succ count inductionHypothesis =>
    have valid : count < sizes 2 := by omega
    erw [processed.eq_def]
    dsimp only
    erw [dite_eq_left valid, inductionHypothesis (by omega)]
    erw [← MatrixRows.processedColumns_next writeSource (operation Empty.elim) coefficient matrix
      ⟨sourceRow.val, sourceValid⟩ ⟨targetRow.val, targetValid⟩ (⟨count, valid⟩ : Fin (sizes 2))]
    rw [matrixEquiv_entryUpdate]
    have sourceIndex := matrixIndex_eq sizes (⟨sourceRow.val, sourceValid⟩ : Fin (sizes 1)) (⟨count, valid⟩ : Fin (sizes 2))
    have targetIndex := matrixIndex_eq sizes (⟨targetRow.val, targetValid⟩ : Fin (sizes 1)) (⟨count, valid⟩ : Fin (sizes 2))
    erw [← sourceIndex, ← targetIndex]
    simp only [matrixEquiv_apply, StandardMatrixRowEntry.effectiveOperation]
    rfl

end Polytime2.StandardMatrixRows
