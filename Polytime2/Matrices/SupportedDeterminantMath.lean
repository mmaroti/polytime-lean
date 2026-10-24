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

import Polytime2.Matrices.MinorBoundsMath

/-! # Determinants of fully supported rectangular presentations

If all nonzero entries lie in a selected square block, a two-sided presentation
restricts to products with that block. Mutual divisibility under unimodular
transformations then preserves its determinant magnitude, even for singular
blocks and empty dimensions.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [Fintype Row] [Fintype Column] {rank : ℕ}

/-- Full row and column support restrict a two-sided presentation to its square block. -/
theorem supported_presentation_factorization (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = current)
    (rowSupport : ∀ row ∉ Set.range selectedRows, ∀ column, original row column = 0)
    (columnSupport : ∀ column ∉ Set.range selectedColumns, ∀ row, original row column = 0) :
    current.submatrix selectedRows selectedColumns =
      left.submatrix selectedRows selectedRows * original.submatrix selectedRows selectedColumns *
        right.submatrix selectedColumns selectedColumns := by
  have leftFactor := supported_minor_factorization selectedRows selectedRows selectedColumns current (original * right) left
    (by simpa only [Matrix.mul_assoc] using equation.symm) (by
      intro row outside column
      simp only [Matrix.mul_apply, rowSupport row outside, zero_mul, Finset.sum_const_zero])
  have rightFactor := supported_minor_factorization selectedColumns selectedColumns selectedRows
    (original * right).transpose original.transpose right.transpose (Matrix.transpose_mul original right)
    (fun column outside row => columnSupport column outside (selectedRows row))
  have rightEquation := congrArg Matrix.transpose rightFactor
  simp only [Matrix.transpose_mul, Matrix.transpose_submatrix, Matrix.transpose_transpose] at rightEquation
  rw [leftFactor, rightEquation, Matrix.mul_assoc]

/-- The original supported block determinant divides every transformed selected block determinant. -/
theorem supported_presentation_det_dvd (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = current)
    (rowSupport : ∀ row ∉ Set.range selectedRows, ∀ column, original row column = 0)
    (columnSupport : ∀ column ∉ Set.range selectedColumns, ∀ row, original row column = 0) :
    (original.submatrix selectedRows selectedColumns).det ∣ (current.submatrix selectedRows selectedColumns).det := by
  refine ⟨(left.submatrix selectedRows selectedRows).det * (right.submatrix selectedColumns selectedColumns).det, ?_⟩
  rw [supported_presentation_factorization selectedRows selectedColumns original current left right equation rowSupport columnSupport,
    Matrix.det_mul, Matrix.det_mul]
  ring

/-- Unimodular presentations preserve determinant magnitude when both matrices are fully supported. -/
theorem supported_presentation_det_natAbs [DecidableEq Row] [DecidableEq Column]
    (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ) (right : Matrix Column Column ℤ)
    (equation : left * original * right = current) (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det)
    (originalRows : ∀ row ∉ Set.range selectedRows, ∀ column, original row column = 0)
    (originalColumns : ∀ column ∉ Set.range selectedColumns, ∀ row, original row column = 0)
    (currentRows : ∀ row ∉ Set.range selectedRows, ∀ column, current row column = 0)
    (currentColumns : ∀ column ∉ Set.range selectedColumns, ∀ row, current row column = 0) :
    (current.submatrix selectedRows selectedColumns).det.natAbs =
      (original.submatrix selectedRows selectedColumns).det.natAbs := by
  have inverse : left⁻¹ * current * right⁻¹ = original := by
    calc
      _ = (left⁻¹ * (left * (original * right))) * right⁻¹ := by rw [← equation]; simp only [Matrix.mul_assoc]
      _ = (original * right) * right⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left left _ leftUnit]
      _ = original := Matrix.mul_nonsing_inv_cancel_right right original rightUnit
  apply Nat.dvd_antisymm
  · simpa only [Int.natAbs_dvd_natAbs] using supported_presentation_det_dvd selectedRows selectedColumns
      current original left⁻¹ right⁻¹ inverse currentRows currentColumns
  · simpa only [Int.natAbs_dvd_natAbs] using supported_presentation_det_dvd selectedRows selectedColumns
      original current left right equation originalRows originalColumns

end Polytime2.IntegerMatrix
