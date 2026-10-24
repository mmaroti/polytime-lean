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

import Polytime2.Matrices.HermiteBlockBoundsMath
import Polytime2.Matrices.IntegerOperationsMath

/-! # Bounds for trailing columns of a compact Hermite matrix

A normalized positive pivot block bounds the entire reduced matrix when all
other rows are zero. An original nonzero minor is obtained from the accumulated
unimodular transformation. An adjugate identity extends the pivot coordinates
to every column using only original entries and original minors. No bound on
the inverse change-of-basis matrix is needed.
-/

namespace Polytime2.IntegerMatrix

/-- Eliminate an arbitrary row-coordinate factor from an adjugate extension identity. -/
theorem adjugate_row_extension {Column : Type} {rank : ℕ}
    (change pivot : Matrix (Fin rank) (Fin rank) ℤ) (full : Matrix (Fin rank) Column ℤ) :
    pivot * (change * pivot).adjugate * (change * full) = (change * pivot).det • full := by
  calc
    _ = (pivot * pivot.adjugate) * (change.adjugate * change) * full := by
      rw [Matrix.adjugate_mul_distrib]
      simp only [Matrix.mul_assoc]
    _ = (pivot.det * change.det) • full := by
      rw [Matrix.mul_adjugate, Matrix.adjugate_mul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [mul_comm]
    _ = (change * pivot).det • full := by rw [Matrix.det_mul, mul_comm]

/-- Original entry widths bound every cofactor, including the one-by-one case. -/
theorem adjugate_bound (width rank : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (matrix.adjugate row column).natAbs < 2 ^ (rank * (width + rank) + 1) := by
  cases rank with
  | zero => intro row; exact row.elim0
  | succ rank =>
    intro row column
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Int.natAbs_mul, Int.natAbs_pow]
    simp only [Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
    exact (determinant_bound width rank _ (fun first second => entryBound _ _)).trans_le
      (pow_le_pow_right₀ (by decide) (by nlinarith))

/-- Compact normalized Hermite matrices, including trailing columns, have original-input widths. -/
theorem normalized_supported_rows_bound {Row Column : Type} [Fintype Row] [DecidableEq Row] {rank : ℕ} (width : ℕ)
    (currentRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (equation : left * original = current) (unit : IsUnit left.det)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row column = 0)
    (upper : (current.submatrix currentRows selectedColumns).IsUpperTriangular)
    (positive : ∀ index, 0 < current (currentRows index) (selectedColumns index))
    (reduced : ∀ row column : Fin rank, row < column →
      0 ≤ current (currentRows row) (selectedColumns column) ∧
        current (currentRows row) (selectedColumns column) < current (currentRows column) (selectedColumns column))
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ row column, (current row column).natAbs <
      2 ^ (2 * (rank * (width + rank) + 1) + width + 2 * rank + 2) := by
  classical
  let minorWidth := rank * (width + rank) + 1
  let block := current.submatrix currentRows selectedColumns
  have blockBound : ∀ row column, (block row column).natAbs < 2 ^ minorWidth :=
    normalized_supported_block_bound width currentRows selectedColumns original current left equation unit
      (fun row outside column => support row outside (selectedColumns column)) upper positive reduced entryBound
  have blockNonzero : block.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular upper]
    exact ne_of_gt (Finset.prod_pos (fun index _ => positive index))
  obtain ⟨originalRows, nonzero⟩ := exists_nonzero_original_minor currentRows selectedColumns original current left equation blockNonzero
  let inputBlock := original.submatrix originalRows selectedColumns
  let change := left⁻¹.submatrix originalRows currentRows
  let inputRows := original.submatrix originalRows id
  let currentRowMatrix := current.submatrix currentRows id
  have recovered : original = left⁻¹ * current := calc
    original = left⁻¹ * (left * original) := (Matrix.nonsing_inv_mul_cancel_left left original unit).symm
    _ = left⁻¹ * current := by rw [equation]
  have blockEquation : inputBlock = change * block :=
    supported_minor_factorization originalRows currentRows selectedColumns original current left⁻¹ recovered
      (fun row outside column => support row outside (selectedColumns column))
  have rowEquation : inputRows = change * currentRowMatrix :=
    supported_minor_factorization originalRows currentRows (id : Column → Column) original current left⁻¹ recovered support
  have extension : block * inputBlock.adjugate * inputRows = inputBlock.det • currentRowMatrix := by
    rw [blockEquation, rowEquation]
    exact adjugate_row_extension change block currentRowMatrix
  have adjugateBound : ∀ row column, (inputBlock.adjugate row column).natAbs < 2 ^ minorWidth :=
    adjugate_bound width rank inputBlock (fun row column => entryBound (originalRows row) (selectedColumns column))
  have firstBound : ∀ row column, ((block * inputBlock.adjugate) row column).natAbs < 2 ^ (minorWidth + minorWidth + rank + 1) := by
    simpa only [Fintype.card_fin] using mul_bound minorWidth minorWidth block inputBlock.adjugate blockBound adjugateBound
  have finalBound := mul_bound (minorWidth + minorWidth + rank + 1) width
    (block * inputBlock.adjugate) inputRows firstBound (fun row column => entryBound (originalRows row) column)
  intro row column
  by_cases inside : row ∈ Set.range currentRows
  · obtain ⟨index, rfl⟩ := inside
    have valueEquation := congrArg (fun matrix => matrix index column) extension
    change (block * inputBlock.adjugate * inputRows) index column = inputBlock.det * current (currentRows index) column at valueEquation
    have valueLe : (current (currentRows index) column).natAbs ≤ ((block * inputBlock.adjugate * inputRows) index column).natAbs := by
      rw [valueEquation, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr nonzero)
    exact (valueLe.trans_lt (finalBound index column)).trans_le (pow_le_pow_right₀ (by decide) (by
      simp only [Fintype.card_fin]
      omega))
  · rw [support row inside column, Int.natAbs_zero]
    positivity

end Polytime2.IntegerMatrix
