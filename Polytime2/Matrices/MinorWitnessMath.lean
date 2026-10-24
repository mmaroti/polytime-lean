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

/-! # Nonzero original minors from a transformed block

A nonzero square minor of `left * original` implies a nonzero original minor
with the same columns. Determinant multilinearity expands the product over
row choices; a nonzero term has an injective row choice. This is a proof-only
existence argument, not a runtime enumeration of minors.
-/

namespace Polytime2.IntegerMatrix

/-- A rectangular product expands over row choices, before grouping equal selections. -/
theorem rectangular_det_mul_expand {Index : Type} [Fintype Index] {rank : ℕ}
    (left : Matrix (Fin rank) Index ℤ) (right : Matrix Index (Fin rank) ℤ) :
    (left * right).det = ∑ choice : Fin rank → Index,
      (∏ row, left row (choice row)) * (right.submatrix choice id).det := by
  classical
  have rows : left * right = (fun row => ∑ index, left row index • right index) := by
    ext row column
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [rows]
  change (Matrix.detRowAlternating (R := ℤ) (n := Fin rank)).toMultilinearMap
    (fun row => ∑ index, left row index • right index) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro choice _
  exact Matrix.det_mul_column (fun row => left row (choice row)) (right.submatrix choice id)

/-- A nonzero transformed minor supplies a nonzero original minor with the same columns. -/
theorem exists_nonzero_original_minor {Row Column : Type} [Fintype Row] {rank : ℕ}
    (selectedRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (equation : left * original = current)
    (nonzero : (current.submatrix selectedRows selectedColumns).det ≠ 0) :
    ∃ originalRows : Fin rank ↪ Row, (original.submatrix originalRows selectedColumns).det ≠ 0 := by
  classical
  let first := left.submatrix selectedRows id
  let second := original.submatrix id selectedColumns
  have product : first * second = current.submatrix selectedRows selectedColumns := by
    ext row column
    simpa only [first, second, Matrix.submatrix_apply, Matrix.mul_apply, id_eq] using
      congrFun (congrFun equation (selectedRows row)) (selectedColumns column)
  have sumNonzero : (∑ choice : Fin rank → Row,
      (∏ row, first row (choice row)) * (second.submatrix choice id).det) ≠ 0 := by
    rw [← rectangular_det_mul_expand, product]
    exact nonzero
  obtain ⟨choice, _member, termNonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero sumNonzero
  have minorNonzero := (mul_ne_zero_iff.mp termNonzero).2
  have injective : Function.Injective choice := by
    intro firstRow secondRow same
    by_contra different
    apply minorNonzero
    exact Matrix.det_zero_of_row_eq different (by
      funext column
      simp only [Matrix.submatrix_apply, same])
  exact ⟨⟨choice, injective⟩, minorNonzero⟩

/-- Supported blocks have an input-size bound without a caller-supplied nonzero minor. -/
theorem unimodular_supported_minor_bound {Row Column : Type} [Fintype Row] [DecidableEq Row] {rank : ℕ} (width : ℕ)
    (currentRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (equation : left * original = current) (unit : IsUnit left.det)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row (selectedColumns column) = 0)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    (current.submatrix currentRows selectedColumns).det.natAbs < 2 ^ (rank * (width + rank) + 1) := by
  classical
  by_cases zero : (current.submatrix currentRows selectedColumns).det = 0
  · rw [zero, Int.natAbs_zero]
    positivity
  · obtain ⟨originalRows, nonzero⟩ := exists_nonzero_original_minor currentRows selectedColumns original current left equation zero
    exact (Int.natAbs_le_of_dvd_ne_zero
      (unimodular_supported_minor_dvd originalRows currentRows selectedColumns original current left equation unit support) nonzero).trans_lt
      (determinant_bound width rank _ (fun row column => entryBound (originalRows row) (selectedColumns column)))

end Polytime2.IntegerMatrix
