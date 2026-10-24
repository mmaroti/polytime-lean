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

import Polytime2.Matrices.MinorWitnessMath
import Polytime2.Matrices.MinorInvarianceMath

/-! # Input-size bounds for normalized Hermite pivot blocks

An upper triangular integer block with positive diagonal and reduced entries
above the diagonal has every entry bounded by its determinant magnitude. If
it is a supported block of a unimodular row transform, the automatic original
minor witness supplies a width derived solely from the original input. This
bounds the pivot block; trailing columns need a separate row-space argument.
-/

namespace Polytime2.IntegerMatrix

/-- A column-reduced positive triangular block is bounded entrywise by its determinant. -/
theorem normalized_block_entry_le_det {rank : ℕ} (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (upper : matrix.IsUpperTriangular) (positive : ∀ index, 0 < matrix index index)
    (reduced : ∀ row column, row < column → 0 ≤ matrix row column ∧ matrix row column < matrix column column) :
    ∀ row column, (matrix row column).natAbs ≤ matrix.det.natAbs := by
  intro row column
  have diagonal := upperTriangular_diagonal_natAbs_le matrix upper column
    (fun other _ => ne_of_gt (positive other))
  by_cases same : row = column
  · simpa only [same] using diagonal
  · by_cases before : row < column
    · have range := reduced row column before
      have castBound : ((matrix row column).natAbs : ℤ) ≤ ((matrix column column).natAbs : ℤ) := by
        rw [Int.natAbs_of_nonneg range.1, Int.natAbs_of_nonneg (le_of_lt (positive column))]
        exact range.2.le
      have bound : (matrix row column).natAbs ≤ (matrix column column).natAbs := by exact_mod_cast castBound
      exact bound.trans diagonal
    · have below : column < row := lt_of_le_of_ne (le_of_not_gt before) (Ne.symm same)
      rw [upper below, Int.natAbs_zero]
      exact Nat.zero_le _

/-- Normalized supported pivot blocks have entry widths in the original input sizes. -/
theorem normalized_supported_block_bound {Row Column : Type} [Fintype Row] [DecidableEq Row] {rank : ℕ} (width : ℕ)
    (currentRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (equation : left * original = current) (unit : IsUnit left.det)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row (selectedColumns column) = 0)
    (upper : (current.submatrix currentRows selectedColumns).IsUpperTriangular)
    (positive : ∀ index, 0 < current (currentRows index) (selectedColumns index))
    (reduced : ∀ row column : Fin rank, row < column →
      0 ≤ current (currentRows row) (selectedColumns column) ∧
        current (currentRows row) (selectedColumns column) < current (currentRows column) (selectedColumns column))
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ row column : Fin rank, (current (currentRows row) (selectedColumns column)).natAbs <
      2 ^ (rank * (width + rank) + 1) := by
  have determinant := unimodular_supported_minor_bound width currentRows selectedColumns original current left equation unit support entryBound
  exact fun row column => (normalized_block_entry_le_det _ upper positive reduced row column).trans_lt determinant

end Polytime2.IntegerMatrix
