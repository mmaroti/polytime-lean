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

import Polytime2.Matrices.HermiteInsertMath
import Polytime2.Matrices.HermiteRowBoundsMath
import Polytime2.Matrices.RectangularDiagonalMath

/-! # Restricting Hermite bounds to processed inputs

A basis with no processed-row coefficients on future inputs, and identity rows
on future inputs, is the identity extension of its processed block. Its block
therefore remains unimodular. Restricting the presentation to that block lets
original-minor bounds apply to processed rows even when future matrix rows are
nonzero. This provides the width reset needed between incoming insertions.
-/

namespace Polytime2.IntegerMatrix

/-- A supported prefix basis has the same determinant as its identity extension. -/
theorem processedBasis_det {dimension processed : ℕ} (within : processed ≤ dimension)
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (support : ∀ row : Fin dimension, row.val < processed →
      ∀ column : Fin dimension, processed ≤ column.val → basis row column = 0)
    (future : ∀ row : Fin dimension, processed ≤ row.val → basis row = (1 : Matrix (Fin dimension) (Fin dimension) ℤ) row) :
    basis.det = (basis.submatrix (Fin.castLE within) (Fin.castLE within)).det := by
  have extension : basis = extendDiagonalBasis dimension within
      (basis.submatrix (Fin.castLE within) (Fin.castLE within)) := by
    ext row column
    rw [extendDiagonalBasis_apply]
    by_cases rowActive : row.val < processed
    · rw [dite_eq_left rowActive]
      by_cases columnActive : column.val < processed
      · rw [dite_eq_left columnActive]
        rfl
      · rw [dite_eq_right columnActive]
        exact support row rowActive column (by omega)
    · rw [dite_eq_right rowActive]
      simpa only [Matrix.one_apply, Fin.ext_iff] using congrFun (future row (by omega)) column
  calc
    basis.det = (extendDiagonalBasis dimension within
        (basis.submatrix (Fin.castLE within) (Fin.castLE within))).det := congrArg Matrix.det extension
    _ = _ := extendDiagonalBasis_det dimension within _

/-- Processing the next input preserves basis support and identity rows on the remaining inputs. -/
theorem hermiteInsertRow_processed_basis {dimension processed columns pivots : ℕ}
    (selectedRows : Fin (pivots + 1) ↪ Fin dimension) (pivotColumns : Fin pivots → Fin columns)
    (oldRows : ∀ index : Fin pivots, (selectedRows index.castSucc).val < processed)
    (incoming : (selectedRows (Fin.last pivots)).val = processed)
    (matrix : Matrix (Fin dimension) (Fin columns) ℤ) (left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (support : ∀ row : Fin dimension, row.val < processed →
      ∀ column : Fin dimension, processed ≤ column.val → left row column = 0)
    (future : ∀ row : Fin dimension, processed ≤ row.val → left row = (1 : Matrix (Fin dimension) (Fin dimension) ℤ) row) :
    let result := (hermiteInsertRow selectedRows pivotColumns matrix left).1.2
    (∀ row : Fin dimension, row.val < processed + 1 →
      ∀ column : Fin dimension, processed + 1 ≤ column.val → result row column = 0) ∧
    (∀ row : Fin dimension, processed + 1 ≤ row.val → result row = (1 : Matrix (Fin dimension) (Fin dimension) ℤ) row) := by
  have selectedBound : ∀ index, (selectedRows index).val < processed + 1 := by
    intro index
    cases index using Fin.lastCases
    · rw [incoming]; omega
    · exact Nat.lt_succ_of_lt (oldRows _)
  have expandedSupport : ∀ row : Fin dimension, row.val < processed + 1 →
      ∀ column : Fin dimension, processed + 1 ≤ column.val → left row column = 0 := by
    intro row before column after
    by_cases old : row.val < processed
    · exact support row old column (by omega)
    · have rowValue : row.val = processed := by omega
      rw [congrFun (future row (by omega)) column]
      simp only [Matrix.one_apply, Fin.ext_iff]
      split_ifs with same
      · omega
      · rfl
  constructor
  · intro row before column after
    have unchanged := hermiteInsertRow_left_zero_column selectedRows pivotColumns column matrix left
      (fun index => expandedSupport (selectedRows index) (selectedBound index) column after)
    exact (unchanged row).trans (expandedSupport row before column after)
  · intro row after
    have outside : row ∉ Set.range selectedRows := by
      rintro ⟨index, same⟩
      have before := selectedBound index
      rw [same] at before
      omega
    exact (hermiteInsertRow_rows_other selectedRows pivotColumns row outside matrix left).2.trans
      (future row (by omega))

/-- Previously inactive processed rows remain zero when the incoming row is added to the active set. -/
theorem hermiteInsertRow_processed_support {dimension processed columns pivots : ℕ}
    (selectedRows : Fin (pivots + 1) ↪ Fin dimension) (pivotColumns : Fin pivots → Fin columns)
    (incoming : (selectedRows (Fin.last pivots)).val = processed)
    (matrix : Matrix (Fin dimension) (Fin columns) ℤ) (left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (support : ∀ row : Fin dimension, row.val < processed →
      row ∉ Set.range (Fin.Embedding.init selectedRows) → matrix row = 0) :
    ∀ row : Fin dimension, row.val < processed + 1 → row ∉ Set.range selectedRows →
      (hermiteInsertRow selectedRows pivotColumns matrix left).1.1 row = 0 := by
  intro row before outside
  have notIncoming : row ≠ selectedRows (Fin.last pivots) := fun same => outside ⟨Fin.last pivots, same.symm⟩
  have old : row.val < processed := by
    have notEqual : row.val ≠ processed := fun same => notIncoming (Fin.ext (same.trans incoming.symm))
    omega
  have notActive : row ∉ Set.range (Fin.Embedding.init selectedRows) := by
    rintro ⟨index, same⟩
    exact outside ⟨index.castSucc, same⟩
  exact (hermiteInsertRow_rows_other selectedRows pivotColumns row outside matrix left).1.trans
    (support row old notActive)

/-- If rank does not grow, the enlarged processed prefix is supported on the old active rows. -/
theorem hermiteInsertRow_processed_support_none {dimension processed columns pivots : ℕ}
    (selectedRows : Fin (pivots + 1) ↪ Fin dimension) (pivotColumns : Fin pivots → Fin columns)
    (incoming : (selectedRows (Fin.last pivots)).val = processed)
    (matrix : Matrix (Fin dimension) (Fin columns) ℤ) (left : Matrix (Fin dimension) (Fin dimension) ℤ)
    (support : ∀ row : Fin dimension, row.val < processed →
      row ∉ Set.range (Fin.Embedding.init selectedRows) → matrix row = 0)
    (stopped : (hermiteInsertRow selectedRows pivotColumns matrix left).2 = none) :
    ∀ row : Fin dimension, row.val < processed + 1 → row ∉ Set.range (Fin.Embedding.init selectedRows) →
      (hermiteInsertRow selectedRows pivotColumns matrix left).1.1 row = 0 := by
  intro row before outside
  by_cases same : row = selectedRows (Fin.last pivots)
  · subst row
    exact (hermiteInsertRow_none selectedRows pivotColumns matrix left stopped).2
  · have notSelected : row ∉ Set.range selectedRows := by
      rintro ⟨index, equal⟩
      cases index using Fin.lastCases
      · exact same equal.symm
      · exact outside ⟨_, equal⟩
    exact hermiteInsertRow_processed_support selectedRows pivotColumns incoming matrix left support row before notSelected

/-- Original-width row bounds apply to a processed prefix while future rows remain untouched. -/
theorem normalized_processed_rows_bound {dimension processed rank : ℕ} {Column : Type}
    (width : ℕ) (within : processed ≤ dimension) (activeRows : Fin rank ↪ Fin processed)
    (pivotColumns : Fin rank ↪ Column) (original current : Matrix (Fin dimension) Column ℤ)
    (left : Matrix (Fin dimension) (Fin dimension) ℤ) (equation : left * original = current) (unit : IsUnit left.det)
    (basisSupport : ∀ row : Fin dimension, row.val < processed →
      ∀ column : Fin dimension, processed ≤ column.val → left row column = 0)
    (future : ∀ row : Fin dimension, processed ≤ row.val → left row = (1 : Matrix (Fin dimension) (Fin dimension) ℤ) row)
    (support : ∀ row : Fin processed, row ∉ Set.range activeRows →
      ∀ column, current (Fin.castLE within row) column = 0)
    (upper : (current.submatrix (fun index => Fin.castLE within (activeRows index)) pivotColumns).IsUpperTriangular)
    (positive : ∀ index, 0 < current (Fin.castLE within (activeRows index)) (pivotColumns index))
    (reduced : ∀ row column : Fin rank, row < column →
      0 ≤ current (Fin.castLE within (activeRows row)) (pivotColumns column) ∧
        current (Fin.castLE within (activeRows row)) (pivotColumns column) <
          current (Fin.castLE within (activeRows column)) (pivotColumns column))
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ (row : Fin processed) column, (current (Fin.castLE within row) column).natAbs <
      2 ^ (2 * (rank * (width + rank) + 1) + width + 2 * rank + 2) := by
  let selected := Fin.castLEEmb within
  have restricted := supported_minor_factorization_of_left selected selected (id : Column → Column)
    current original left equation.symm (by
      intro row other outside
      apply basisSupport (selected row) row.isLt other
      by_contra before
      have otherLt : other.val < processed := by omega
      exact outside ⟨⟨other.val, otherLt⟩, Fin.ext rfl⟩)
  have restrictedUnit : IsUnit (left.submatrix (Fin.castLE within) (Fin.castLE within)).det := by
    rw [← processedBasis_det within left basisSupport future]
    exact unit
  exact normalized_supported_rows_bound width activeRows pivotColumns
    (original.submatrix selected id) (current.submatrix selected id) (left.submatrix selected selected)
    restricted.symm restrictedUnit support upper positive reduced
    (fun row column => entryBound (selected row) column)

end Polytime2.IntegerMatrix
