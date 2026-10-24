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

import Polytime2.Matrices.EuclideanSweepMath
import Mathlib.Data.Fin.Tuple.Basic

/-! # Extending a normalized Hermite pivot block

Given normalized old pivots and an incoming row that vanishes in their columns,
a positive entry of the incoming row can become the next pivot. Reducing all
old pivot rows modulo that entry leaves every old pivot column unchanged and
makes the extended block positive, upper triangular, and column reduced.
This is the rank-growth normalization step; selecting and making the residual
entry positive are separate operations.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] {rank : ℕ}

/-- A positive residual pivot extends the normalized block without altering old columns. -/
theorem rowRemainderSweep_extend_normalized (activeRows : Fin rank ↪ Row)
    (pivotColumns : Fin rank → Column) (source : Row) (column : Column)
    (excluded : source ∉ Set.range activeRows)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (upper : (matrix.submatrix activeRows pivotColumns).IsUpperTriangular)
    (positive : ∀ index, 0 < matrix (activeRows index) (pivotColumns index))
    (reduced : ∀ row other : Fin rank, row < other →
      0 ≤ matrix (activeRows row) (pivotColumns other) ∧
        matrix (activeRows row) (pivotColumns other) < matrix (activeRows other) (pivotColumns other))
    (sourceZero : ∀ index, matrix source (pivotColumns index) = 0)
    (sourcePositive : 0 < matrix source column) :
    let result := (rowRemainderSweep source column ((List.finRange rank).map activeRows) matrix left).1
    let rows := Fin.snoc (α := fun _ => Row) activeRows source
    let columns := Fin.snoc (α := fun _ => Column) pivotColumns column
    (result.submatrix rows columns).IsUpperTriangular ∧
      (∀ index, 0 < result (rows index) (columns index)) ∧
      (∀ row other : Fin (rank + 1), row < other →
        0 ≤ result (rows row) (columns other) ∧
          result (rows row) (columns other) < result (rows other) (columns other)) := by
  let targets := (List.finRange rank).map activeRows
  have distinct : targets.Nodup := (List.nodup_finRange rank).map activeRows.injective
  have sourceExcluded : source ∉ targets := by
    intro member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    exact excluded ⟨index, same⟩
  let result := (rowRemainderSweep source column targets matrix left).1
  have unchanged (index : Fin rank) (row : Row) : result row (pivotColumns index) = matrix row (pivotColumns index) :=
    rowRemainderSweep_zero_column source column _ targets distinct sourceExcluded matrix left (sourceZero index) row
  have sourceSame (other : Column) : result source other = matrix source other := by
    have formula := (rowRemainderSweep_apply source column targets distinct sourceExcluded matrix left).1 source other
    simpa only [ite_eq_right sourceExcluded] using formula
  have ranges (index : Fin rank) : 0 ≤ result (activeRows index) column ∧
      result (activeRows index) column < matrix source column :=
    rowRemainderSweep_range source column targets distinct sourceExcluded matrix left sourcePositive _
      (List.mem_map.mpr ⟨index, by simp, rfl⟩)
  change (result.submatrix (Fin.snoc (α := fun _ => Row) activeRows source) (Fin.snoc (α := fun _ => Column) pivotColumns column)).IsUpperTriangular ∧
    (∀ index, 0 < result (Fin.snoc (α := fun _ => Row) activeRows source index) (Fin.snoc (α := fun _ => Column) pivotColumns column index)) ∧
    (∀ row other : Fin (rank + 1), row < other →
      0 ≤ result (Fin.snoc (α := fun _ => Row) activeRows source row) (Fin.snoc (α := fun _ => Column) pivotColumns column other) ∧
      result (Fin.snoc (α := fun _ => Row) activeRows source row) (Fin.snoc (α := fun _ => Column) pivotColumns column other) <
        result (Fin.snoc (α := fun _ => Row) activeRows source other) (Fin.snoc (α := fun _ => Column) pivotColumns column other))
  refine ⟨?_, ?_, ?_⟩
  · intro row other below
    cases row using Fin.lastCases <;> cases other using Fin.lastCases
    · exact False.elim (lt_irrefl _ below)
    · simpa only [Matrix.submatrix_apply, Fin.snoc_last, Fin.snoc_castSucc, unchanged] using sourceZero _
    · simp only [Fin.lt_def, id_eq, Fin.val_last, Fin.val_castSucc] at below
      omega
    · simpa only [Matrix.submatrix_apply, Fin.snoc_castSucc, unchanged] using upper below
  · intro index
    cases index using Fin.lastCases
    · simpa only [Fin.snoc_last, sourceSame] using sourcePositive
    · simpa only [Fin.snoc_castSucc, unchanged] using positive _
  · intro row other below
    cases row using Fin.lastCases <;> cases other using Fin.lastCases
    · exact False.elim (lt_irrefl _ below)
    · simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at below
      omega
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, sourceSame] using ranges _
    · simpa only [Fin.snoc_castSucc, unchanged] using reduced _ _ below

end Polytime2.IntegerMatrix
