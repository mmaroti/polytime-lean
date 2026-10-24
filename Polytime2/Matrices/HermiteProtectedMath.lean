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

import Polytime2.Matrices.HermiteColumnTraversalMath

/-! # Preserving completed blocks during integer column reduction

Choose protected rows and columns. The source lies outside the protected rows;
protected rows have zero in the new pivot column, and unprotected rows have
zero in protected columns. Every column-reduction prefix preserves protected
rows in both the matrix and left basis, and preserves all protected matrix
columns. This applies to a completed diagonal block without rank assumptions.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column]

/-- One Hermite step preserves a separated earlier block. -/
theorem hermiteRowStep_protected (protectedRows : Set Row) (protectedColumns : Set Column)
    (source target : Row) (column : Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceOutside : source ∉ protectedRows)
    (selectedZeros : ∀ row ∈ protectedRows, matrix row column = 0)
    (earlierZeros : ∀ row ∉ protectedRows, ∀ other ∈ protectedColumns, matrix row other = 0) :
    (∀ row ∈ protectedRows, (hermiteRowStep source target column matrix left).1 row = matrix row ∧
      (hermiteRowStep source target column matrix left).2 row = left row) ∧
    (∀ other ∈ protectedColumns, ∀ row, (hermiteRowStep source target column matrix left).1 row other = matrix row other) := by
  by_cases targetInside : target ∈ protectedRows
  · rw [hermiteRowStep_zero_target source target column matrix left (selectedZeros target targetInside)]
    simp
  · constructor
    · intro row inside
      have notSource : row ≠ source := fun equal => sourceOutside (equal ▸ inside)
      have notTarget : row ≠ target := fun equal => targetInside (equal ▸ inside)
      exact hermiteRowStep_rows_other source target row notSource notTarget column matrix left
    · intro other inside row
      exact hermiteRowStep_zero_column source target column other matrix left
        (earlierZeros source sourceOutside other inside) (earlierZeros target targetInside other inside) row

/-- Any sequence of target rows preserves the separated block and its left-basis rows. -/
theorem hermiteColumnSweep_protected (protectedRows : Set Row) (protectedColumns : Set Column)
    (source : Row) (column : Column) (targets : List Row) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (sourceOutside : source ∉ protectedRows)
    (selectedZeros : ∀ row ∈ protectedRows, matrix row column = 0)
    (earlierZeros : ∀ row ∉ protectedRows, ∀ other ∈ protectedColumns, matrix row other = 0) :
    (∀ row ∈ protectedRows, (hermiteColumnSweep source column targets matrix left).1 row = matrix row ∧
      (hermiteColumnSweep source column targets matrix left).2 row = left row) ∧
    (∀ other ∈ protectedColumns, ∀ row, (hermiteColumnSweep source column targets matrix left).1 row other = matrix row other) := by
  induction targets with
  | nil => exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  | cons target targets induction =>
    have step := hermiteRowStep_protected protectedRows protectedColumns source target column
      (hermiteColumnSweep source column targets matrix left).1 (hermiteColumnSweep source column targets matrix left).2
      sourceOutside (fun row inside => (congrFun (induction.1 row inside).1 column).trans (selectedZeros row inside))
      (fun row outside other inside => (induction.2 other inside row).trans (earlierZeros row outside other inside))
    constructor
    · intro row inside
      exact ⟨(step.1 row inside).1.trans (induction.1 row inside).1,
        (step.1 row inside).2.trans (induction.1 row inside).2⟩
    · intro other inside row
      exact (step.2 other inside row).trans (induction.2 other inside row)

end Polytime2.IntegerMatrix
