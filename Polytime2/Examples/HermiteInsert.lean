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

/-! # Complete mathematical incoming-row insertion

The independent example clears a negative incoming entry, discovers a new pivot,
and reduces the old rows. The dependent example returns no new pivot and a zero
residual row. Both retain actual accumulated bases.
-/

namespace Polytime2.Examples.HermiteInsert

open Polytime2.IntegerMatrix

private def rows : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
private def columns : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)
private def independent : Matrix (Fin 3) (Fin 3) ℤ := !![2, 11, 5; 0, 6, 1; 0, -14, 4]
private def result := hermiteInsertRow rows columns independent 1

private theorem positive : ∀ index, 0 < independent (rows index.castSucc) (columns index) := by decide +kernel
private theorem upper : ∀ row column : Fin 2, column < row →
    independent (rows row.castSucc) (columns column) = 0 := by
  intro row column below
  fin_cases row <;> fin_cases column <;> norm_num at below
  decide +kernel

example : result =
    ((!![2, 1, 16; 0, 2, 13; 0, 0, 19], !![1, 3, 2; 0, 5, 2; 0, 7, 3]), some 2) := by
  apply Prod.ext
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel
  · decide +kernel

example : result.1.2 * independent = result.1.1 ∧ IsUnit result.1.2.det := by
  simpa only [result, Matrix.mul_one] using hermiteInsertRow_preserves rows columns independent independent 1 1
    (by simp) (by simp)

/-- The discovered pivot is new and the resulting full block is normalized. -/
example : (2 : Fin 3) ∉ Set.range columns ∧
    let extendedColumns := Fin.snoc (α := fun _ => Fin 3) columns 2
    (result.1.1.submatrix rows extendedColumns).IsUpperTriangular ∧
      (∀ index, 0 < result.1.1 (rows index) (extendedColumns index)) ∧
      (∀ row other : Fin 3, row < other →
        0 ≤ result.1.1 (rows row) (extendedColumns other) ∧
          result.1.1 (rows row) (extendedColumns other) < result.1.1 (rows other) (extendedColumns other)) := by
  exact hermiteInsertRow_normalized_some rows columns independent 1 positive upper 2 (by decide +kernel)

set_option exponentiation.threshold 1024 in
example :
    (∀ row column, (result.1.1 row column).natAbs < 2 ^ 285) ∧
      (∀ row column, (result.1.2 row column).natAbs < 2 ^ 522) := by
  have bounded := hermiteInsertRow_bound 4 1 rows columns independent 1 positive upper
    (by decide +kernel) (by decide +kernel)
  simpa only [result] using bounded

private def dependent : Matrix (Fin 3) (Fin 3) ℤ := !![6, 1, 4; 0, 2, 3; -12, 0, -5]
private def dependentResult := hermiteInsertRow rows columns dependent 1

example : dependentResult =
    ((!![6, 1, 4; 0, 2, 3; 0, 0, 0], !![1, 0, 0; 0, 1, 0; 2, -1, 1]), none) := by
  apply Prod.ext
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel
  · decide +kernel

example : dependentResult.1.1 (2 : Fin 3) = 0 :=
  (hermiteInsertRow_none rows columns dependent 1 (by decide +kernel)).2

example : dependentResult.1.2 * dependent = dependentResult.1.1 ∧ IsUnit dependentResult.1.2.det := by
  simpa only [dependentResult, Matrix.mul_one] using hermiteInsertRow_preserves rows columns dependent dependent 1 1
    (by simp) (by simp)

example :
    let selected : Fin 1 ↪ Fin 1 := Function.Embedding.refl _
    let oldColumns : Fin 0 → Fin 0 := Fin.elim0
    hermiteInsertRow selected oldColumns (0 : Matrix (Fin 1) (Fin 0) ℤ) 1 = ((0, 1), none) := by
  decide +kernel

example : (dependentResult.1.1.submatrix (fun index : Fin 2 => rows index.castSucc) columns).IsUpperTriangular := by
  exact (hermiteInsertRow_normalized_none rows columns dependent 1 (by decide +kernel) (by
    intro row column below
    fin_cases row <;> fin_cases column <;> norm_num at below
    decide +kernel) (by decide +kernel)).1

/-- Unselected future or inactive rows retain their original matrix and basis values. -/
example (matrix : Matrix (Fin 4) (Fin 3) ℤ) (basis : Matrix (Fin 4) (Fin 4) ℤ) :
    let selectedRows : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide +kernel⟩
    let inserted := hermiteInsertRow selectedRows columns matrix basis
    inserted.1.1 2 = matrix 2 ∧ inserted.1.2 2 = basis 2 := by
  exact hermiteInsertRow_rows_other _ columns 2 (by decide +kernel) matrix basis

/-- No basis coefficient from an unprocessed fourth coordinate enters the selected rows. -/
example (matrix : Matrix (Fin 4) (Fin 3) ℤ) :
    let selectedRows : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide +kernel⟩
    let basis : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 7, 0; 0, 0, 0, 1]
    let inserted := hermiteInsertRow selectedRows columns matrix basis
    ∀ row, inserted.1.2 row 2 = basis row 2 := by
  exact hermiteInsertRow_left_zero_column _ columns 2 matrix _ (by decide +kernel)

/-- The accumulated equation restricts to processed inputs even when future input rows are nonzero. -/
example (matrix : Matrix (Fin 4) (Fin 3) ℤ) :
    let selectedRows : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide +kernel⟩
    let inserted := hermiteInsertRow selectedRows columns matrix 1
    inserted.1.1.submatrix selectedRows id =
      inserted.1.2.submatrix selectedRows selectedRows * matrix.submatrix selectedRows id := by
  let selectedRows : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide +kernel⟩
  let inserted := hermiteInsertRow selectedRows columns matrix 1
  have presentation := hermiteInsertRow_preserves selectedRows columns matrix matrix 1 1 (by simp) (by simp)
  apply supported_minor_factorization_of_left selectedRows selectedRows id inserted.1.1 matrix inserted.1.2
    (by simpa only [Matrix.mul_one] using presentation.1.symm)
  intro index other outside
  have otherEq : other = 2 := by
    have only : ∀ other : Fin 4, other ∉ Set.range selectedRows → other = 2 := by decide +kernel
    exact only other outside
  subst other
  have unchanged := hermiteInsertRow_left_zero_column selectedRows columns 2 matrix 1 (by decide +kernel)
  have zero : ∀ index : Fin 3, (1 : Matrix (Fin 4) (Fin 4) ℤ) (selectedRows index) 2 = 0 := by decide +kernel
  exact (unchanged (selectedRows index)).trans (zero index)

end Polytime2.Examples.HermiteInsert
