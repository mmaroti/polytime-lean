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

import Polytime2.Matrices.HermiteStageMath
import Polytime2.Matrices.HermiteBlockBoundsMath
import Polytime2.Matrices.HermiteExtendMath
import Polytime2.Matrices.HermiteRowBoundsMath

/-! # Interleaved Hermite elimination and remainder normalization

An incoming negative entry changes the pivot from six to two. The earlier
entry eleven is then reduced to one. The first column remains unchanged,
while the earlier row's trailing entry and the accumulated basis both change.
-/

namespace Polytime2.Examples.HermiteStage

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 3) (Fin 3) ℤ := !![2, 11, 5; 0, 6, 1; 0, -14, 4]

example : hermiteRowStage 1 2 1 [0] matrix 1 =
    (!![2, 1, -60; 0, 2, 13; 0, 0, 19], !![1, -25, -10; 0, 5, 2; 0, 7, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : ∀ row, (hermiteRowStage 1 2 1 [0] matrix 1).1 row 0 = matrix row 0 :=
  hermiteRowStage_zero_column 1 2 1 0 [0] (by decide) (by decide) matrix 1 rfl rfl

example :
    (∀ row column, ((hermiteRowStage 1 2 1 [0] matrix 1).1 row column).natAbs < 2 ^ 19) ∧
    (∀ row column, ((hermiteRowStage 1 2 1 [0] matrix 1).2 row column).natAbs < 2 ^ 16) := by
  exact hermiteRowStage_bound 4 4 1 1 2 (by decide) 1 [0] (by decide) (by decide) matrix 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem presentation : (hermiteRowStage 1 2 1 [0] matrix 1).2 * matrix = (hermiteRowStage 1 2 1 [0] matrix 1).1 ∧
    IsUnit (hermiteRowStage 1 2 1 [0] matrix 1).2.det := by
  simpa only [Matrix.mul_one] using
    hermiteRowStage_preserves 1 2 (by decide) 1 [0] (by decide) matrix matrix 1 1 (by simp) (by simp)

private def selected : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)
private theorem supported : ∀ row ∉ Set.range selected, ∀ column,
    (hermiteRowStage 1 2 1 [0] matrix 1).1 row (selected column) = 0 := by
  intro row outside column
  fin_cases row
  · exact False.elim (outside ⟨0, rfl⟩)
  · exact False.elim (outside ⟨1, rfl⟩)
  · fin_cases column <;> decide +kernel

/-- The reduced leading determinant divides the fixed input minor, without a growth recurrence. -/
example : ((hermiteRowStage 1 2 1 [0] matrix 1).1.submatrix selected selected).det ∣
    (matrix.submatrix selected selected).det :=
  unimodular_supported_minor_dvd selected selected selected matrix _ _ presentation.1 presentation.2 supported

example : ((hermiteRowStage 1 2 1 [0] matrix 1).1.submatrix selected selected).det.natAbs < 2 ^ 13 := by
  exact unimodular_supported_minor_bound 4 selected selected matrix _ _ presentation.1 presentation.2 supported
    (by decide +kernel)

/-- All entries of the completed pivot block have an original-input bound. -/
example : ∀ row column : Fin 2,
    ((hermiteRowStage 1 2 1 [0] matrix 1).1 (selected row) (selected column)).natAbs < 2 ^ 13 := by
  apply normalized_supported_block_bound 4 selected selected matrix _ _ presentation.1 presentation.2 supported
  · intro row column below
    fin_cases row <;> fin_cases column <;> norm_num at below
    decide +kernel
  · decide +kernel
  · intro row column before
    fin_cases row <;> fin_cases column <;> norm_num at before
    decide +kernel
  · decide +kernel

example (width : ℕ) (empty : Matrix (Fin 0) (Fin 0) ℤ) : empty.det.natAbs < 2 ^ 1 := by
  simpa only [zero_mul, zero_add] using determinant_bound width 0 empty (by intro row; exact row.elim0)

/-- Large earlier rows do not enlarge the selected pair's elimination coefficients. -/
example :
    let input : Matrix (Fin 3) (Fin 3) ℤ := !![2, 10000, 10000; 0, 6, 1; 0, -14, 4]
    let result := hermiteRowStage 1 2 1 [0] input 1
    (∀ row column, (result.1 row column).natAbs < 2 ^ 29) ∧
      (∀ row column, (result.2 row column).natAbs < 2 ^ 26) := by
  exact hermiteRowStage_bound_of_small_pair 4 4 14 1 1 2 (by decide) 1 [0]
    (by decide) (by decide) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def extendedResult :=
  let eliminated := hermiteRowStage 1 2 1 [0] matrix 1
  rowRemainderSweep 2 2 ((List.finRange 2).map selected) eliminated.1 eliminated.2

/-- The residual nineteen becomes a new pivot, reducing minus sixty to sixteen. -/
private theorem extendedNormalized :
    extendedResult.1.IsUpperTriangular ∧ (∀ index, 0 < extendedResult.1 index index) ∧
      ∀ row column : Fin 3, row < column →
        0 ≤ extendedResult.1 row column ∧ extendedResult.1 row column < extendedResult.1 column column := by
  have extended : (Fin.snoc selected (2 : Fin 3) : Fin 3 → Fin 3) = id := by decide +kernel
  have normalized := rowRemainderSweep_extend_normalized selected selected 2 2
    (by decide +kernel) (hermiteRowStage 1 2 1 [0] matrix 1).1
    (hermiteRowStage 1 2 1 [0] matrix 1).2 (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [extendedResult, extended, Matrix.submatrix_id_id, id_eq] using normalized

example : extendedResult =
    (!![2, 1, 16; 0, 2, 13; 0, 0, 19], !![1, 3, 2; 0, 5, 2; 0, 7, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

private theorem extendedPresentation : extendedResult.2 * matrix = extendedResult.1 ∧
    IsUnit extendedResult.2.det := by
  have preserved := rowRemainderSweep_preserves 2 2 ((List.finRange 2).map selected) (by decide +kernel)
    (hermiteRowStage 1 2 1 [0] matrix 1).1 matrix (hermiteRowStage 1 2 1 [0] matrix 1).2 1
    (by simpa only [Matrix.mul_one] using presentation.1) presentation.2
  simpa only [extendedResult, Matrix.mul_one] using preserved

/-- After rank growth, the full normalized row bound resets to the original entry width. -/
example : ∀ row column, (extendedResult.1 row column).natAbs < 2 ^ 56 := by
  exact normalized_supported_rows_bound 4 (Function.Embedding.refl (Fin 3)) (Function.Embedding.refl (Fin 3))
    matrix extendedResult.1 extendedResult.2 extendedPresentation.1 extendedPresentation.2
    (by intro row outside; exact False.elim (outside ⟨row, rfl⟩))
    extendedNormalized.1 extendedNormalized.2.1 extendedNormalized.2.2 (by decide +kernel)

end Polytime2.Examples.HermiteStage
