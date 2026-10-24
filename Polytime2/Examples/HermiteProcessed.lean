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

import Polytime2.Matrices.HermiteProcessedMath

/-! # Original-input bounds before the final input row

Insert the third row of a four-row matrix. The future fourth row is nonzero.
Basis support and untouched future basis rows let the processed block retain
unimodularity and derive its entry bound in the original input width.
-/

namespace Polytime2.Examples.HermiteProcessed

open Polytime2.IntegerMatrix

private def selected : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by decide)
private def columns : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)
private def original : Matrix (Fin 4) (Fin 3) ℤ := !![2, 11, 5; 0, 6, 1; 0, -14, 4; 9, 8, 7]
private def inserted := hermiteInsertRow selected columns original 1

private theorem basisInvariant :
    (∀ row : Fin 4, row.val < 3 → ∀ column : Fin 4, 3 ≤ column.val → inserted.1.2 row column = 0) ∧
    (∀ row : Fin 4, 3 ≤ row.val → inserted.1.2 row = (1 : Matrix (Fin 4) (Fin 4) ℤ) row) := by
  exact hermiteInsertRow_processed_basis (processed := 2) selected columns (by decide +kernel) rfl original 1
    (by
      intro row before column after
      simp only [Matrix.one_apply, Fin.ext_iff]
      split_ifs with same
      · omega
      · rfl) (by intro row after; rfl)

example : IsUnit (inserted.1.2.submatrix selected selected).det := by
  have unit := (hermiteInsertRow_preserves selected columns original original 1 1 (by simp) (by simp)).2
  change IsUnit (inserted.1.2.submatrix (Fin.castLE (by decide : 3 ≤ 4)) (Fin.castLE (by decide : 3 ≤ 4))).det
  rw [← processedBasis_det (by decide : 3 ≤ 4) inserted.1.2 basisInvariant.1 basisInvariant.2]
  simpa only [inserted] using unit

/-- The nonzero future row does not enter the bound for the normalized processed block. -/
example : ∀ (row : Fin 3) column, (inserted.1.1 (selected row) column).natAbs < 2 ^ 56 := by
  have presentation := (hermiteInsertRow_preserves selected columns original original 1 1 (by simp) (by simp))
  exact normalized_processed_rows_bound 4 (by decide : 3 ≤ 4)
    (Function.Embedding.refl (Fin 3)) (Function.Embedding.refl (Fin 3)) original inserted.1.1 inserted.1.2
    (by simpa only [inserted, Matrix.mul_one] using presentation.1) presentation.2 basisInvariant.1 basisInvariant.2
    (by intro row outside; exact False.elim (outside ⟨row, rfl⟩)) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      all_goals decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : inserted.1.1 3 = original 3 :=
  (hermiteInsertRow_rows_other selected columns 3 (by decide +kernel) original 1).1

private def supportRows : Fin 2 ↪ Fin 4 := ⟨![0, 2], by decide +kernel⟩

private theorem oldInactiveSupport (first second : ℤ) :
    ∀ row : Fin 4, row.val < 2 → row ∉ Set.range (Fin.Embedding.init supportRows) →
      (!![2, 3; 0, 0; first, second; 7, 9] : Matrix (Fin 4) (Fin 2) ℤ) row = 0 := by
  intro row before outside
  fin_cases row <;> norm_num at before
  · exact False.elim (outside ⟨0, rfl⟩)
  · funext column; fin_cases column <;> rfl

/-- A dependent incoming row leaves both old inactive and new dependent rows zero. -/
example :
    let selectedRows := supportRows
    let oldColumns : Fin 1 → Fin 2 := ![0]
    let matrix : Matrix (Fin 4) (Fin 2) ℤ := !![2, 3; 0, 0; -4, -6; 7, 9]
    let inserted := hermiteInsertRow selectedRows oldColumns matrix 1
    ∀ row : Fin 4, row.val < 3 → row ∉ Set.range (Fin.Embedding.init selectedRows) → inserted.1.1 row = 0 := by
  dsimp only
  apply hermiteInsertRow_processed_support_none (processed := 2)
  · rfl
  · exact oldInactiveSupport (-4) (-6)
  · decide +kernel

/-- Rank growth preserves the zero rows already outside the active set. -/
example :
    let selectedRows := supportRows
    let oldColumns : Fin 1 → Fin 2 := ![0]
    let matrix : Matrix (Fin 4) (Fin 2) ℤ := !![2, 3; 0, 0; -4, -5; 7, 9]
    let inserted := hermiteInsertRow selectedRows oldColumns matrix 1
    inserted.2 = some 1 ∧
      ∀ row : Fin 4, row.val < 3 → row ∉ Set.range selectedRows → inserted.1.1 row = 0 := by
  dsimp only
  constructor
  · decide +kernel
  · apply hermiteInsertRow_processed_support (processed := 2)
    · rfl
    · exact oldInactiveSupport (-4) (-5)

end Polytime2.Examples.HermiteProcessed
