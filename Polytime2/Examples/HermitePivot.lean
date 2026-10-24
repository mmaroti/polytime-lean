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

import Polytime2.Matrices.HermitePivotMath

/-! # Sign-aware rank growth

A negative residual pivot is made positive before normalizing the old rows.
The returned basis is checked explicitly, including a first pivot with no old
active rows.
-/

namespace Polytime2.Examples.HermitePivot

open Polytime2.IntegerMatrix

private def activeRows : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)
private def matrix : Matrix (Fin 3) (Fin 3) ℤ := !![2, 1, -60; 0, 2, 13; 0, 0, -19]
private def result := hermiteExtendPivot activeRows 2 2 matrix 1

example : result =
    (!![2, 1, 16; 0, 2, 13; 0, 0, 19], !![1, 0, -4; 0, 1, 0; 0, 0, -1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : result.2 * matrix = result.1 ∧ IsUnit result.2.det := by
  simpa only [result, Matrix.mul_one] using hermiteExtendPivot_preserves activeRows 2 2 (by decide +kernel)
    matrix matrix 1 1 (by simp) (by simp)

example :
    (∀ row column, (result.1 row column).natAbs < 2 ^ 13) ∧
      (∀ row column, (result.2 row column).natAbs < 2 ^ 8) := by
  exact hermiteExtendPivot_bound 6 1 activeRows 2 2 (by decide +kernel) matrix 1
    (by decide +kernel) (by decide +kernel)

example : result.1.IsUpperTriangular ∧ (∀ index, 0 < result.1 index index) ∧
    ∀ row column : Fin 3, row < column →
      0 ≤ result.1 row column ∧ result.1 row column < result.1 column column := by
  have extended : (Fin.snoc activeRows (2 : Fin 3) : Fin 3 → Fin 3) = id := by decide +kernel
  have normalized := hermiteExtendPivot_normalized activeRows activeRows 2 2 (by decide +kernel) matrix 1
    (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel) (hermiteResidualPivot_nonzero 2 matrix 2 (by decide +kernel))
  simpa only [result, extended, Matrix.submatrix_id_id, id_eq] using normalized

private def noRows : Fin 0 ↪ Fin 1 := ⟨Fin.elim0, by intro index; exact index.elim0⟩

example : hermiteExtendPivot noRows 0 0 (!![-5] : Matrix (Fin 1) (Fin 1) ℤ) 1 =
    (!![5], !![-1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

/-- Sign normalization does not need an existing pivot or a second row. -/
example :
    let columns : Fin 0 → Fin 1 := Fin.elim0
    let result := (hermiteExtendPivot noRows 0 0 (!![-5] : Matrix (Fin 1) (Fin 1) ℤ) 1).1
    let rows := Fin.snoc (α := fun _ => Fin 1) noRows 0
    let extendedColumns := Fin.snoc (α := fun _ => Fin 1) columns 0
    (result.submatrix rows extendedColumns).IsUpperTriangular ∧
      (∀ index, 0 < result (rows index) (extendedColumns index)) ∧
      (∀ row column : Fin 1, row < column →
        0 ≤ result (rows row) (extendedColumns column) ∧
          result (rows row) (extendedColumns column) < result (rows column) (extendedColumns column)) := by
  exact hermiteExtendPivot_normalized noRows Fin.elim0 0 0 (by decide +kernel) _ _
    (by intro row; exact row.elim0) (by intro index; exact index.elim0)
    (by intro row; exact row.elim0) (by intro index; exact index.elim0) (by decide +kernel)

example : hermiteResidualPivot 2 matrix = some 2 := by decide +kernel

/-- The selected residual coordinate is new relative to the old pivot columns. -/
example : (2 : Fin 3) ∉ Set.range activeRows :=
  hermiteResidualPivot_not_pivot 2 matrix activeRows (by decide +kernel) 2 (by decide +kernel)

example : hermiteResidualPivot 0 (0 : Matrix (Fin 1) (Fin 3) ℤ) = none :=
  (hermiteResidualPivot_none _ _).mpr rfl

example : hermiteResidualPivot 0 (0 : Matrix (Fin 1) (Fin 0) ℤ) = none :=
  (hermiteResidualPivot_none _ _).mpr rfl

end Polytime2.Examples.HermitePivot
