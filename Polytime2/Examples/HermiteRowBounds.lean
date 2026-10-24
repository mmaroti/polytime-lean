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

import Polytime2.Matrices.HermiteRowBoundsMath

/-! # Original-input bounds for trailing Hermite columns

The input has a dependent third row. Its compact normalized row form has two
pivot columns and two trailing columns. A nontrivial unimodular left basis
certifies that form, whose entire rectangular storage is bounded from the
original four-bit entries. A rank-zero case checks the empty pivot block.
-/

namespace Polytime2.Examples.HermiteRowBounds

open Polytime2.IntegerMatrix

private def original : Matrix (Fin 3) (Fin 4) ℤ := !![6, 1, 4, 3; -14, 5, 7, -2; -8, 6, 11, 1]
private def current : Matrix (Fin 3) (Fin 4) ℤ := !![2, 15, 34, 11; 0, 22, 49, 15; 0, 0, 0, 0]
private def left : Matrix (Fin 3) (Fin 3) ℤ := !![5, 2, 0; 7, 3, 0; -1, -1, 1]
private def rows : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by decide)
private def columns : Fin 2 ↪ Fin 4 := Fin.castLEEmb (by decide)

example : ∀ row column, (current row column).natAbs < 2 ^ 36 := by
  apply normalized_supported_rows_bound 4 rows columns original current left
  · ext row column
    fin_cases row <;> fin_cases column <;> decide +kernel
  · decide +kernel
  · intro row outside column
    fin_cases row
    · exact False.elim (outside ⟨0, rfl⟩)
    · exact False.elim (outside ⟨1, rfl⟩)
    · fin_cases column <;> rfl
  · intro row column below
    fin_cases row <;> fin_cases column <;> norm_num at below
    decide +kernel
  · decide +kernel
  · intro row column before
    fin_cases row <;> fin_cases column <;> norm_num at before
    decide +kernel
  · decide +kernel

private def noRows : Fin 0 ↪ Fin 3 := ⟨Fin.elim0, by intro row; exact row.elim0⟩
private def noColumns : Fin 0 ↪ Fin 4 := ⟨Fin.elim0, by intro column; exact column.elim0⟩

example : ∀ row column, ((0 : Matrix (Fin 3) (Fin 4) ℤ) row column).natAbs < 2 ^ 4 := by
  exact normalized_supported_rows_bound 0 noRows noColumns 0 0 1 (by simp) (by simp)
    (by intros; rfl) (by intro row; exact row.elim0) (by intro row; exact row.elim0)
    (by intro row; exact row.elim0) (by intros; norm_num)

end Polytime2.Examples.HermiteRowBounds
