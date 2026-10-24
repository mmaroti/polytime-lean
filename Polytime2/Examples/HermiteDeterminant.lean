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

import Polytime2.Matrices.HermiteDeterminantMath

/-! # One fixed active determinant across alternating passes

A rectangular rank-two input has a normalized lower active block. A genuine gcd
change transfers a factor of three between its diagonal entries. Row and column
passes retain active determinant magnitude 24 and all returned entries are at
most 24, including the inactive strips.
-/

namespace Polytime2.Examples.HermiteDeterminant

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 3) (Fin 4) ℤ := !![6, 0, 0, 0; 2, 4, 0, 0; 0, 0, 0, 0]
private theorem rowBound : 2 ≤ 3 := by decide
private theorem columnBound : 2 ≤ 4 := by decide
private def rowResult := compactHermiteRows matrix
private def columnResult := compactHermiteColumns rowResult.2.1

private theorem normalizedInput : IsCompactRowHermite 2 matrix.transpose := by
  refine ⟨columnBound, rowBound, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · intro row after
    fin_cases row <;> norm_num at after
    all_goals funext column; fin_cases column <;> rfl
  · intro row column below
    fin_cases row <;> fin_cases column <;> norm_num at below
    decide +kernel

private theorem zeroRows : ∀ row : Fin 3, 2 ≤ row.val → matrix row = 0 := by
  intro row after
  fin_cases row <;> norm_num at after
  funext column; fin_cases column <;> rfl

private theorem normalizedRow : IsCompactRowHermite 2 rowResult.2.1 := by
  have shape := (compactHermiteRows_correct matrix).2.2.2
  have sameRank : (compactHermiteRows matrix).1 = 2 := by
    rw [compactHermiteRows_rank]
    simpa only [Matrix.transpose_transpose] using normalizedInput.transpose_rank_eq
  rw [sameRank] at shape
  exact shape

private theorem rowDet : (rowResult.2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs = 24 := by
  calc
    _ = (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs :=
      compactHermiteRows_det_natAbs rowBound columnBound matrix normalizedInput zeroRows
    _ = 24 := by decide +kernel

example : rowResult.2.1 = !![2, 4, 0, 0; 0, 12, 0, 0; 0, 0, 0, 0] := by
  ext row column; fin_cases row <;> fin_cases column <;> decide +kernel

example : columnResult.2.1 = !![2, 0, 0, 0; 0, 12, 0, 0; 0, 0, 0, 0] := by
  ext row column; fin_cases row <;> fin_cases column <;> decide +kernel

example : (columnResult.2.1.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs = 24 := by
  exact (compactHermiteColumns_det_natAbs rowBound columnBound rowResult.2.1 normalizedRow
    (compactHermiteRows_zero_columns matrix normalizedInput)).trans rowDet

example : ∀ row column, (rowResult.2.1 row column).natAbs ≤ 24 := by
  have bounded := compactHermiteRows_entry_le_det rowBound columnBound matrix normalizedInput zeroRows
  have determinant : (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det.natAbs = 24 := by decide +kernel
  simpa only [rowResult, determinant] using bounded

example : ∀ row column, (columnResult.2.1 row column).natAbs ≤ 24 := by
  have bounded := compactHermiteColumns_entry_le_det rowBound columnBound rowResult.2.1 normalizedRow
    (compactHermiteRows_zero_columns matrix normalizedInput)
  simpa only [columnResult, rowDet] using bounded

example : 0 < (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).det := by
  have positive := normalizedInput.det_pos columnBound rowBound
  simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using positive

private theorem zeroShape (rows columns : ℕ) : IsCompactRowHermite 0 (0 : Matrix (Fin rows) (Fin columns) ℤ) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
  · intro row after; rfl
  · intro row; exact row.elim0
  · intro index; exact index.elim0
  · intro row; exact row.elim0

/-- The rank-zero active determinant is the empty determinant, one. -/
example :
    ((compactHermiteRows (0 : Matrix (Fin 3) (Fin 4) ℤ)).2.1.submatrix
      (Fin.castLE (by decide : 0 ≤ 3)) (Fin.castLE (by decide : 0 ≤ 4))).det.natAbs = 1 := by
  have preserved := compactHermiteRows_det_natAbs (by decide : 0 ≤ 3) (by decide : 0 ≤ 4)
    (0 : Matrix (Fin 3) (Fin 4) ℤ) (zeroShape 4 3) (by intro row after; rfl)
  exact preserved.trans (by simp only [Matrix.det_fin_zero, Int.natAbs_one])

end Polytime2.Examples.HermiteDeterminant
