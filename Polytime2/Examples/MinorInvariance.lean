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

import Polytime2.Matrices.HermiteIncomingBounds

/-! # Bounding an incoming entry by an invariant proper minor

The selected rows are zero and two of a rectangular matrix. The unselected
row remains nonzero in the selected column, so a zero-support assumption would
not apply. A genuine Bézout change retains the selected determinant magnitude
44; the resulting triangular minor bounds the next incoming entry, 22.
-/

namespace Polytime2.Examples.MinorInvariance

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 3) (Fin 2) ℤ := !![6, 1; 99, 37; -14, 5]
private def selectedRows : Fin 2 ↪ Fin 3 := ⟨![0, 2], by
  intro first second equal
  fin_cases first <;> fin_cases second <;> simp_all⟩
private def selectedColumns : Fin 2 ↪ Fin 2 := Function.Embedding.refl _

private def reduced := (hermiteRowStage 0 2 0 [] matrix 1).1.submatrix selectedRows selectedColumns

example : hermiteRowStage 0 2 0 [] matrix 1 =
    (!![2, 15; 99, 37; 0, 22], !![5, 0, 2; 0, 1, 0; 7, 0, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : reduced.det.natAbs = 44 := by
  have invariant := hermiteRowStage_minor_natAbs selectedRows selectedColumns 0 1 (by decide) 0 [] (by decide) matrix 1
  have initial : (matrix.submatrix selectedRows selectedColumns).det.natAbs = 44 := by decide +kernel
  exact invariant.trans initial

private theorem reduced_upper : reduced.IsUpperTriangular := by
  intro row column below
  fin_cases row <;> fin_cases column <;> norm_num at below
  decide +kernel

/-- The incoming entry has a bound in the original input width, rather than an intermediate width. -/
example : ((hermiteRowStage 0 2 0 [] matrix 1).1 2 1).natAbs < 2 ^ 19 := by
  exact hermiteRowStage_diagonal_bound 7 selectedRows selectedColumns 0 1 (by decide) 0 [] (by decide) matrix 1
    (by decide +kernel) 1 reduced_upper (by
      intro other different
      fin_cases other
      · decide +kernel
      · exact False.elim (different rfl))

private def prefixMatrix : Matrix (Fin 4) (Fin 3) ℤ := !![6, 1, 4; 0, 2, 3; 99, 37, 8; -14, 5, 7]
private def prefixRows : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by
  intro first second equal
  fin_cases first <;> fin_cases second <;> simp_all⟩
private def prefixColumns : Fin 2 → Fin 3 := ![0, 1]
private def prefixResult := hermiteIncomingPrefix prefixRows prefixColumns 2 prefixMatrix 1

example : prefixResult =
    (!![2, 1, 13; 0, 2, 3; 99, 37, 8; 0, 0, 16],
      !![5, -7, 0, 2; 0, 1, 0, 0; 0, 0, 1, 0; 7, -11, 0, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

/-- The prefix invariants supply the triangular minor needed for the incoming bound. -/
example : (prefixResult.1 3 2).natAbs < 2 ^ 31 := by
  exact hermiteIncomingPrefix_incoming_bound 7 prefixRows (Function.Embedding.refl (Fin 3))
    prefixColumns (by decide +kernel) prefixMatrix 1 (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel)

/-- The second pivot is untouched while the first incoming entry is eliminated. -/
example :
    (hermiteIncomingPrefix prefixRows prefixColumns 1 prefixMatrix 1).1 1 = prefixMatrix 1 ∧
      (hermiteIncomingPrefix prefixRows prefixColumns 1 prefixMatrix 1).2 1 =
        (1 : Matrix (Fin 4) (Fin 4) ℤ) 1 := by
  exact hermiteIncomingPrefix_future_row prefixRows prefixColumns 1 1 (by decide) prefixMatrix 1

/-- Every visited pivot stays positive, clears the incoming row, and normalizes above it. -/
example : ∀ index : Fin 2,
    0 < prefixResult.1 (prefixRows index.castSucc) (prefixColumns index) ∧
    prefixResult.1 (prefixRows (Fin.last 2)) (prefixColumns index) = 0 ∧
    ∀ earlier : Fin 2, earlier < index →
      0 ≤ prefixResult.1 (prefixRows earlier.castSucc) (prefixColumns index) ∧
      prefixResult.1 (prefixRows earlier.castSucc) (prefixColumns index) <
        prefixResult.1 (prefixRows index.castSucc) (prefixColumns index) := by
  intro index
  have entries := hermiteIncomingPrefix_entries prefixRows prefixColumns 2 (by decide) prefixMatrix 1
    (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) index index.isLt
  exact ⟨entries.1, entries.2.1, entries.2.2.1⟩

/-- A two-row minor bounds the future entry after only the first of two pivots. -/
example : ((hermiteIncomingPrefix prefixRows prefixColumns 1 prefixMatrix 1).1 3 2).natAbs < 2 ^ 19 := by
  let minorRows : Fin 2 ↪ Fin 4 := ⟨![0, 3], by decide +kernel⟩
  let minorColumns : Fin 2 ↪ Fin 3 := ⟨![0, 2], by decide +kernel⟩
  exact hermiteIncomingPrefix_truncated_bound 7 1 (by decide) prefixRows prefixColumns minorRows minorColumns
    (by decide +kernel) (by decide +kernel) (by decide +kernel) prefixMatrix 1
    (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel)

/-- The full incoming traversal derives polynomial matrix and basis widths from its input. -/
example :
    (∀ row column, (prefixResult.1 row column).natAbs < 2 ^ 199) ∧
      (∀ row column, (prefixResult.2 row column).natAbs < 2 ^ 529) := by
  let columns : Fin 2 ↪ Fin 3 := ⟨prefixColumns, by decide +kernel⟩
  have bound := hermiteIncomingPrefix_bound 7 1 2 (by decide) prefixRows columns prefixMatrix 1
    (by decide +kernel) (by
      intro row column below
      fin_cases row <;> fin_cases column <;> norm_num at below
      decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [prefixResult, columns, Function.Embedding.coeFn_mk] using bound

end Polytime2.Examples.MinorInvariance
