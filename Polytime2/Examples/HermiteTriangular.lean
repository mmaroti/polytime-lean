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

import Polytime2.Matrices.HermiteTriangularMath

/-! # Canonical insertion in a lower triangular matrix

The incoming third row causes a genuine gcd change. A nonzero fourth row
remains unprocessed, including its positive diagonal in the future column.
-/

namespace Polytime2.Examples.HermiteTriangular

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![6, 0, 0, 0; 0, 5, 0, 0; 2, 0, 4, 0; 7, 3, 2, 9]

private def outerState := hermiteRowsPrefix matrix 2 (by decide)
private def selected : Fin 3 ↪ Fin 4 := Fin.castLEEmb (by decide)
private def columns : Fin 2 → Fin 4 := Fin.castLE (by decide)
private def inserted := hermiteInsertRow selected columns outerState.val.1.1 outerState.val.1.2

private theorem lower : matrix.IsLowerTriangular := by
  intro row column before
  change row.val < column.val at before
  fin_cases row <;> fin_cases column <;> norm_num at before
  all_goals norm_num [matrix]

example : ∀ row : Fin 3, ∀ column : Fin 4, 3 ≤ column.val →
    outerState.val.1.1 (Fin.castLE (by decide) row) column = 0 :=
  outerState.property.incoming_rectangle_zero lower (by decide)

example : inserted.2 = some 2 ∧
    (∀ index, 0 < inserted.1.1 index index) ∧
    (diagonalPotential (fun index => (inserted.1.1 index index).natAbs)).size ≤
      (diagonalPotential (fun index => (outerState.val.1.1 index index).natAbs)).size := by
  exact hermiteInsertRow_canonical_progress (by decide : 2 + 1 ≤ 4)
    outerState.val.1.1 outerState.val.1.2 (by decide +kernel) (by decide +kernel)
    (fun index => outerState.property.upper_right_zero lower _ _ index.isLt (by decide))
    (outerState.property.incoming_rectangle_zero lower (by decide))

example : inserted.1.1 =
    !![2, 0, 4, 0; 0, 5, 0, 0; 0, 0, 12, 0; 7, 3, 2, 9] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

/-- The first insertion has no earlier pivots. -/
example :
    (hermiteInsertRow (Fin.castLEEmb (by decide : 0 + 1 ≤ 4))
      (Fin.castLE (by decide : 0 ≤ 4)) matrix 1).2 = some 0 := by
  exact (hermiteInsertRow_canonical_progress (by decide : 0 + 1 ≤ 4)
    matrix 1 (by decide +kernel) (by intro row; exact row.elim0)
    (by intro row; exact row.elim0)
    (by intro row column after
        fin_cases row; fin_cases column <;> simp_all [matrix])).1

/-- A genuine first gcd update remains strict after the later divisible stage and extension. -/
example :
    (diagonalPotential (fun row => ((hermiteInsertRow selected columns matrix 1).1.1 row row).natAbs)).size <
      (diagonalPotential (fun row => (matrix row row).natAbs)).size :=
  hermiteInsertRow_canonical_strict (by decide : 2 + 1 ≤ 4) matrix 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 0 (by decide +kernel)

/-- The complete existing traversal retains all four canonical pivots. -/
example : (hermiteRowsSweep matrix).2 =
    ⟨4, Fin.castLEEmb (by decide), Fin.castLEEmb (by decide)⟩ ∧
    (∀ index, 0 < (hermiteRowsSweep matrix).1.1 index index) ∧
    (diagonalPotential (fun index => ((hermiteRowsSweep matrix).1.1 index index).natAbs)).size ≤
      (diagonalPotential (fun index => (matrix index index).natAbs)).size :=
  hermiteRowsPrefix_canonical matrix lower (by decide +kernel) 4 (by decide)

example : (hermiteRowsSweep (0 : Matrix (Fin 0) (Fin 0) ℤ)).2.1 = 0 := by
  have canonical := hermiteRowsPrefix_canonical (0 : Matrix (Fin 0) (Fin 0) ℤ)
    (by intro row; exact row.elim0) (by intro index; exact index.elim0) 0 (by decide)
  exact congrArg Sigma.fst canonical.1

private def divisible : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 4, 3]

/-- Without a gcd change, a complete row sweep is diagonal and retains the actual basis. -/
example : (hermiteRowsSweep divisible).1 = (!![2, 0; 0, 3], !![1, 0; -2, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : (hermiteRowsSweep divisible).1.1.IsLowerTriangular :=
  hermiteRowsPrefix_lower_of_potential_le divisible
    (by intro row column before
        change row.val < column.val at before
        fin_cases row <;> fin_cases column <;> norm_num at before
        all_goals norm_num [divisible])
    (by decide +kernel) 2 (by decide) (by decide +kernel)

private def changing : Matrix (Fin 2) (Fin 2) ℤ := !![6, 0; 2, 4]

/-- A non-diagonal completed pass forces strict progress by the full-pass theorem. -/
example :
    (diagonalPotential (fun row => ((hermiteRowsSweep changing).1.1 row row).natAbs)).size <
      (diagonalPotential (fun row => (changing row row).natAbs)).size := by
  have alternatives := hermiteRowsSweep_diagonal_or_progress changing
    (by intro row column before
        change row.val < column.val at before
        fin_cases row <;> fin_cases column <;> norm_num at before
        all_goals norm_num [changing])
    (by decide +kernel)
  rcases alternatives with diagonal | strict
  · have zero := diagonal 0 1 (by decide)
    have nonzero : (hermiteRowsSweep changing).1.1 0 1 ≠ 0 := by decide +kernel
    exact False.elim (nonzero zero)
  · exact strict

end Polytime2.Examples.HermiteTriangular
