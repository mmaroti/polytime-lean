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

import Polytime2.Matrices.HermiteDiagonalMath

/-! # Weighted progress for nonadjacent Hermite pivots

A gcd update from row zero to row two moves a factor of three to the later
diagonal entry. The middle entry remains fixed. The next divisible stage keeps
the diagonal unchanged. A negative incoming pivot entry is also checked.
-/

namespace Polytime2.Examples.HermiteDiagonal

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 3) (Fin 3) ℤ := !![6, 0, 0; 0, 5, 0; 2, 0, 4]
private def first := hermiteRowStage 0 2 0 [] matrix 1
private def second := hermiteRowStage 1 2 1 [0] first.1 first.2

example : first =
    (!![2, 0, 4; 0, 5, 0; 0, 0, 12], !![0, 0, 1; 0, 1, 0; -1, 0, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : (diagonalPotential (fun index => (matrix index index).natAbs)) = 21600 ∧
    (diagonalPotential (fun index => (first.1 index index).natAbs)) = 2400 := by decide +kernel

example : ∀ index, 0 < first.1 index index :=
  hermiteRowStage_diagonal_positive 0 2 (by decide) [] (by simp) (by simp) (by simp) matrix 1
    (by decide +kernel) rfl (by simp)

/-- The shared bit measure decreases across a nonadjacent genuine gcd update. -/
example : (diagonalPotential (fun index => (first.1 index index).natAbs)).size <
    (diagonalPotential (fun index => (matrix index index).natAbs)).size :=
  hermiteRowStage_potential_decreases 0 2 (by decide) [] (by simp) (by simp) (by simp) matrix 1
    (by decide +kernel) rfl (by simp) (by decide +kernel)

example : ∀ index, second.1 index index = first.1 index index :=
  hermiteRowStage_diagonal_of_dvd 1 2 (by decide) [0] (by decide) (by decide) (by decide)
    first.1 first.2 (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

example : (diagonalPotential (fun index => (second.1 index index).natAbs)).size ≤
    (diagonalPotential (fun index => (first.1 index index).natAbs)).size :=
  hermiteRowStage_potential_mono 1 2 (by decide) [0] (by decide) (by decide) (by decide)
    first.1 first.2 (by decide +kernel) rfl (by decide +kernel)

private def negative : Matrix (Fin 2) (Fin 2) ℤ := !![6, 0; -2, 4]

example :
    (diagonalPotential (fun index => ((hermiteRowStage 0 1 0 [] negative 1).1 index index).natAbs)).size <
      (diagonalPotential (fun index => (negative index index).natAbs)).size :=
  hermiteRowStage_potential_decreases 0 1 (by decide) [] (by simp) (by simp) (by simp) negative 1
    (by decide +kernel) rfl (by simp) (by decide +kernel)

end Polytime2.Examples.HermiteDiagonal
