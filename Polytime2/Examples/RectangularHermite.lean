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

import Polytime2.Matrices.RectangularHermiteMath

/-! # Rectangular bounded Hermite diagonalization

The active two-dimensional block is diagonalized inside a singular 3-by-4
matrix. Both full bases retain complementary identities. Rank zero and an
empty row dimension are checked as well.
-/

namespace Polytime2.Examples.RectangularHermite

open Polytime2.IntegerMatrix

private def active : Matrix (Fin 2) (Fin 2) ℤ := !![6, 0; 2, 4]
private def result := rectangularHermiteRun (by decide : 2 ≤ 3) (by decide : 2 ≤ 4) 3 active

example : result =
    (!![2, 0, 0, 0; 0, 12, 0, 0; 0, 0, 0, 0],
      !![0, 1, 0; -1, 3, 0; 0, 0, 1],
      !![1, -2, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]) := by
  apply Prod.ext
  · ext row column
    fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : result.2.1 * rectangularBlock (by decide : 2 ≤ 3) (by decide : 2 ≤ 4) active * result.2.2 =
    result.1 ∧ IsUnit result.2.1.det ∧ IsUnit result.2.2.det :=
  rectangularHermiteRun_preserves _ _ 3 active

example : result.1 = rectangularDiagonal 3 4
    (fun index => ((hermiteAlternatingRun 14 active).1 index index).natAbs) :=
  rectangularHermiteRun_diagonal _ _ 3 active
    (by intro row column before
        change row.val < column.val at before
        fin_cases row <;> fin_cases column <;> norm_num at before
        all_goals norm_num [active])
    (by decide +kernel) (by decide +kernel)

example : rectangularHermiteRun (by decide : 0 ≤ 0) (by decide : 0 ≤ 2) 0
    (0 : Matrix (Fin 0) (Fin 0) ℤ) = (0, 1, 1) := by
  apply Prod.ext
  · ext row; exact row.elim0
  · apply Prod.ext
    · ext row; exact row.elim0
    · ext row column
      fin_cases row <;> fin_cases column <;> decide +kernel

end Polytime2.Examples.RectangularHermite
