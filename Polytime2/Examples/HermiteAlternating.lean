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

import Polytime2.Matrices.HermiteAlternatingBounds

/-! # Bounded alternating Hermite reduction

A non-diagonal lower triangular input needs both a row and a column pass.
The polynomial budget returns the diagonal and both nonidentity bases.
Zero budget and empty dimensions are also checked.
-/

namespace Polytime2.Examples.HermiteAlternating

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 2) (Fin 2) ℤ := !![6, 0; 2, 4]
private def result := hermiteAlternatingRun (3 * 2 * 2 + 2) matrix

private theorem lower : matrix.IsLowerTriangular := by
  intro row column before
  change row.val < column.val at before
  fin_cases row <;> fin_cases column <;> norm_num at before
  all_goals norm_num [matrix]

example : result =
    (!![2, 0; 0, 12], !![0, 1; -1, 3], !![1, -2; 0, 1]) := by
  apply Prod.ext
  · ext row column
    fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : ∀ row column, row ≠ column → result.1 row column = 0 :=
  hermiteAlternatingRun_polynomial_budget 3 matrix
    lower
    (by decide +kernel) (by decide +kernel)

example : result.2.1 * matrix * result.2.2 = result.1 ∧
    IsUnit result.2.1.det ∧ IsUnit result.2.2.det :=
  hermiteAlternatingRun_preserves _ matrix

example : hermiteAlternatingRun 0 matrix = (matrix, 1, 1) := rfl

example : hermiteAlternatingRun 2 (0 : Matrix (Fin 0) (Fin 0) ℤ) = (0, 1, 1) :=
  hermiteAlternatingRun_of_diagonal _ _ (by intro row; exact row.elim0)

/-- The full accumulated run preserves the fixed determinant magnitude. -/
example : result.1.det.natAbs = 24 :=
  (hermiteAlternatingRun_det_natAbs _ matrix).trans (by decide +kernel)

/-- Original input width alone supplies the entry and actual basis width certificates. -/
example (fuel : ℕ) :
    let output := hermiteAlternatingRun fuel matrix
    (∀ row column, (output.1 row column).natAbs < 2 ^ 14) ∧
    (∀ row column, (output.2.1 row column).natAbs <
      2 ^ (1 + fuel * (1 + 2 * hermiteSweepBasisIncrement 2 14 + 2 + 1))) ∧
    (∀ row column, (output.2.2 row column).natAbs <
      2 ^ (1 + fuel * (1 + 2 * hermiteSweepBasisIncrement 2 14 + 2 + 1))) :=
  hermiteAlternatingRun_bound 3 fuel matrix
    lower
    (by decide +kernel) (by decide +kernel)

/-- The forward controller has exactly the same accumulated nonidentity bases. -/
example : hermiteAlternatingAdvance^[3 * 2 * 2 + 2] (matrix, 1, 1) = result :=
  (hermiteAlternatingRun_eq_iterate _ matrix).symm

/-- All prefixes fit fixed widths derived from the total budget. -/
example (budget count : ℕ) (within : count ≤ budget) :
    let output := hermiteAlternatingAdvance^[count] (matrix, 1, 1)
    (∀ row column, (output.1 row column).natAbs < 2 ^ 5) ∧
    (∀ row column, (output.2.1 row column).natAbs <
      2 ^ (1 + budget * (1 + 2 * hermiteSweepBasisIncrement 2 5 + 2 + 1))) ∧
    (∀ row column, (output.2.2 row column).natAbs <
      2 ^ (1 + budget * (1 + 2 * hermiteSweepBasisIncrement 2 5 + 2 + 1))) :=
  hermiteAlternatingAdvance_prefix_bound 5 budget count matrix lower
    (by decide +kernel) (by decide +kernel) (by decide +kernel) within

end Polytime2.Examples.HermiteAlternating
