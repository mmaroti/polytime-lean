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

import Polytime2.Matrices.RectangularDiagonalMath

/-! # Rectangular diagonal cleanup, including unused coordinates

The examples use independent row and column counts, verify the unchanged
identity action on both complementary spaces, exercise zero-dimensional
matrices, and compose a sign-corrected diagonal presentation with cleanup.
-/

namespace Polytime2.Examples.RectangularDiagonal

open IntegerMatrix

private def inputDiagonal : Fin 3 → ℕ := ![6, 10, 15]

example : (rectangularDiagonalCleanup 4 5 (by decide) (by decide) 4 inputDiagonal).1 =
    !![(1 : ℤ), 0, 0, 0, 0; 0, 30, 0, 0, 0; 0, 0, 30, 0, 0; 0, 0, 0, 0, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : (rectangularDiagonalCleanup 4 5 (by decide) (by decide) 4 inputDiagonal).2 =
    (!![(16 : ℤ), -8, -1, 0; -30, 15, 2, 0; 5, -3, 2, 0; 0, 0, 0, 1],
      !![(6 : ℤ), 95, -5, 0, 0; 7, 111, -6, 0, 0; 1, 16, 0, 0, 0;
        0, 0, 0, 1, 0; 0, 0, 0, 0, 1]) := by
  apply Prod.ext <;> ext row column
  all_goals fin_cases row <;> fin_cases column <;> decide +kernel

example :
    let result := rectangularDiagonalCleanup 4 5 (by decide) (by decide) 4 inputDiagonal
    IsSmithForm (rectangularDiagonal 4 5 inputDiagonal) result.1 result.2.1 result.2.2 3 := by
  exact rectangularDiagonalCleanup_isSmithForm (by decide) (by decide) 4 inputDiagonal
    (by intro index; fin_cases index <;> decide) (by intro index; fin_cases index <;> decide)

example :
    let result := rectangularDiagonalCleanup 0 4 (by decide) (by decide) 0 (Fin.elim0 : Fin 0 → ℕ)
    IsSmithForm (rectangularDiagonal 0 4 (Fin.elim0 : Fin 0 → ℕ)) result.1 result.2.1 result.2.2 0 := by
  exact rectangularDiagonalCleanup_isSmithForm (by decide) (by decide) 0 Fin.elim0
    (fun index => index.elim0) (fun index => index.elim0)

example :
    let result := rectangularDiagonalCleanup 4 0 (by decide) (by decide) 0 (Fin.elim0 : Fin 0 → ℕ)
    IsSmithForm (rectangularDiagonal 4 0 (Fin.elim0 : Fin 0 → ℕ)) result.1 result.2.1 result.2.2 0 := by
  exact rectangularDiagonalCleanup_isSmithForm (by decide) (by decide) 0 Fin.elim0
    (fun index => index.elim0) (fun index => index.elim0)

example : (rectangularDiagonalCleanup 3 2 (by decide) (by decide) 0 (Fin.elim0 : Fin 0 → ℕ)).2 = (1, 1) := by
  apply Prod.ext <;> ext row column
  all_goals fin_cases row <;> fin_cases column <;> decide +kernel

/-- Cleanup composes with an actual sign correction of a rectangular input. -/
example :
    let result := rectangularDiagonalCleanup 3 2 (by decide) (by decide) 5 (![30, 18] : Fin 2 → ℕ)
    IsSmithForm !![(-30 : ℤ), 0; 0, 18; 0, 0] result.1
      (result.2.1 * Matrix.diagonal ![-1, 1, 1]) result.2.2 2 := by
  have equation : Matrix.diagonal ![(-1 : ℤ), 1, 1] * !![(-30 : ℤ), 0; 0, 18; 0, 0] * (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      rectangularDiagonal 3 2 (![30, 18] : Fin 2 → ℕ) := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [rectangularDiagonal, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  have leftUnit : IsUnit (Matrix.diagonal ![(-1 : ℤ), 1, 1]).det := by
    norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]
  simpa only [Matrix.one_mul] using rectangularDiagonalCleanup_of_presentation
    (by decide) (by decide) 5 (![30, 18] : Fin 2 → ℕ)
    (by intro index; fin_cases index <;> decide) (by intro index; fin_cases index <;> decide)
    !![(-30 : ℤ), 0; 0, 18; 0, 0] (Matrix.diagonal ![-1, 1, 1]) 1 equation leftUnit (by simp)

end Polytime2.Examples.RectangularDiagonal
