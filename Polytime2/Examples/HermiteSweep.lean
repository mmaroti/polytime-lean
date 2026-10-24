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

import Polytime2.Matrices.HermiteSweepMath

/-! # Outer row traversal examples

The full-rank case needs successive insertions and remainder normalization.
The singular rectangular case begins with a zero row, retains a pivot in the
second input row, and recognizes a later dependent row. Empty dimensions and
the all-zero input are also covered.
-/

namespace Polytime2.Examples.HermiteSweep

open Polytime2.IntegerMatrix

private def original : Matrix (Fin 3) (Fin 3) ℤ := !![2, 11, 5; 0, 6, 1; 0, -14, 4]
private def result := hermiteRowsSweep original

example : result.2.1 = 3 := by decide +kernel

example : result.1 =
    (!![2, 1, 16; 0, 2, 13; 0, 0, 19], !![1, 3, 2; 0, 5, 2; 0, 7, 3]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : result.1.2 * original = result.1.1 ∧ IsUnit result.1.2.det := by
  have correct := hermiteRowsSweep_correct original
  exact ⟨correct.1, correct.2.1⟩

example : ∀ row column, (result.1.1 row column).natAbs < 2 ^ 56 :=
  hermiteRowsSweep_matrix_bound 4 original (by decide +kernel)

example : ∀ row column, (result.1.2 row column).natAbs <
    2 ^ (1 + 3 * hermiteSweepBasisIncrement 3 4) :=
  hermiteRowsSweep_basis_bound 4 original (by decide +kernel)

/-- The third row is still untouched before its insertion. -/
example : (hermiteRowsPrefix original 2 (by decide)).val.1 =
    (!![2, 5, 4; 0, 6, 1; 0, -14, 4], !![1, -1, 0; 0, 1, 0; 0, 0, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

private def singular : Matrix (Fin 3) (Fin 2) ℤ := !![0, 0; 6, 1; -12, -2]
private def singularResult := hermiteRowsSweep singular

example : singularResult.2.1 = 1 := by decide +kernel

example : singularResult.1 =
    (!![0, 0; 6, 1; 0, 0], !![1, 0, 0; 0, 1, 0; 0, 2, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

/-- The active row need not be the first input row. -/
example : ∃ index, singularResult.2.2.1 index = 1 := by decide +kernel

example : (hermiteRowsSweep (0 : Matrix (Fin 0) (Fin 3) ℤ)).2.1 = 0 := rfl
example : (hermiteRowsSweep (0 : Matrix (Fin 3) (Fin 0) ℤ)).2.1 = 0 := by decide +kernel
example : (hermiteRowsSweep (0 : Matrix (Fin 2) (Fin 3) ℤ)).2.1 = 0 := by decide +kernel

end Polytime2.Examples.HermiteSweep
