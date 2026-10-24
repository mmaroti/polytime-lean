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

import Polytime2.Matrices.HermiteStabilizationMath

/-! # Rank stabilization and both inactive strips

The rank-two example leaves a genuine lower triangular active block after the
two initial passes; subsequent alternating normalization is still needed.
The rectangular rank-one example checks the actual composed bases and zeros
in both inactive strips.
-/

namespace Polytime2.Examples.HermiteStabilization

open Polytime2.IntegerMatrix

private def original : Matrix (Fin 3) (Fin 3) ℤ := !![2, 1, 0; 0, 6, 0; 0, 0, 0]
private def result := compactHermiteInitial original

example : result.1 = 2 := by decide +kernel

example : result.2 =
    (!![1, 0, 0; 6, 12, 0; 0, 0, 0], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, -1, 0; 1, 2, 0; 0, 0, 1]) := by
  apply Prod.ext
  · ext row column; fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : original.rank = 2 := (compactHermiteInitial_rank original).symm.trans (by decide +kernel)

example : result.2.2.1 * original * result.2.2.2 = result.2.1 ∧
    IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧
    IsCompactRowHermite result.1 result.2.1.transpose ∧
    (∀ row : Fin 3, result.1 ≤ row.val → result.2.1 row = 0) :=
  compactHermiteInitial_correct original

example : ∀ column : Fin 3, result.1 ≤ column.val → result.2.1.transpose column = 0 := by
  obtain ⟨_, _, zeroColumns, _, _, _⟩ := (compactHermiteInitial_correct original).2.2.2.1
  exact zeroColumns

/-- A following row pass keeps the inactive columns zero. -/
example : ∀ column : Fin 3, result.1 ≤ column.val →
    (compactHermiteRows result.2.1).2.1.transpose column = 0 :=
  compactHermiteRows_zero_columns _ (compactHermiteInitial_correct original).2.2.2.1

example : (compactHermiteRows result.2.1).2.1 = !![1, 0, 0; 0, 12, 0; 0, 0, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

private def rectangular : Matrix (Fin 2) (Fin 3) ℤ := !![6, 1, 0; -12, -2, 0]

example : (compactHermiteInitial rectangular).2 =
    (!![1, 0, 0; 0, 0, 0], !![1, 0; 2, 1], !![0, -1, 0; 1, 6, 0; 0, 0, 1]) := by
  apply Prod.ext
  · ext row column; fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : (compactHermiteColumns (compactHermiteRows rectangular).2.1).1 = (compactHermiteRows rectangular).1 :=
  (compactHermite_initial_strips rectangular).1

/-- The composed transformation bounds depend only on the original dimensions and width. -/
example :
    let firstWidth := 2 * (3 * (3 + 3) + 1) + 3 + 2 * 3 + 2
    (∀ row column, (result.2.1 row column).natAbs < 2 ^ hermiteInitialWidth 3 3 3) ∧
    (∀ row column, (result.2.2.1 row column).natAbs < 2 ^ (1 + 3 * hermiteSweepBasisIncrement 3 3 + 3 + 2)) ∧
    (∀ row column, (result.2.2.2 row column).natAbs < 2 ^ (1 + 3 * hermiteSweepBasisIncrement 3 firstWidth + 3 + 2)) :=
  compactHermiteInitial_bound 3 original (by decide +kernel)

example : (compactHermiteInitial (0 : Matrix (Fin 0) (Fin 3) ℤ)).1 = 0 := by decide +kernel
example : (compactHermiteInitial (0 : Matrix (Fin 3) (Fin 0) ℤ)).1 = 0 := by decide +kernel
example : (compactHermiteInitial (0 : Matrix (Fin 2) (Fin 3) ℤ)).1 = 0 := by decide +kernel

end Polytime2.Examples.HermiteStabilization
