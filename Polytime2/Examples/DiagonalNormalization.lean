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

import Polytime2.Matrices.DiagonalBoundsMath

/-! # Diagonal divisibility cleanup examples

These mathematical examples exercise actual unimodular pair transformations,
negative and zero entries, repeated adjacent repairs, an already valid chain,
and the empty active diagonal. The accumulated bases satisfy the Smith contract
and polynomial width bounds. Machine certification of the cleanup loop remains
separate from these mathematical certificates.
-/

namespace Polytime2.Examples.DiagonalNormalization

open IntegerMatrix

example : IsSmithForm !![(30 : ℤ), 0; 0, 18] !![6, 0; 0, 90]
    (bezoutMatrix 30 18) (diagonalPairRight 30 18) 2 := by
  convert diagonalPair_isSmithForm 30 18 (by decide) (by decide) using 1; norm_num

example : bezoutMatrix (-30) 18 * !![(-30 : ℤ), 0; 0, 18] * diagonalPairRight (-30) 18 =
    !![6, 0; 0, -90] := by
  convert diagonalPair_equation (-30) 18 using 1; norm_num

example : bezoutMatrix 0 0 * (0 : Matrix (Fin 2) (Fin 2) ℤ) * diagonalPairRight 0 0 = 0 := by
  simp

example : diagonalCleanup 37 (![6, 10, 15] : Fin 3 → ℕ) = ![1, 30, 30] := by
  funext index
  fin_cases index <;> decide +kernel

example : diagonalCleanup 37 (![1, 3, 12] : Fin 3 → ℕ) = ![1, 3, 12] := by
  funext index
  fin_cases index <;> decide +kernel

example : diagonalCleanup 1 (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 := by
  funext index
  exact index.elim0

example : diagonalPotential (Fin.elim0 : Fin 0 → ℕ) = 1 := by
  simp [diagonalPotential]

example : diagonalDivisibilityChain (diagonalCleanup 37 (![6, 10, 15] : Fin 3 → ℕ)) ∧
    (∀ index, diagonalCleanup 37 (![6, 10, 15] : Fin 3 → ℕ) index < 2 ^ 13) := by
  have certified := diagonalCleanup_polynomial 4 (![6, 10, 15] : Fin 3 → ℕ)
    (by intro index; fin_cases index <;> decide) (by intro index; fin_cases index <;> decide)
  exact ⟨certified.1, certified.2.2.1⟩

/-- The actual bases record all three repairs, including revisiting the first pair. -/
example : (diagonalCleanupWithBases 37 (![6, 10, 15] : Fin 3 → ℕ) 1 1).2 =
    (!![16, -8, -1; -30, 15, 2; 5, -3, 2], !![6, 95, -5; 7, 111, -6; 1, 16, 0]) := by
  apply Prod.ext <;> ext row column
  all_goals fin_cases row <;> fin_cases column <;> decide +kernel

example :
    let result := diagonalCleanupWithBases 37 (![6, 10, 15] : Fin 3 → ℕ) 1 1
    IsSmithForm (Matrix.diagonal (fun index => ((![6, 10, 15] : Fin 3 → ℕ) index : ℤ)))
      (Matrix.diagonal (fun index => (result.1 index : ℤ))) result.2.1 result.2.2 3 := by
  exact diagonalCleanupWithBases_isSmithForm 4 (![6, 10, 15] : Fin 3 → ℕ)
    (by intro index; fin_cases index <;> decide) (by intro index; fin_cases index <;> decide)

example :
    let result := diagonalCleanupWithBases 1 (Fin.elim0 : Fin 0 → ℕ) 1 1
    IsSmithForm (Matrix.diagonal (fun index => ((Fin.elim0 : Fin 0 → ℕ) index : ℤ)))
      (Matrix.diagonal (fun index => (result.1 index : ℤ))) result.2.1 result.2.2 0 := by
  exact diagonalCleanupWithBases_isSmithForm 0 Fin.elim0 (fun index => index.elim0) (fun index => index.elim0)

end Polytime2.Examples.DiagonalNormalization
