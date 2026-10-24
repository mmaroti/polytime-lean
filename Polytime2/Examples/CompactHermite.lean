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

import Polytime2.Matrices.CompactHermiteMath

/-! # Compact pivots and actual permutation bases

A singular matrix starts with a zero row and zero first column. Both selected
pivot embeddings therefore need a nontrivial permutation. The compact result
retains the trailing mathematical column and the actual left and right bases.
-/

namespace Polytime2.Examples.CompactHermite

open Polytime2.IntegerMatrix

private def selected : Fin 2 ↪ Fin 4 := ⟨![3, 0], by decide +kernel⟩

example : (pivotPermutation selected : Fin 4 → Fin 4) = ![3, 0, 2, 1] := by
  funext index
  fin_cases index <;> decide +kernel

example : pivotPermutation (⟨Fin.elim0, by intro index; exact index.elim0⟩ : Fin 0 ↪ Fin 3) = Equiv.refl _ := rfl

private def original : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 0; 0, 6, 1; 0, -12, -2]
private def result := compactHermiteRows original

example : result.1 = 1 := by decide +kernel

example : result.2 =
    (!![6, 0, 1; 0, 0, 0; 0, 0, 0],
      !![0, 1, 0; 1, 0, 0; 0, 2, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1]) := by
  apply Prod.ext
  · ext row column; fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : result.2.2.1 * original * result.2.2.2 = result.2.1 ∧
    IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧ IsCompactRowHermite result.1 result.2.1 :=
  compactHermiteRows_correct original

example :
    (∀ row column, (result.2.1 row column).natAbs < 2 ^ 56) ∧
    (∀ row column, (result.2.2.1 row column).natAbs < 2 ^ (1 + 3 * hermiteSweepBasisIncrement 3 4)) ∧
    (∀ row column, (result.2.2.2 row column).natAbs < 2 ^ 1) :=
  compactHermiteRows_bound 4 original (by decide +kernel)

example : (compactHermiteRows (0 : Matrix (Fin 0) (Fin 3) ℤ)).1 = 0 := rfl
example : (compactHermiteRows (0 : Matrix (Fin 3) (Fin 0) ℤ)).1 = 0 := by decide +kernel
example : IsCompactRowHermite (compactHermiteRows (0 : Matrix (Fin 2) (Fin 3) ℤ)).1
    (compactHermiteRows (0 : Matrix (Fin 2) (Fin 3) ℤ)).2.1 :=
  (compactHermiteRows_correct _).2.2.2

example : (compactHermiteColumns original.transpose).2 =
    ((!![6, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ).transpose,
      (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose,
      (!![0, 1, 0; 1, 0, 0; 0, 2, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose) := by
  apply Prod.ext
  · ext row column; fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example :
    let result := compactHermiteColumns original.transpose
    result.2.2.1 * original.transpose * result.2.2.2 = result.2.1 ∧
      IsUnit result.2.2.1.det ∧ IsUnit result.2.2.2.det ∧ IsCompactRowHermite result.1 result.2.1.transpose :=
  compactHermiteColumns_correct _

/-- Rectangular column normalization retains a two-by-two left and three-by-three right basis. -/
example : (compactHermiteColumns (!![0, 6, -12; 0, 1, -2] : Matrix (Fin 2) (Fin 3) ℤ)).2 =
    (!![6, 0, 0; 1, 0, 0], !![1, 0; 0, 1], !![0, 1, 0; 1, 0, 2; 0, 0, 1]) := by
  apply Prod.ext
  · ext row column; fin_cases row <;> fin_cases column <;> decide +kernel
  · apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

example : (compactHermiteColumns (0 : Matrix (Fin 0) (Fin 3) ℤ)).1 = 0 := by decide +kernel
example : (compactHermiteColumns (0 : Matrix (Fin 3) (Fin 0) ℤ)).1 = 0 := rfl

end Polytime2.Examples.CompactHermite
