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

import Polytime2.Matrices.MinorWitnessMath

/-! # Automatic original-minor witnesses

A row permutation moves a nonzero entry into the selected current block while
the same original row has a zero minor. The bound must discover a different
original row selection. Zero and empty current blocks also satisfy the bound.
-/

namespace Polytime2.Examples.MinorWitness

open Polytime2.IntegerMatrix

private def rows : Fin 1 ↪ Fin 2 := Fin.castLEEmb (by decide)
private def columns : Fin 1 ↪ Fin 1 := Function.Embedding.refl _
private def original : Matrix (Fin 2) (Fin 1) ℤ := !![0; 6]
private def current : Matrix (Fin 2) (Fin 1) ℤ := !![6; 0]
private def permutation : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

private theorem equation : permutation * original = current := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

private theorem unit : IsUnit permutation.det := by norm_num [permutation, Matrix.det_fin_two]

private theorem support : ∀ row ∉ Set.range rows, ∀ column, current row (columns column) = 0 := by
  intro row outside column
  fin_cases row
  · exact False.elim (outside ⟨0, rfl⟩)
  · fin_cases column
    rfl

example : (original.submatrix rows columns).det = 0 ∧ (current.submatrix rows columns).det = 6 := by
  decide +kernel

example : ∃ originalRows : Fin 1 ↪ Fin 2, (original.submatrix originalRows columns).det ≠ 0 :=
  exists_nonzero_original_minor rows columns original current permutation equation (by decide +kernel)

/-- The nonzero input minor is now derived internally. -/
example : (current.submatrix rows columns).det.natAbs < 2 ^ 5 :=
  unimodular_supported_minor_bound 3 rows columns original current permutation equation unit support (by decide +kernel)

example : ((0 : Matrix (Fin 2) (Fin 1) ℤ).submatrix rows columns).det.natAbs < 2 ^ 2 := by
  exact unimodular_supported_minor_bound 0 rows columns 0 0 1 (by simp) (by simp)
    (by intros; rfl) (by intros; norm_num)

example (matrix : Matrix (Fin 0) (Fin 0) ℤ) : matrix.det.natAbs < 2 ^ 1 := by
  exact unimodular_supported_minor_bound 0 (Function.Embedding.refl (Fin 0)) (Function.Embedding.refl (Fin 0))
    matrix matrix 1 (by simp) (by simp) (by intro row; exact row.elim0) (by intro row; exact row.elim0)

end Polytime2.Examples.MinorWitness
