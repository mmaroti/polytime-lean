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

import Polytime2.Matrices.HermiteProtectedMath

/-! # Reducing an active column without disturbing an earlier block

The first diagonal entry is already complete. Reducing the second column must
retain its row and column, as well as a nonidentity protected basis row. The
active block still undergoes a genuine gcd pivot change.
-/

namespace Polytime2.Examples.HermiteProtected

open Polytime2.IntegerMatrix

private def matrix : Matrix (Fin 3) (Fin 3) ℤ := !![2, 0, 0; 0, 6, 1; 0, -17, 4]
private def basis : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, 3; 0, 1, 0; 0, 0, 1]

example : hermiteColumnPrefix 1 1 3 matrix basis =
    (!![2, 0, 0; 0, 1, 7; 0, 0, 41], !![1, 2, 3; 0, 3, 1; 0, 17, 6]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;> decide +kernel

/-- The block theorem retains the arbitrary protected basis row, not only the diagonal. -/
example :
    (hermiteColumnPrefix 1 1 3 matrix basis).1 0 = matrix 0 ∧
    (hermiteColumnPrefix 1 1 3 matrix basis).2 0 = basis 0 ∧
    ∀ row, (hermiteColumnPrefix 1 1 3 matrix basis).1 row 0 = matrix row 0 := by
  have preserved := hermiteColumnSweep_protected ({0} : Set (Fin 3)) ({0} : Set (Fin 3)) 1 1
    (hermiteColumnTargets 1 3) matrix basis (by simp) (by
      intro row member
      have zero : row = 0 := by simpa using member
      subst row
      rfl) (by
      intro row outside column member
      have zero : column = 0 := by simpa using member
      subst column
      fin_cases row <;> simp_all [matrix])
  exact ⟨(preserved.1 0 (by simp)).1, (preserved.1 0 (by simp)).2, preserved.2 0 (by simp)⟩

end Polytime2.Examples.HermiteProtected
