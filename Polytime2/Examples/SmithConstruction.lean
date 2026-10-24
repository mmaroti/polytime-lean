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

import Polytime2.Matrices.SmithConstructionBounds

/-! # Complete mathematical Smith construction

Signed rectangular and singular inputs use the full pipeline, including initial
compaction and final divisibility cleanup. The contracts retain both actual
unimodular bases and cover empty dimensions.
-/

namespace Polytime2.Examples.SmithConstruction

open Polytime2.IntegerMatrix

private def signed : Matrix (Fin 2) (Fin 3) ℤ := !![-6, 0, 0; 2, 4, 0]
private def signedResult := smithNormalForm 3 signed

example : IsSmithForm signed signedResult.2.1 signedResult.2.2.1 signedResult.2.2.2 signedResult.1 :=
  smithNormalForm_isSmithForm 3 signed (by decide +kernel)

example : signedResult.2.1 = !![2, 0, 0; 0, 12, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

private def singular : Matrix (Fin 2) (Fin 3) ℤ := !![0, 0, 0; 0, -6, 9]
private def singularResult := smithNormalForm 4 singular

example : IsSmithForm singular singularResult.2.1 singularResult.2.2.1 singularResult.2.2.2 singularResult.1 :=
  smithNormalForm_isSmithForm 4 singular (by decide +kernel)

example : singularResult.1 = 1 := by decide +kernel

example : singularResult.2.1 = !![3, 0, 0; 0, 0, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : (smithNormalForm 0 (0 : Matrix (Fin 0) (Fin 2) ℤ)).1 = 0 := by decide +kernel

example :
    let matrix := (0 : Matrix (Fin 2) (Fin 0) ℤ)
    let result := smithNormalForm 0 matrix
    IsSmithForm matrix result.2.1 result.2.2.1 result.2.2.2 result.1 :=
  smithNormalForm_isSmithForm 0 _ (by intro row column; exact column.elim0)

/-- The full signed rectangular result uses one width derived from the original instance sizes. -/
example :
    (∀ row column, (signedResult.2.1 row column).natAbs < 2 ^ smithNormalFormWidth 2 3 3) ∧
    (∀ row column, (signedResult.2.2.1 row column).natAbs < 2 ^ smithNormalFormWidth 2 3 3) ∧
    (∀ row column, (signedResult.2.2.2 row column).natAbs < 2 ^ smithNormalFormWidth 2 3 3) :=
  smithNormalForm_bound 3 signed (by decide +kernel)

end Polytime2.Examples.SmithConstruction
