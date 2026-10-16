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

import Polytime2.Computation.Composition
import Polytime2.Computations.Counter
import Polytime2.Computations.GaussJordan
import Mathlib.Data.ZMod.Basic

/-! # Public finite-field elimination and composition

The example uses mathematical matrices and public realizability rules only.
-/

namespace Polytime2.Examples.GaussJordan

open Polytime2.Computation

noncomputable section MathematicalExamples

private abbrev enumeration := (ZMod.finEquiv 2).toEquiv.symm
private abbrev sizes : Fin 2 → ℕ := ![2, 3]
private def original : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 1, 0], ![1, 0, 1]]
private def expected : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 0, 1], ![0, 1, 1]]
private def arguments : (gaussJordan enumeration).Arguments sizes := fun _ => original
private theorem admissible : (gaussJordan enumeration).precondition sizes arguments := by
  trivial

example : (gaussJordan enumeration).Realizable := gaussJordan_realizable enumeration

example : (gaussJordan enumeration).compute sizes ⟨arguments, admissible⟩ = expected := by
  change Polytime2.GaussJordan.eliminate original = expected
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Polytime2.GaussJordan.eliminate, Polytime2.GaussJordan.eliminateColumns,
      Polytime2.GaussJordan.columnStep, Polytime2.GaussJordan.findPivot,
      MatrixOperations.pivotStep, MatrixOperations.clearColumn, MatrixOperations.addPivotRow,
      MatrixOperations.scaleRow, MatrixOperations.swapRows, original, expected, List.finRange] <;> decide

example : Matrix.RowEquivalent (R := ZMod 2) original
      ((gaussJordan enumeration).compute sizes ⟨arguments, admissible⟩) ∧
    Matrix.IsReducedRowEchelon (R := ZMod 2)
      ((gaussJordan enumeration).compute sizes ⟨arguments, admissible⟩) :=
  gaussJordan_correct enumeration sizes arguments admissible

/-- A downstream proof depends only on the mathematical result domain. -/
def copiedElimination : Polytime2.Computation (Fin 2) Unit :=
  (gaussJordan enumeration).followedBy (copy (gaussJordan enumeration).outputDomain) rfl
    (by intro sizes arguments valid; trivial)

theorem copiedElimination_realizable : copiedElimination.Realizable :=
  (gaussJordan_realizable enumeration).followedBy
    (copy_realizable (gaussJordan enumeration).outputDomain) rfl
    (by intro sizes arguments valid; trivial)

end MathematicalExamples
end Polytime2.Examples.GaussJordan
