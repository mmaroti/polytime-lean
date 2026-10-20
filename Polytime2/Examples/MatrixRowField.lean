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
import Polytime2.Matrices.RowsOperations
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Matrices.FieldRow
import Polytime2.Matrices.RowField
import Mathlib.Data.ZMod.Basic

/-! # Finite-field row operations through mathematical certificates -/

namespace Polytime2.Examples.MatrixRowField

open Polytime2.Computation

noncomputable section RowExamples

private abbrev sizes : Fin 2 → ℕ := ![2, 3]
private abbrev enumeration := (ZMod.finEquiv 2).toEquiv.symm
private abbrev scalar := FieldRow.scalarDomain enumeration
private def original : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 0, 1], ![0, 1, 0]]
private def expected : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 0, 1], ![1, 1, 1]]

private def addition : Computation (Fin 2) (Fin 4) :=
  rowTransform false scalar (Polytime2.MatrixRowField.add (Scalar := ZMod 2))
private def arguments : addition.Arguments sizes
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | 2 => (1 : ZMod 2)
  | 3 => original
private theorem admissible : addition.precondition sizes arguments := by
  trivial

private theorem addition_realizable : addition.Realizable :=
  rowTransform_realizable false scalar (Polytime2.MatrixRowField.add (Scalar := ZMod 2))

/-- Row addition returns the expected ordinary matrix without exposing tapes. -/
theorem add_rectangular : addition.compute sizes ⟨arguments, admissible⟩ = expected := by
  change MatrixRows.transform false (Polytime2.MatrixRowField.add (Scalar := ZMod 2))
    1 original (0 : Fin 2) (1 : Fin 2) = expected
  rw [Polytime2.MatrixRowField.add_transform]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [original, expected]

private def copiedAddition := addition.followedBy (copy addition.outputDomain) rfl
  (by intro sizes arguments valid; trivial)

example : copiedAddition.Realizable :=
  addition_realizable.followedBy (copy_realizable addition.outputDomain) rfl _

example : copiedAddition.compute sizes ⟨arguments, admissible⟩ = expected := add_rectangular

-- Empty column families require no special capacity assumptions.
example (input : addition.Arguments (![1, 0] : Fin 2 → ℕ)) :
    addition.compute ![1, 0] ⟨input, trivial⟩ = input 3 := by
  funext row column
  exact column.elim0

-- Every scalar can occupy zero bits; both selected rows may coincide.
example : (rowTransform true (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (fun (_coefficient source target : Fin 1) => (target, source))).Realizable :=
  rowTransform_realizable _ _ _

end RowExamples
end Polytime2.Examples.MatrixRowField
