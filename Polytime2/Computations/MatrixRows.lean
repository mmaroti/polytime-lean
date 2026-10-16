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

import Polytime2.Computation.Layout
import Polytime2.StandardMatrixRowsPresentation

/-! # Mathematical row transformations with hidden realizations -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

noncomputable section RowComputations

/-- Arguments are source row, target row, coefficient, and original matrix.
Sizes specify binary counter capacity, rows, and columns. The specialization
fixes the finite scalar operation and whether both rows are written. -/
def rowTransform (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes) :
    Computation (Fin 3) (Fin 4) where
  inputDomains
    | 0 | 1 => EncodedDomain.binaryNaturals 0
    | 2 => scalar.constant
    | 3 => StandardMatrixRows.matrixDomain scalar
  outputDomain := StandardMatrixRows.matrixDomain scalar
  precondition sizes arguments :=
    (arguments 0).val < sizes 1 ∧ (arguments 1).val < sizes 1 ∧
      sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments := MatrixRows.transform writeSource (operation Empty.elim)
    (arguments.val 2) (arguments.val 3)
    ⟨(arguments.val 0).val, arguments.property.1⟩
    ⟨(arguments.val 1).val, arguments.property.2.1⟩

namespace Realizable.Internal

private abbrev RowTape := StandardMatrixRows.TapeName

private def rowLayout (name : RowTape) : Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ RowTape)) :=
  match name with
  | .inl (.inl (.inl parameter)) => .inl parameter
  | .inl (.inl (.inr 0)) => .inr (.inl 0)
  | .inl (.inl (.inr 1)) => .inr (.inl 1)
  | .inl (.inl (.inr 3)) => .inr (.inl 2)
  | .inr 3 => .inr (.inl 3)
  | .inl (.inl (.inr 5)) => .inr (.inr (.inl ()))
  | privateTape => .inr (.inr (.inr privateTape))

private def rowSource : Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ RowTape)) → RowTape
  | .inl parameter => StandardMatrixRows.sizeTape parameter
  | .inr (.inl 0) => StandardMatrixRows.dataTape 0
  | .inr (.inl 1) => StandardMatrixRows.dataTape 1
  | .inr (.inl 2) => StandardMatrixRows.dataTape 3
  | .inr (.inl 3) => StandardMatrixRows.inputTape
  | .inr (.inr (.inl _)) => StandardMatrixRows.dataTape 5
  | .inr (.inr (.inr name)) => name

private theorem rowLayout_leftInverse : Function.LeftInverse rowSource rowLayout := by
  intro name
  fin_cases name <;> rfl

private def rowEmbedding : RowTape ↪ Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ RowTape)) :=
  ⟨rowLayout, rowLayout_leftInverse.injective⟩

private theorem rowDomains (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes)
    (name : RowTape) :
    domains (rowTransform writeSource scalar operation) (StandardMatrixRows.mathematicalDomains scalar)
      (rowEmbedding name) = StandardMatrixRows.mathematicalDomains scalar name := by
  fin_cases name <;> rfl

end Realizable.Internal

open Realizable.Internal in
theorem rowTransform_realizable (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes) :
    (rowTransform writeSource scalar operation).Realizable := by
  let computation := rowTransform writeSource scalar operation
  let scratchDomains := StandardMatrixRows.mathematicalDomains scalar
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (rowDomains writeSource scalar operation name))
  refine ofLayout computation scratchDomains (StandardMatrixRows.mathematicalDomains scalar)
    StandardMatrixRows.readOnly StandardMatrixRows.sizeTapes StandardMatrixRows.outputTapes
    (StandardMatrixRows.machine writeSource scalar operation)
    (StandardMatrixRows.entry (scalar.width Empty.elim))
    (StandardMatrixRows.exit (scalar.width Empty.elim)) _ _
    (StandardMatrixRows.mathematical_contract writeSource scalar operation)
    rowEmbedding values
    (by
      intro name sizes
      exact congrArg (fun domain => domain.width sizes) (rowDomains writeSource scalar operation name))
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨sourceValid, targetValid, result⟩ := correct
  exact congrArg (encoded (StandardMatrixRows.matrixDomain scalar) sizes) result

end RowComputations
end Polytime2.Computation
