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

private def rowPlacement : PublicTape (Fin 3) (Fin 4) ↪ StandardMatrixRows.TapeName :=
  ⟨(fun role => match role with
    | .inl parameter => StandardMatrixRows.sizeTape parameter
    | .inr (.inl 0) => StandardMatrixRows.dataTape 0
    | .inr (.inl 1) => StandardMatrixRows.dataTape 1
    | .inr (.inl 2) => StandardMatrixRows.dataTape 3
    | .inr (.inl 3) => StandardMatrixRows.inputTape
    | .inr (.inr _) => StandardMatrixRows.dataTape 5), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

end Realizable.Internal

open Realizable.Internal in
theorem rowTransform_realizable (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes) :
    (rowTransform writeSource scalar operation).Realizable := by
  refine ofNamedLayout (rowTransform writeSource scalar operation)
    (StandardMatrixRows.mathematicalDomains scalar) StandardMatrixRows.readOnly
    StandardMatrixRows.sizeTapes StandardMatrixRows.outputTapes
    (StandardMatrixRows.machine writeSource scalar operation)
    (StandardMatrixRows.entry (scalar.width Empty.elim))
    (StandardMatrixRows.exit (scalar.width Empty.elim)) _ _
    (StandardMatrixRows.mathematical_contract writeSource scalar operation) rowPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by
      intro name outside
      fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inl 0, rfl⟩)
        | exact False.elim (outside ⟨.inl 1, rfl⟩)
        | exact False.elim (outside ⟨.inl 2, rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl 0), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl 1), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl 2), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl 3), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨sourceValid, targetValid, result⟩ := correct
  exact congrArg (encoded (StandardMatrixRows.matrixDomain scalar) sizes) result

end RowComputations
end Polytime2.Computation
