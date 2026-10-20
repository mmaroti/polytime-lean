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
import Polytime2.Computation.EncodedInputs
import Polytime2.Matrices.RowsPresentation

/-! # Mathematical row transformations with hidden realizations -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

namespace Realizable.Internal

noncomputable section RowComputations

/-- Arguments are source row, target row, coefficient, and original matrix.
Sizes specify binary counter capacity, rows, and columns. The specialization
fixes the finite scalar operation and whether both rows are written. -/
def rowTransformWithCapacity (writeSource : Bool) (scalar : EncodedDomain Empty)
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

theorem rowTransformWithCapacity_realizable (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes) :
    (rowTransformWithCapacity writeSource scalar operation).Realizable := by
  refine ofNamedLayout (rowTransformWithCapacity writeSource scalar operation)
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
end Realizable.Internal

noncomputable section PublicRowComputations

/-- The specialization fixes a scalar operation and whether the source row is
written. Public sizes are rows and columns; both row indices are valid by type.
The coefficient and original matrix are immutable, and the result is separate. -/
def rowTransform (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : scalar.Carrier Empty.elim → scalar.Carrier Empty.elim →
      scalar.Carrier Empty.elim → scalar.Carrier Empty.elim × scalar.Carrier Empty.elim) :
    Computation (Fin 2) (Fin 4) where
  inputDomains
    | 0 | 1 => StandardMatrixRows.coordinateDomain 0
    | 2 => scalar.constant.withInternalSize
    | 3 => (StandardMatrixRows.matrixDomain scalar).withInternalSize
  outputDomain := (StandardMatrixRows.matrixDomain scalar).withInternalSize
  precondition _ _ := True
  compute _ arguments := MatrixRows.transform writeSource operation (arguments.val 2)
    (arguments.val 3) (arguments.val 0) (arguments.val 1)

open Realizable.Internal StandardMatrixRows in
theorem rowTransform_realizable (writeSource : Bool) (scalar : EncodedDomain Empty)
    (operation : scalar.Carrier Empty.elim → scalar.Carrier Empty.elim →
      scalar.Carrier Empty.elim → scalar.Carrier Empty.elim × scalar.Carrier Empty.elim) :
    (rowTransform writeSource scalar operation).Realizable := by
  let internalOperation (sizes : Empty → ℕ) : scalar.Carrier sizes → scalar.Carrier sizes →
      scalar.Carrier sizes → scalar.Carrier sizes × scalar.Carrier sizes := by
    cases Subsingleton.elim sizes Empty.elim
    exact operation
  let inputs := (rowTransform writeSource scalar operation).inputDomains
  let map (name : Fin 4) (sizes : Fin 2 → ℕ) : (inputs name).Carrier sizes →
      (((rowTransformWithCapacity writeSource scalar internalOperation).withInternalSize).inputDomains name).Carrier sizes :=
    match name with
    | 0 | 1 => coordinateValue 0 sizes
    | 2 | 3 => id
  have ready := (rowTransformWithCapacity_realizable writeSource scalar internalOperation).withInternalSize.withEncodedInputs inputs map
    (by intro name sizes value; fin_cases name
        exact coordinate_bits 0 sizes value
        exact coordinate_bits 0 sizes value
        rfl
        rfl)
    (fun _ _ => True) (by
      intro sizes arguments valid
      have fits := internalCapacity_fits sizes
      exact ⟨(arguments 0).isLt, (arguments 1).isLt, fits.2.1, fits.2.2⟩)
  exact ready.withSpecification (fun _ _ => True) (rowTransform writeSource scalar operation).compute
    (by intros; trivial) (by intros; rfl)

end PublicRowComputations
end Polytime2.Computation
