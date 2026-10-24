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

import Polytime2.Matrices.IntegerHermiteStep
import Polytime2.Matrices.IntegerPairNarrow

/-! # A Hermite update within a fixed workspace

The controller keeps the working matrix and accumulated left basis at a fixed
width. Its logical invariant bounds the selected column by the original column
width and both matrices by a smaller prefix width. If one additive growth step
fits the workspace, the certified Hermite update can narrow its result back to
that workspace. The logical width is a proof witness, not runtime storage.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private def withinAllowed (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteRowStep rows columns workspace).Arguments sizes) :=
  (integerHermiteRowStep rows columns workspace).precondition sizes arguments ∧
    ((arguments 3).val (arguments 0) (arguments 2)).natAbs < 2 ^ MvPolynomial.eval sizes columnWidth ∧
    ((arguments 3).val (arguments 1) (arguments 2)).natAbs < 2 ^ MvPolynomial.eval sizes columnWidth ∧
    ∃ logicalWidth : ℕ,
      (∀ row column, ((arguments 3).val row column).natAbs < 2 ^ logicalWidth) ∧
      (∀ row column, ((arguments 4).val row column).natAbs < 2 ^ logicalWidth) ∧
      logicalWidth + (2 * MvPolynomial.eval sizes columnWidth + 2) ≤ MvPolynomial.eval sizes workspace

private theorem withinFits (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStep rows columns workspace).Arguments sizes //
      withinAllowed rows columns columnWidth workspace sizes arguments}) :
    let result := (integerHermiteRowStep rows columns workspace).compute sizes ⟨arguments.val, arguments.property.1⟩
    (∀ row column, (result.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (result.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) := by
  obtain ⟨logicalWidth, matrixBound, basisBound, room⟩ := arguments.property.2.2.2
  have bounds := IntegerMatrix.hermiteRowStep_bound
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    (MvPolynomial.eval sizes columnWidth) logicalWidth logicalWidth
    (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val
    arguments.property.2.1 arguments.property.2.2.1 matrixBound basisBound
  exact ⟨fun row column => (bounds.1 row column).trans_le (pow_le_pow_right₀ (by decide) room),
    fun row column => (bounds.2 row column).trans_le (pow_le_pow_right₀ (by decide) room)⟩

/-- Execute one logical Hermite update, retaining the controller's workspace width. -/
noncomputable def integerHermiteRowStepWithin (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  ((integerHermiteRowStep rows columns workspace).withPrecondition
    (withinAllowed rows columns columnWidth workspace) (fun _ _ valid => valid.1)).followedBy
    (integerMatrixPairNarrow rows columns rows rows (2 * (2 * workspace + 1) + 1)
      (2 * (2 * workspace + 1) + 1) workspace) rfl
    (fun sizes arguments valid => withinFits rows columns columnWidth workspace sizes ⟨arguments, valid⟩)

theorem integerHermiteRowStepWithin_realizable (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStepWithin rows columns columnWidth workspace).Realizable :=
  ((integerHermiteRowStep_realizable rows columns workspace).withPrecondition
    (withinAllowed rows columns columnWidth workspace) (fun _ _ valid => valid.1)).followedBy
    (integerMatrixPairNarrow_realizable rows columns rows rows (2 * (2 * workspace + 1) + 1)
      (2 * (2 * workspace + 1) + 1) workspace
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)) rfl
    (fun sizes arguments valid => withinFits rows columns columnWidth workspace sizes ⟨arguments, valid⟩)

/-- Narrowing preserves the exact mathematical step. -/
theorem integerHermiteRowStepWithin_correct (rows columns columnWidth workspace : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStepWithin rows columns columnWidth workspace).Arguments sizes //
      (integerHermiteRowStepWithin rows columns columnWidth workspace).precondition sizes arguments}) :
    let result := (integerHermiteRowStepWithin rows columns columnWidth workspace).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStep
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := rfl

end Polytime2.Computation.Realizable.Internal
