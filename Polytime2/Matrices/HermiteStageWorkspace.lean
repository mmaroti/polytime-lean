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

import Polytime2.Matrices.IntegerHermiteStageUpdate
import Polytime2.Matrices.IntegerPairNarrow

/-! # Interleaved stage updates in a fixed workspace

The enclosing traversal proves that the next mathematical prefix fits its
workspace. The runtime update composes the certified stage update with matrix
pair narrowing; the logical fit proof performs no runtime bound checks.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private def withinAllowed (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteRowStageUpdate rows columns workspace).Arguments sizes) :=
  (integerHermiteRowStageUpdate rows columns workspace).precondition sizes arguments ∧
    let result := IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments 0) (arguments 1) (arguments 3) [arguments 2] (arguments 4).val (arguments 5).val
    (∀ row column, (result.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (result.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace)

private theorem withinPermitted (rows columns workspace : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerHermiteRowStageUpdate rows columns workspace).Arguments sizes)
    (valid : withinAllowed rows columns workspace sizes arguments) :
    (integerMatrixPairNarrow rows columns rows rows (2 * (2 * (2 * workspace + 1) + 1) + 1)
      (2 * (2 * (2 * workspace + 1) + 1) + 1) workspace).precondition sizes
      (fun _ => (integerHermiteRowStageUpdate rows columns workspace).compute sizes ⟨arguments, valid.1⟩) := by
  have actual := integerHermiteRowStageUpdate_correct rows columns workspace sizes ⟨arguments, valid.1⟩
  exact (congrArg (fun pair =>
    (∀ row column, (pair.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (pair.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace)) actual).mpr valid.2

/-- Execute a stage update and return both matrices to the enclosing controller's workspace. -/
noncomputable def integerHermiteRowStageUpdateWithin (rows columns workspace : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) :=
  ((integerHermiteRowStageUpdate rows columns workspace).withPrecondition
    (withinAllowed rows columns workspace) (fun _ _ valid => valid.1)).followedBy
    (integerMatrixPairNarrow rows columns rows rows (2 * (2 * (2 * workspace + 1) + 1) + 1)
      (2 * (2 * (2 * workspace + 1) + 1) + 1) workspace) rfl
    (withinPermitted rows columns workspace)

/-- The controller's fit invariant justifies narrowing without a machine-side check. -/
theorem integerHermiteRowStageUpdateWithin_realizable (rows columns workspace : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStageUpdateWithin rows columns workspace).Realizable :=
  ((integerHermiteRowStageUpdate_realizable rows columns workspace).withPrecondition
    (withinAllowed rows columns workspace) (fun _ _ valid => valid.1)).followedBy
    (integerMatrixPairNarrow_realizable rows columns rows rows (2 * (2 * (2 * workspace + 1) + 1) + 1)
      (2 * (2 * (2 * workspace + 1) + 1) + 1) workspace
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)) rfl
    (withinPermitted rows columns workspace)

/-- The fixed-workspace result retains the exact mathematical singleton stage. -/
theorem integerHermiteRowStageUpdateWithin_correct (rows columns workspace : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStageUpdateWithin rows columns workspace).Arguments sizes //
      (integerHermiteRowStageUpdateWithin rows columns workspace).precondition sizes arguments}) :
    let result := (integerHermiteRowStageUpdateWithin rows columns workspace).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 3) [arguments.val 2]
      (arguments.val 4).val (arguments.val 5).val := by
  exact integerHermiteRowStageUpdate_correct rows columns workspace sizes
    ⟨arguments.val, arguments.property.1⟩

end Polytime2.Computation.Realizable.Internal
