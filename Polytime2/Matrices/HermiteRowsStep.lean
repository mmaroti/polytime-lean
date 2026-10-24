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

import Polytime2.Matrices.HermiteRowsWorkspace

/-! # A fixed-workspace step for the outer Hermite traversal

The current matrices and pivot embeddings equal a canonical prefix of a bounded
original input. That mathematical witness proves that advancing and resizing
returns both matrices to the same original-input-derived workspace.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private def allowed (rows columns inputWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).Arguments sizes) : Prop :=
  ∃ original : (integerMatrices rows columns inputWidth).Carrier sizes,
    (((arguments () 1).val, (arguments () 2).val), (arguments () 0).1) =
      (IntegerMatrix.hermiteRowsPrefix original.val (arguments () 0).2.val
        (Nat.le_of_lt (arguments () 0).2.isLt)).val

private theorem permitted (rows columns inputWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).Arguments sizes)
    (valid : allowed rows columns inputWidth sizes arguments) :
    (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).precondition sizes arguments := by
  obtain ⟨original, same⟩ := valid
  apply integerHermiteAdvance_permitted rows columns (hermiteRowsWorkspace inputWidth rows) sizes arguments original.val
  rw [same]
  exact (IntegerMatrix.hermiteRowsPrefix original.val _ _).property

private theorem fits (rows columns inputWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).Arguments sizes //
      allowed rows columns inputWidth sizes arguments}) :
    let result := (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes
      ⟨arguments.val, permitted rows columns inputWidth sizes arguments.val arguments.property⟩
    (∀ row column, (result.1.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace inputWidth rows)) ∧
    (∀ row column, (result.1.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace inputWidth rows)) := by
  obtain ⟨original, same⟩ := arguments.property
  exact integerHermiteAdvance_workspace rows columns inputWidth sizes
    ⟨arguments.val, permitted rows columns inputWidth sizes arguments.val arguments.property⟩ original.val original.property same

/-- Advance a canonical prefix and return matrices to the same polynomial workspace. -/
noncomputable def integerHermiteRowsStep (rows columns inputWidth : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).inputDomains
  outputDomain := ((integerMatrices rows columns (hermiteRowsWorkspace inputWidth rows)).prod
    (integerMatrices rows rows (hermiteRowsWorkspace inputWidth rows))).prod (hermitePivotSelection rows columns)
  precondition := allowed rows columns inputWidth
  compute sizes arguments :=
    let result := (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes
      ⟨arguments.val, permitted rows columns inputWidth sizes arguments.val arguments.property⟩
    ((⟨result.1.1.val, (fits rows columns inputWidth sizes arguments).1⟩,
      ⟨result.1.2.val, (fits rows columns inputWidth sizes arguments).2⟩), result.2)

/-- Fixed-workspace advancement reuses the realized transition and matrix resizing. -/
theorem integerHermiteRowsStep_realizable (rows columns inputWidth : MvPolynomial Parameter ℕ) :
    (integerHermiteRowsStep rows columns inputWidth).Realizable := by
  let computation := integerHermiteRowsStep rows columns inputWidth
  let width := hermiteRowsWorkspace inputWidth rows
  let matrix := integerMatrices rows columns width
  let basis := integerMatrices rows rows width
  have advanced := (integerHermiteAdvance_realizable rows columns width).withPrecondition computation.precondition
    (permitted rows columns inputWidth)
  have pair := advanced.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldMatrix := pair.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldBasis := pair.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have selection := advanced.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have matrixReady := oldMatrix.followedBy (integerMatrixResize_realizable rows columns (hermiteInsertOutputWidth width rows) width)
    rfl (by intro sizes arguments valid; exact (fits rows columns inputWidth sizes ⟨arguments, valid⟩).1)
  have basisReady := oldBasis.followedBy (integerMatrixResize_realizable rows rows (hermiteInsertOutputWidth width rows) width)
    rfl (by intro sizes arguments valid; exact (fits rows columns inputWidth sizes ⟨arguments, valid⟩).2)
  have matrices := Realizable.pairOutputs computation.inputDomains matrix basis computation.precondition _ _ matrixReady basisReady
  have paired := Realizable.pairOutputs computation.inputDomains (matrix.prod basis) (hermitePivotSelection rows columns)
    computation.precondition _ _ matrices selection
  exact paired.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- The fixed-workspace result is exactly the next canonical mathematical prefix. -/
theorem integerHermiteRowsStep_correct (rows columns inputWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowsStep rows columns inputWidth).Arguments sizes //
      (integerHermiteRowsStep rows columns inputWidth).precondition sizes arguments})
    (original : (integerMatrices rows columns inputWidth).Carrier sizes)
    (same : (((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1) =
      (IntegerMatrix.hermiteRowsPrefix original.val (arguments.val () 0).2.val (Nat.le_of_lt (arguments.val () 0).2.isLt)).val) :
    let result := (integerHermiteRowsStep rows columns inputWidth).compute sizes arguments
    (((result.1.1.val, result.1.2.val), result.2) : IntegerMatrix.HermiteRowState
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)) =
      (IntegerMatrix.hermiteRowsPrefix original.val ((arguments.val () 0).2.val + 1) (arguments.val () 0).2.isLt).val := by
  have invariant : IntegerMatrix.HermiteRowPrefix original.val (arguments.val () 0).2.val
      (((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1) := by
    rw [same]
    exact (IntegerMatrix.hermiteRowsPrefix original.val _ _).property
  have advanced := integerHermiteAdvance_correct rows columns (hermiteRowsWorkspace inputWidth rows) sizes
    ⟨arguments.val, permitted rows columns inputWidth sizes arguments.val arguments.property⟩ original.val invariant
  apply advanced.trans
  apply congrArg (fun state => (IntegerMatrix.hermiteRowAdvance original.val (arguments.val () 0).2 state).val)
  exact Subtype.ext same

end Polytime2.Computation
