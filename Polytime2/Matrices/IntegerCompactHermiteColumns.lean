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

import Polytime2.Matrices.IntegerCompactHermiteRows

/-! # Certified compact Hermite column normalization

Transpose the input, use the complete compact row pass, then transpose the
matrix and exchange and transpose the two bases. This realizes the existing
mathematical column normalization for arbitrary signed rectangular input.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def columnResult (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (integerCompactHermiteRows columns rows width).outputDomain
  outputDomain := (boundedUnary columns).prod
    ((integerMatrices rows columns (hermiteRowsWorkspace width columns)).prod
      ((integerMatrices rows rows 1).prod
        (integerMatrices columns columns (hermiteRowsWorkspace width columns))))
  precondition _ _ := True
  compute _ arguments :=
    ((arguments.val ()).1,
      ⟨(arguments.val ()).2.1.val.transpose, fun row column => (arguments.val ()).2.1.property column row⟩,
      ⟨(arguments.val ()).2.2.2.val.transpose, fun row column => (arguments.val ()).2.2.2.property column row⟩,
      ⟨(arguments.val ()).2.2.1.val.transpose, fun row column => (arguments.val ()).2.2.1.property column row⟩)

private theorem columnResult_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (columnResult rows columns width).Realizable := by
  let workspace := hermiteRowsWorkspace width columns
  let matrix := integerMatrices columns rows workspace
  let left := integerMatrices columns columns workspace
  let right := integerMatrices rows rows 1
  let rank := boundedUnary columns
  have rankReady := pairProjection_realizable rank (matrix.prod (left.prod right)) false
  have triple := pairProjection_realizable rank (matrix.prod (left.prod right)) true
  have matrixReady := (triple.followedBy (pairProjection_realizable matrix (left.prod right) false)
    rfl (by intros; trivial)).followedBy (integerMatrixTranspose_realizable columns rows workspace)
    rfl (by intros; trivial)
  have bases := triple.followedBy (pairProjection_realizable matrix (left.prod right) true) rfl (by intros; trivial)
  have leftReady := (bases.followedBy (pairProjection_realizable left right true) rfl (by intros; trivial)).followedBy
    (integerMatrixTranspose_realizable rows rows 1) rfl (by intros; trivial)
  have rightReady := (bases.followedBy (pairProjection_realizable left right false) rfl (by intros; trivial)).followedBy
    (integerMatrixTranspose_realizable columns columns workspace) rfl (by intros; trivial)
  let context := (columnResult rows columns width).inputDomains
  have paired := Realizable.pairOutputs context _ _ (fun _ _ => True) _ _ leftReady rightReady
  have matrices := Realizable.pairOutputs context _ _ (fun _ _ => True) _ _ matrixReady paired
  exact Realizable.pairOutputs context _ _ (fun _ _ => True) _ _ rankReady matrices

/-- The complete transpose-dual compact column pass with both actual bases. -/
noncomputable def integerCompactHermiteColumns (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((integerMatrixTranspose rows columns width).followedBy
    (integerCompactHermiteRows columns rows width) rfl (by intros; trivial)).followedBy
    (columnResult rows columns width) rfl (by intros; trivial)

/-- Column normalization reuses certified transpose and compact row normalization. -/
theorem integerCompactHermiteColumns_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteColumns rows columns width).Realizable :=
  ((integerMatrixTranspose_realizable rows columns width).followedBy
    (integerCompactHermiteRows_realizable columns rows width) rfl (by intros; trivial)).followedBy
    (columnResult_realizable rows columns width) rfl (by intros; trivial)

/-- The realized column pass equals the mathematical transpose-dual construction. -/
theorem integerCompactHermiteColumns_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteColumns rows columns width).Arguments sizes //
      (integerCompactHermiteColumns rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteColumns rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteColumns (arguments.val ()).val := by
  have actual := integerCompactHermiteRows_correct columns rows width sizes
    ⟨fun _ => (integerMatrixTranspose rows columns width).compute sizes ⟨arguments.val, trivial⟩, trivial⟩
  exact congrArg (fun result => (result.1, result.2.1.transpose, result.2.2.2.transpose, result.2.2.1.transpose)) actual

/-- Column normalization retains both bases and the compact transpose specification. -/
theorem integerCompactHermiteColumns_specification (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteColumns rows columns width).Arguments sizes //
      (integerCompactHermiteColumns rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteColumns rows columns width).compute sizes arguments
    result.2.2.1.val * (arguments.val ()).val * result.2.2.2.val = result.2.1.val ∧
      IsUnit result.2.2.1.val.det ∧ IsUnit result.2.2.2.val.det ∧
      IntegerMatrix.IsCompactRowHermite result.1.val result.2.1.val.transpose := by
  have correct := IntegerMatrix.compactHermiteColumns_correct (arguments.val ()).val
  rw [← integerCompactHermiteColumns_correct rows columns width sizes arguments] at correct
  exact correct

end Polytime2.Computation
