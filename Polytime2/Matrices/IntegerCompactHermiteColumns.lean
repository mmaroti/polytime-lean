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

import Polytime2.Computation.Specification
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
  have matrixReady := (triple.fst).followedBy (integerMatrixTranspose_realizable columns rows workspace)
    rfl (by intros; trivial)
  have bases := triple.snd
  have leftReady := (bases.snd).followedBy
    (integerMatrixTranspose_realizable rows rows 1) rfl (by intros; trivial)
  have rightReady := (bases.fst).followedBy
    (integerMatrixTranspose_realizable columns columns workspace) rfl (by intros; trivial)
  exact rankReady.prodMk (matrixReady.prodMk (leftReady.prodMk rightReady))

/-- The complete transpose-dual compact column pass with both actual bases. -/
private noncomputable def implementation (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((integerMatrixTranspose rows columns width).followedBy
    (integerCompactHermiteRows columns rows width) rfl (by intros; trivial)).followedBy
    (columnResult rows columns width) rfl (by intros; trivial)

/-- Column normalization reuses certified transpose and compact row normalization. -/
private theorem implementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (implementation rows columns width).Realizable :=
  ((integerMatrixTranspose_realizable rows columns width).followedBy
    (integerCompactHermiteRows_realizable columns rows width) rfl (by intros; trivial)).followedBy
    (columnResult_realizable rows columns width) rfl (by intros; trivial)

/-- The realized column pass equals the mathematical transpose-dual construction. -/
private theorem implementation_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation rows columns width).Arguments sizes //
      (implementation rows columns width).precondition sizes arguments}) :
    let result := (implementation rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteColumns (arguments.val ()).val := by
  have actual := integerCompactHermiteRows_correct columns rows width sizes
    ⟨fun _ => (integerMatrixTranspose rows columns width).compute sizes ⟨arguments.val, trivial⟩, trivial⟩
  exact congrArg (fun result => (result.1, result.2.1.transpose, result.2.2.2.transpose, result.2.2.1.transpose)) actual

/-- The mathematical compact columns normalization, with its rank and both bases.
Only the existence proof refers to the implementation. -/
noncomputable def integerCompactHermiteColumns (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => integerMatrices rows columns width)
    ((boundedUnary columns).prod
      ((integerMatrices rows columns (hermiteRowsWorkspace width columns)).prod
        ((integerMatrices rows rows (1)).prod
          (integerMatrices columns columns (hermiteRowsWorkspace width columns))))) (fun _ _ => True)
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val))
    (fun _ arguments => IntegerMatrix.compactHermiteColumns (arguments.val ()).val)
    (fun sizes arguments => ⟨(implementation rows columns width).compute sizes arguments,
      implementation_correct rows columns width sizes arguments⟩)

theorem integerCompactHermiteColumns_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteColumns rows columns width).Realizable := by
  apply (implementation_realizable rows columns width).specificationBy
  · intro sizes
    exact Fin.val_injective.prodMap
      (Subtype.val_injective.prodMap (Subtype.val_injective.prodMap Subtype.val_injective))
  · intro sizes arguments valid
    exact implementation_correct rows columns width sizes ⟨arguments, valid⟩

/-- Observe the ordinary mathematical result without unfolding the sweep. -/
theorem integerCompactHermiteColumns_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteColumns rows columns width).Arguments sizes //
      (integerCompactHermiteColumns rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteColumns rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteColumns (arguments.val ()).val := by
  exact specificationBy_correct _ (integerCompactHermiteColumns rows columns width).outputDomain _
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val)) _ _ sizes arguments

end Polytime2.Computation
