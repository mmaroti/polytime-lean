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

import Polytime2.Computation.ComputedFrame

/-! # Dropping original sizes after a call at extended computed sizes -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

private theorem extendedResult_capacity (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) :
    SizeSubstitution.polynomial (extendedSizeBounds bounds)
      (payload.renameParameters (Sum.inr : NewParameter → Parameter ⊕ NewParameter)).widthPolynomial =
      SizeSubstitution.polynomial bounds payload.widthPolynomial := by
  simp [EncodedDomain.renameParameters, ofCodec, SizeSubstitution.polynomial,
    MvPolynomial.bind₁_rename, extendedSizeBounds, Function.comp_def]

/-- Original sizes are internal working data. Results retain only the actual
computed assignment required by their mathematical output domain. -/
noncomputable def projectComputedFrame (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) : Computation Parameter Unit :=
  unaryMap (atComputedSizeDomain (extendedSizeBounds bounds)
    (payload.renameParameters (Sum.inr : NewParameter → Parameter ⊕ NewParameter)))
    (atComputedSizeDomain bounds payload) (fun _ _ => True)
    (fun _ frame => ⟨(fun name => frame.val.1 (.inr name)), frame.val.2⟩)

theorem projectComputedFrame_realizable (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) : (projectComputedFrame bounds payload).Realizable := by
  classical
  let computation := projectComputedFrame bounds payload
  let fullBounds := extendedSizeBounds bounds
  let renamed := payload.renameParameters (Sum.inr : NewParameter → Parameter ⊕ NewParameter)
  let capacity := SizeSubstitution.polynomial bounds payload.widthPolynomial
  let index := computedSizeDomain bounds
  let sizesResult sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :=
    fun name => (arguments.val ()).1 (.inr name)
  have fieldReady name : (Computation.mk computation.inputDomains (boundedUnary (bounds name))
      computation.precondition (fun sizes arguments => sizesResult sizes arguments name)).Realizable :=
    (readComputedSize_realizable fullBounds renamed (.inr name)).withSpecification
      computation.precondition (fun sizes arguments => sizesResult sizes arguments name)
      (by intros; trivial) (by intros; rfl)
  let enumeration := Fintype.equivFin NewParameter
  have fields := Realizable.recordOutputs computation.inputDomains (Fintype.card NewParameter)
    (fun position => boundedUnary (bounds (enumeration.symm position))) computation.precondition
    (fun position sizes arguments => sizesResult sizes arguments (enumeration.symm position))
    (fun position => fieldReady (enumeration.symm position))
  have indexReady := fields.withEncodedOutput index sizesResult (fun _ => rfl) (by intros; rfl)
  let bitsResult sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :=
    (payload.encode (computedSizeAssignment bounds sizes (sizesResult sizes arguments))
      (arguments.val ()).2).setWidth (MvPolynomial.eval sizes capacity)
  have bitsReady : (Computation.mk computation.inputDomains (bitVectors capacity)
      computation.precondition bitsResult).Realizable := by
    apply Realizable.Internal.fieldProjection
      (atComputedSizeDomain fullBounds renamed) (bitVectors capacity)
      (computedSizeDomain fullBounds).widthPolynomial (fun _ _ => True)
      (fun sizes frame => (payload.encode
        (computedSizeAssignment bounds sizes (fun name => frame.val.1 (.inr name))) frame.val.2).setWidth
          (MvPolynomial.eval sizes capacity))
    intro sizes frame
    refine ⟨ArrayEncoding.bits ((computedSizeDomain fullBounds).encode sizes frame.val.1), [], ?_, ?_⟩
    · change ArrayEncoding.bits (((computedSizeDomain fullBounds).prod
        (bitVectors (SizeSubstitution.polynomial fullBounds renamed.widthPolynomial))).encode sizes
          (frame.val.1, (renamed.encode (computedSizeAssignment fullBounds sizes frame.val.1)
            frame.val.2).setWidth _)) = _
      rw [bits_prod_encode, List.append_nil,
        bits_setWidth _ (computedSizeWidth_bound fullBounds renamed sizes frame.val.1),
        bits_setWidth _ (computedSizeWidth_bound bounds payload sizes (fun name => frame.val.1 (.inr name))),
        renameParameters_bits]
      have capacityEq : SizeSubstitution.polynomial fullBounds renamed.widthPolynomial = capacity :=
        extendedResult_capacity bounds payload
      have widthEq : renamed.width (computedSizeAssignment fullBounds sizes frame.val.1) =
          payload.width (computedSizeAssignment bounds sizes (fun name => frame.val.1 (.inr name))) := by
        rw [renameParameters_width]
        rfl
      rw [capacityEq, widthEq]
      rfl
    · simp only [ArrayEncoding.bits, List.length_ofFn]
  have paired := Realizable.pairOutputs computation.inputDomains index (bitVectors capacity)
    computation.precondition sizesResult bitsResult indexReady bitsReady
  exact paired.withEncodedOutput computation.outputDomain computation.compute (fun _ => rfl) (by intros; rfl)

end Polytime2.Computation
