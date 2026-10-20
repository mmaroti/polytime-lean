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

import Polytime2.Arrays.PackingResult
import Polytime2.Encoding.ParameterRename
import Polytime2.Computation.ComputedCall
import Polytime2.Computation.ComputedRecord

/-! # Preparing packed arrays for calls at the retained count

Original sizes remain available and one new size is the retained count. The
callee receives the exact packed array; all padding stays inside its frame.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain ArrayPacking CallingConvention

variable {Parameter : Type} [Fintype Parameter]

noncomputable def packingCallBounds (length : MvPolynomial Parameter ℕ) :
    Parameter ⊕ Unit → MvPolynomial Parameter ℕ := Sum.elim MvPolynomial.X (fun _ => length)

/-- Retain the original mathematical sizes and add the actual packed length. -/
def packingCallSizes (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (retained : Fin (MvPolynomial.eval sizes length + 1)) :
    (computedSizeDomain (packingCallBounds length)).Carrier sizes :=
  fun name => match name with
    | .inl parameter => ⟨sizes parameter, by simp [packingCallBounds]⟩
    | .inr _ => retained

/-- A callee's elements may still depend on any of the caller's sizes. -/
noncomputable def packingPayload (element : EncodedDomain Parameter) : EncodedDomain (Parameter ⊕ Unit) :=
  (element.renameParameters Sum.inl).array (.inr ())

private theorem packingPayload_bits (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (retained : Fin (MvPolynomial.eval sizes length + 1))
    (values : Fin retained.val → element.Carrier sizes) :
    ArrayEncoding.bits ((packingPayload element).encode
      (computedSizeAssignment (packingCallBounds length) sizes (packingCallSizes length sizes retained)) values) =
      ArrayEncoding.bits (ArrayEncoding.encode (element.encode sizes) retained.val values) := by
  simp only [packingPayload, EncodedDomain.array, ofCodec, ArrayEncoding.bits_cast, ArrayEncoding.bits_encode,
    renameParameters_bits]
  rfl

private theorem packingCall_capacity (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    SizeSubstitution.polynomial (packingCallBounds length)
      (namedRecord (fun _ : Unit => packingPayload element)).widthPolynomial = length * element.widthPolynomial := by
  rw [namedRecord_unit_widthPolynomial]
  simp [packingPayload, EncodedDomain.array, renameParameters, ofCodec,
    SizeSubstitution.polynomial, MvPolynomial.bind₁_rename, MvPolynomial.bind₁_X_left, packingCallBounds, Function.comp_def]

private theorem packingSizeRecord_realizable {InputName : Type} [Fintype InputName]
    (inputs : InputName → EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (length : MvPolynomial Parameter ℕ)
    (retained : ∀ sizes, {arguments // allowed sizes arguments} → Fin (MvPolynomial.eval sizes length + 1))
    (countReady : (Computation.mk inputs (boundedUnary length) allowed retained).Realizable) :
    (Computation.mk inputs (computedSizeDomain (packingCallBounds length)) allowed
      (fun sizes arguments => packingCallSizes length sizes (retained sizes arguments))).Realizable := by
  let sizesResult sizes arguments := packingCallSizes length sizes (retained sizes arguments)
  apply Realizable.namedRecordOutputs
  intro name
  cases name with
  | inl parameter =>
    have evaluated := (polynomialUnarySize_realizable (MvPolynomial.X parameter)).onResults
      inputs allowed (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
    exact evaluated.withSpecification allowed
      (fun sizes arguments => sizesResult sizes arguments (.inl parameter)) (by intros; trivial) (by
        intro sizes arguments valid
        apply Fin.ext
        exact MvPolynomial.eval_X parameter)
  | inr singleton => cases singleton; exact countReady

/-- Convert an existing exact packed array to the standard computed-size call
frame. The count is read from the value, without repeating packing. -/
noncomputable def boundedArrayCallFrame (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := boundedArray element length
  outputDomain := atComputedSizeDomain (packingCallBounds length) (namedRecord (fun _ : Unit => packingPayload element))
  precondition _ _ := True
  compute sizes arguments := ⟨packingCallSizes length sizes (arguments.val ()).1, fun _ => (arguments.val ()).2⟩

theorem boundedArrayCallFrame_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (boundedArrayCallFrame element length).Realizable := by
  let computation := boundedArrayCallFrame element length
  let bounds := packingCallBounds length
  let retained sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :=
    (arguments.val ()).1
  let sizesResult sizes arguments := packingCallSizes length sizes (retained sizes arguments)
  have indexReady := packingSizeRecord_realizable computation.inputDomains computation.precondition length retained
    (boundedArrayCount_realizable element length)
  have pair := Realizable.pairOutputs computation.inputDomains (computedSizeDomain bounds)
    (bitVectors (length * element.widthPolynomial)) computation.precondition sizesResult
    (boundedArrayPayload element length).compute indexReady (boundedArrayPayload_realizable element length)
  apply pair.withEncodedOutput computation.outputDomain computation.compute
  · intro sizes
    change MvPolynomial.eval sizes ((computedSizeDomain bounds).widthPolynomial +
      SizeSubstitution.polynomial bounds (namedRecord (fun _ : Unit => packingPayload element)).widthPolynomial) = _
    rw [packingCall_capacity]
  · intro sizes arguments
    let values := (arguments.val ()).2
    let assignment := computedSizeAssignment bounds sizes (sizesResult sizes arguments)
    let payload := namedRecord (fun _ : Unit => packingPayload element)
    have prefixBits : ArrayEncoding.bits (payload.encode assignment (fun _ => values)) =
        ArrayEncoding.bits (ArrayEncoding.encode (element.encode sizes) (retained sizes arguments).val values) :=
      (namedRecord_unit_bits (packingPayload element) assignment values).trans
        (packingPayload_bits element length sizes (retained sizes arguments) values)
    have capacityEq : MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds payload.widthPolynomial) =
        MvPolynomial.eval sizes (length * element.widthPolynomial) := by rw [packingCall_capacity]
    apply congrArg tape
    change ArrayEncoding.bits (((computedSizeDomain bounds).prod
      (bitVectors (SizeSubstitution.polynomial bounds payload.widthPolynomial))).encode sizes
        (sizesResult sizes arguments, (payload.encode assignment (fun _ => values)).setWidth _)) = _
    rw [bits_prod_encode, bits_prod_encode]
    apply congrArg (fun bits => ArrayEncoding.bits ((computedSizeDomain bounds).encode sizes (sizesResult sizes arguments)) ++ bits)
    change ArrayEncoding.bits ((payload.encode assignment (fun _ => values)).setWidth
      (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds payload.widthPolynomial))) =
        ArrayEncoding.bits ((ArrayEncoding.encode (element.encode sizes) (retained sizes arguments).val values).setWidth
          (MvPolynomial.eval sizes (length * element.widthPolynomial)))
    rw [capacityEq]
    exact ArrayEncoding.bits_setWidth_congr prefixBits

/-- Pack a mask-selected array and prepare its exact result for a consumer at
the computed count. Both stages use the same public mathematical interface. -/
noncomputable def preparePackingCall (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (arrayPack element length).followedBy (boundedArrayCallFrame element length) rfl (by intros; trivial)

theorem preparePackingCall_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (preparePackingCall element length).Realizable :=
  (arrayPack_realizable element length).followedBy (boundedArrayCallFrame_realizable element length) rfl (by intros; trivial)

end Polytime2.Computation
