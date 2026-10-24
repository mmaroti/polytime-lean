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

import Polytime2.Arrays.PackingRead
import Polytime2.Encoding.ParameterRename
import Polytime2.Computation.ComputedHost
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
    Parameter ⊕ Unit → MvPolynomial Parameter ℕ := extendedSizeBounds (fun _ : Unit => length)

/-- Retain the original mathematical sizes and add the actual packed length. -/
def packingCallSizes (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (retained : Fin (MvPolynomial.eval sizes length + 1)) :
    (computedSizeDomain (packingCallBounds length)).Carrier sizes :=
  extendedSizeValues (fun _ : Unit => length) sizes (fun _ => retained)

/-- A callee's elements may still depend on any of the caller's sizes. -/
noncomputable def packingPayload (element : EncodedDomain Parameter) : EncodedDomain (Parameter ⊕ Unit) :=
  (element.renameParameters Sum.inl).array (.inr ())

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
  have read := boundedArrayAtSize_realizable element length
    (Sum.inl : Parameter → Parameter ⊕ Unit) (.inr ()) (element.renameParameters Sum.inl)
    (fun _ => True) (fun _ _ value => value)
    (by intros; exact renameParameters_bits _ _ _ _)
  have called := (read.atComputedHostInput (fun _ : Unit => length) (boundedArray element length)
    (fun _ value _ => value.1) rfl (fun _ => boundedArrayCount_realizable element length)).withPrecondition
    (fun _ _ => True) (by intros; exact ⟨rfl, trivial⟩)
  have framed := called.followedBy (recordComputedFrame_realizable (packingCallBounds length) (packingPayload element))
    rfl (by intros; trivial)
  exact framed.withSpecification (fun _ _ => True)
    (boundedArrayCallFrame element length).compute (by intros; trivial) (by intros; rfl)

/-- Pack a mask-selected array and prepare its exact result for a consumer at
the computed count. Both stages use the same public mathematical interface. -/
noncomputable def preparePackingCall (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (arrayPack element length).followedBy (boundedArrayCallFrame element length) rfl (by intros; trivial)

theorem preparePackingCall_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (preparePackingCall element length).Realizable :=
  (arrayPack_realizable element length).followedBy (boundedArrayCallFrame_realizable element length) rfl (by intros; trivial)

end Polytime2.Computation
