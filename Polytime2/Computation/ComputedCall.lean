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

import Polytime2.Computation.ComputedSizes
import Polytime2.Computation.ComputedRecord
import Polytime2.Computation.PaddedCallRealizable

/-! # Certified composition at input-dependent size assignments

The public interface uses dependent mathematical arguments and results. All
unary preparation, capacities, scratch, and machine witnesses stay private.
-/

namespace Polytime2.Computation.Realizable

open EncodedDomain CallingConvention

variable {Parameter NewParameter InputName : Type}
variable [Fintype Parameter] [Fintype NewParameter] [Fintype InputName]

/-- Invoke a realized computation at the actual sizes stored in its dependent
input frame. Size counts may depend on data, and zero sizes are supported. -/
theorem atComputedSizes {computation : Computation NewParameter InputName}
    (realizable : computation.Realizable) (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    (computation.atComputedSizes bounds).Realizable := by
  classical
  let target := computation.atComputedSizes bounds
  let payload := EncodedDomain.namedRecord computation.inputDomains
  let index := computedSizeDomain bounds
  let inputCapacity := SizeSubstitution.polynomial bounds payload.widthPolynomial
  let outputCapacity := SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial
  let context := target.inputDomains
  let allowed := target.precondition
  let kernel := computation.withRecordArgument.paddedCall bounds
  let values (name : NewParameter ⊕ Unit) sizes
      (arguments : {arguments : ∀ name, (context name).Carrier sizes // allowed sizes arguments}) :
      (kernel.inputDomains name).Carrier sizes :=
    match name with
    | .inl parameter => (arguments.val ()).1 parameter
    | .inr _ => (payload.encode
        (computedSizeAssignment bounds sizes (arguments.val ()).1) (arguments.val ()).2).setWidth
          (MvPolynomial.eval sizes inputCapacity)
  have compatible sizes arguments : kernel.precondition sizes (fun name => values name sizes arguments) := by
    exact ⟨(arguments.val ()).2, rfl, arguments.property⟩
  have producers name :
      (Computation.mk context (kernel.inputDomains name) allowed (values name)).Realizable := by
    cases name with
    | inl parameter =>
      exact (readComputedSize_realizable bounds payload parameter).withSpecification allowed
        (values (.inl parameter)) (by intros; trivial) (by intros; rfl)
    | inr name =>
      cases name
      exact (boundedSigmaPayload_realizable index (computedSizeAssignment bounds) payload
        inputCapacity (computedSizeWidth_bound bounds payload)).withSpecification allowed
        (values (.inr ())) (by intros; trivial) (by intros; rfl)
  have called := (realizable.withRecordArgument.paddedCall bounds).onResults context allowed values compatible producers
  let result sizes (arguments : {arguments : ∀ name, (context name).Carrier sizes // allowed sizes arguments}) :=
    (computation.outputDomain.encode (computedSizeAssignment bounds sizes (arguments.val ()).1)
      (computation.compute (computedSizeAssignment bounds sizes (arguments.val ()).1)
        ⟨(arguments.val ()).2, arguments.property⟩)).setWidth (MvPolynomial.eval sizes outputCapacity)
  have exactResult : (Computation.mk context (bitVectors outputCapacity) allowed result).Realizable := by
    apply called.withSpecification allowed result (by intros; assumption)
    intro sizes raw valid
    let arguments : {arguments : ∀ name, (context name).Carrier sizes // allowed sizes arguments} := ⟨raw, valid⟩
    let actual := computedSizeAssignment bounds sizes (arguments.val ()).1
    have chosen : Classical.choose (compatible sizes arguments) = (arguments.val ()).2 := by
      apply encode_setWidth_injective payload actual (MvPolynomial.eval sizes inputCapacity)
        (computedSizeWidth_bound bounds payload sizes (arguments.val ()).1)
      exact (Classical.choose_spec (compatible sizes arguments)).1
    change (computation.outputDomain.encode actual
        (computation.withRecordArgument.compute actual
          ⟨(fun _ => Classical.choose (compatible sizes arguments)),
            (Classical.choose_spec (compatible sizes arguments)).2⟩)).setWidth _ =
      (computation.outputDomain.encode actual
        (computation.compute actual ⟨(arguments.val ()).2, arguments.property⟩)).setWidth _
    apply congrArg (fun value => (computation.outputDomain.encode actual value).setWidth
      (MvPolynomial.eval sizes outputCapacity))
    change computation.compute actual ⟨Classical.choose (compatible sizes arguments), _⟩ =
      computation.compute actual ⟨(arguments.val ()).2, arguments.property⟩
    exact congrArg (computation.compute actual) (Subtype.ext chosen)
  have indexReady : (Computation.mk context index allowed
      (fun _ arguments => (arguments.val ()).1)).Realizable :=
    (boundedSigmaIndex_realizable index (computedSizeAssignment bounds) payload inputCapacity
      (computedSizeWidth_bound bounds payload)).withSpecification allowed
        (fun _ arguments => (arguments.val ()).1) (by intros; trivial) (by intros; rfl)
  have paired := Realizable.pairOutputs context index (bitVectors outputCapacity) allowed
    (fun _ arguments => (arguments.val ()).1) result indexReady exactResult
  exact paired.withEncodedOutput target.outputDomain target.compute (fun _ => rfl) (by intros; rfl)

/-- The unary call prepares its singleton argument record internally and keeps
the consumer's own precondition at the actual stored size assignment. -/
theorem atComputedUnarySizes {computation : Computation NewParameter Unit}
    (realizable : computation.Realizable) (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    (computation.atComputedUnarySizes bounds).Realizable := by
  let target := computation.atComputedUnarySizes bounds
  have framed := (recordComputedFrame_realizable bounds (computation.inputDomains ())).withPrecondition
    target.precondition (by intros; trivial)
  have called := framed.followedBy (realizable.atComputedSizes bounds) rfl (by
    intro sizes arguments valid
    exact valid)
  exact called.withSpecification target.precondition target.compute
    (by intros; assumption) (by intros; rfl)

end Polytime2.Computation.Realizable
