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
import Polytime2.Computation.Conditional
import Polytime2.Encoding.ParameterRename

/-! # Retaining original sizes and accessing computed-size working data

Frames retain original sizes while adjoining input-dependent counts. Static
record and pair views reuse these original sizes during the computed-size call.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {HostParameter PayloadParameter Parameter : Type}
variable [Fintype HostParameter] [Fintype PayloadParameter] [Fintype Parameter]

/-- Keep original sizes while adjoining any fixed finite family of runtime
counts. -/
noncomputable def extendedSizeBounds
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ) :
    HostParameter ⊕ PayloadParameter → MvPolynomial HostParameter ℕ :=
  Sum.elim MvPolynomial.X bounds

def extendedSizeValues (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (sizes : HostParameter → ℕ) (values : (computedSizeDomain bounds).Carrier sizes) :
    (computedSizeDomain (extendedSizeBounds bounds)).Carrier sizes :=
  fun name => match name with
    | .inl parameter => ⟨sizes parameter, by simp [extendedSizeBounds]⟩
    | .inr parameter => values parameter

/-- A host payload retains its exact width when adjoining computed size names. -/
theorem extendedSize_payloadWidth
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter) :
    SizeSubstitution.polynomial (extendedSizeBounds bounds)
      (payload.renameParameters (Sum.inl : HostParameter → HostParameter ⊕ PayloadParameter)).widthPolynomial =
      payload.widthPolynomial := by
  simp [EncodedDomain.renameParameters, EncodedDomain.ofCodec, SizeSubstitution.polynomial,
    MvPolynomial.bind₁_rename, MvPolynomial.bind₁_X_left, extendedSizeBounds, Function.comp_def]

/-- Attach computed sizes to existing data without repacking or changing its
mathematical carrier. False is the new size record, true is the payload. -/
noncomputable def extendedSizeFrame
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter) : Computation HostParameter Bool where
  inputDomains | false => computedSizeDomain bounds | true => payload
  outputDomain := atComputedSizeDomain (extendedSizeBounds bounds)
    (payload.renameParameters (Sum.inl : HostParameter → HostParameter ⊕ PayloadParameter))
  precondition _ _ := True
  compute sizes arguments :=
    ⟨extendedSizeValues bounds sizes (arguments.val false), arguments.val true⟩

/-- A frame with the original host sizes has the same bits as its index and
ordinary host payload, with no additional padding. -/
theorem extendedSizeFrame_encode_bits
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ) (payload : EncodedDomain HostParameter)
    (sizes : HostParameter → ℕ) (values : (computedSizeDomain bounds).Carrier sizes)
    (payloadValue : payload.Carrier sizes) :
    EncodedDomain.ArrayEncoding.bits ((atComputedSizeDomain (extendedSizeBounds bounds)
      (payload.renameParameters (Sum.inl : HostParameter → HostParameter ⊕ PayloadParameter))).encode sizes
        ⟨extendedSizeValues bounds sizes values, payloadValue⟩) =
      EncodedDomain.ArrayEncoding.bits (((computedSizeDomain (extendedSizeBounds bounds)).prod payload).encode sizes
        (extendedSizeValues bounds sizes values, payloadValue)) := by
  let names := HostParameter ⊕ PayloadParameter
  let fullBounds := extendedSizeBounds bounds
  let index := computedSizeDomain fullBounds
  let value := extendedSizeValues bounds sizes values
  let renamed := payload.renameParameters (Sum.inl : HostParameter → names)
  let assignment := computedSizeAssignment fullBounds sizes value
  let capacity := SizeSubstitution.polynomial fullBounds renamed.widthPolynomial
  change EncodedDomain.ArrayEncoding.bits
    ((index.prod (EncodedDomain.bitVectors capacity)).encode sizes
      (value, (renamed.encode assignment payloadValue).setWidth (MvPolynomial.eval sizes capacity))) =
    EncodedDomain.ArrayEncoding.bits ((index.prod payload).encode sizes (value, payloadValue))
  rw [EncodedDomain.bits_prod_encode, EncodedDomain.bits_prod_encode,
    EncodedDomain.bits_setWidth _ (computedSizeWidth_bound fullBounds renamed sizes value),
    EncodedDomain.renameParameters_bits]
  have capacityEq : capacity = payload.widthPolynomial := extendedSize_payloadWidth bounds payload
  have widthEq : renamed.width assignment = payload.width sizes := by
    rw [EncodedDomain.renameParameters_width]
    rfl
  rw [capacityEq, widthEq]
  have evaluatedCapacity : MvPolynomial.eval sizes
      (SizeSubstitution.polynomial fullBounds renamed.widthPolynomial) = payload.width sizes :=
    congrArg (MvPolynomial.eval sizes) capacityEq
  rw [evaluatedCapacity, Nat.sub_self]
  simp only [List.replicate_zero, List.append_nil]
  rfl

theorem extendedSizeFrame_realizable
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter) :
    (extendedSizeFrame bounds payload).Realizable := by
  let computation := extendedSizeFrame bounds payload
  let names := HostParameter ⊕ PayloadParameter
  let fullBounds := extendedSizeBounds bounds
  let index := computedSizeDomain fullBounds
  let result sizes (arguments : {arguments : computation.Arguments sizes // True}) :=
    extendedSizeValues bounds sizes (arguments.val false)
  have indexReady : (Computation.mk computation.inputDomains index computation.precondition result).Realizable := by
    apply Realizable.namedRecordOutputs
    intro name
    cases name with
    | inl parameter =>
      have evaluated := (polynomialUnarySize_realizable (MvPolynomial.X parameter)).onResults
        computation.inputDomains computation.precondition (fun impossible => impossible.elim)
        (by intros; trivial) (fun impossible => impossible.elim)
      exact evaluated.withSpecification computation.precondition
        (fun sizes arguments => result sizes arguments (.inl parameter)) (by intros; trivial) (by
          intro sizes arguments valid
          apply Fin.ext
          exact MvPolynomial.eval_X parameter)
    | inr parameter =>
      exact (namedRecordProjection_realizable
        (fun parameter => EncodedDomain.boundedUnary (bounds parameter)) parameter).onResults
          computation.inputDomains computation.precondition
          (fun _ => fun sizes arguments => arguments.val false) (by intros; trivial)
          (fun _ => Realizable.argument computation.inputDomains false computation.precondition)
  have pair := Realizable.pairOutputs computation.inputDomains index payload computation.precondition
    result (fun _ arguments => arguments.val true) indexReady
    (Realizable.argument computation.inputDomains true computation.precondition)
  apply pair.withEncodedOutput computation.outputDomain computation.compute
  · intro sizes
    change MvPolynomial.eval sizes (index.widthPolynomial +
      SizeSubstitution.polynomial fullBounds
        (payload.renameParameters (Sum.inl : HostParameter → names)).widthPolynomial) = _
    rw [extendedSize_payloadWidth]
  · intro sizes arguments
    apply congrArg CallingConvention.tape
    exact extendedSizeFrame_encode_bits bounds payload sizes (arguments.val false) (arguments.val true)


/-- Select a record field while retaining the caller's original sizes in a
larger computed-size parameter family. -/
noncomputable def recordProjectionAtNames (count : ℕ)
    (fields : Fin count → EncodedDomain HostParameter) (position : Fin count)
    (hostNames : HostParameter → Parameter) : Computation Parameter Unit :=
  unaryMap ((EncodedDomain.record count fields).renameParameters hostNames)
    ((fields position).renameParameters hostNames) (fun _ _ => True)
    (fun _ values => values.val position)

theorem recordProjectionAtNames_realizable (count : ℕ)
    (fields : Fin count → EncodedDomain HostParameter) (position : Fin count)
    (hostNames : HostParameter → Parameter) :
    (recordProjectionAtNames count fields position hostNames).Realizable := by
  apply Realizable.Internal.fieldProjection _ _
    (MvPolynomial.rename hostNames (EncodedDomain.recordOffset count fields position))
  intro sizes values
  obtain ⟨before, after, equal, width⟩ := EncodedDomain.split_record_encode
    count fields (sizes ∘ hostNames) values.val position
  refine ⟨before, after, ?_, ?_⟩
  · simpa only [EncodedDomain.renameParameters_bits] using equal
  · simpa only [MvPolynomial.eval_rename] using width

/-- Parameter renaming commutes with an ordinary pair's canonical layout. -/
noncomputable def renamedPairView (first second : EncodedDomain HostParameter)
    (hostNames : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((first.prod second).renameParameters hostNames)
    ((first.renameParameters hostNames).prod (second.renameParameters hostNames))
    (fun _ value => value)

theorem renamedPairView_realizable (first second : EncodedDomain HostParameter)
    (hostNames : HostParameter → Parameter) :
    (renamedPairView first second hostNames).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, MvPolynomial.eval_rename]
  · intro sizes values
    rw [EncodedDomain.renameParameters_bits, EncodedDomain.bits_prod_encode,
      EncodedDomain.bits_prod_encode, EncodedDomain.renameParameters_bits,
      EncodedDomain.renameParameters_bits]


/-- View a host coordinate at its renamed polynomial dimension. -/
noncomputable def renamedIndexView (length : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((EncodedDomain.boundedIndex length).renameParameters names)
    (EncodedDomain.boundedIndex (MvPolynomial.rename names length))
    (fun sizes index => Fin.cast (MvPolynomial.eval_rename names sizes length).symm index)

/-- Renaming a coordinate preserves its natural value and exact binary width. -/
theorem renamedIndexView_realizable (length : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : (renamedIndexView length names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, EncodedDomain.boundedIndex, EncodedDomain.boundedIndexOfWidth]
  · intro sizes index
    rw [EncodedDomain.renameParameters_bits]
    simp only [EncodedDomain.boundedIndex, EncodedDomain.boundedIndexOfWidth,
      BitVec.ofNatLT_eq_ofNat, Fin.val_cast, EncodedDomain.ArrayEncoding.bits]
    simp only [BitVec.getLsbD_ofNat, Fin.val_cast, MvPolynomial.eval_rename]

end Polytime2.Computation
