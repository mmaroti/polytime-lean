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
import Polytime2.Arithmetic.UnarySuccessor
import Polytime2.Computation.ComputedFrame
import Polytime2.Computation.ComputedCall

/-! # Appending at the decoded length of a bounded array

The old live array is read at its stored count, then the existing array snoc is
called at that count. Capacity padding is not interpreted as an element.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def source (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :=
  (boundedArray element capacity).prod element

private noncomputable def callee (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    Computation (Parameter ⊕ Unit) Unit where
  inputDomains _ := (source element capacity).renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)
  outputDomain := (element.renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)).arrayOfLength (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1)
  precondition sizes arguments := (arguments ()).1.1.val = sizes (.inr ())
  compute sizes arguments := by
    let packed : (boundedArray element capacity).Carrier (sizes ∘ Sum.inl) := (arguments.val ()).1
    have countEquation : packed.1.val = sizes (.inr ()) := arguments.property
    let values : Fin (MvPolynomial.eval sizes (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit))) → element.Carrier (sizes ∘ Sum.inl) :=
      fun index => packed.2 ⟨index.val, by rw [countEquation]; simpa only [MvPolynomial.eval_X] using index.isLt⟩
    exact snocValues (Parameter := Parameter ⊕ Unit) (Element := element.Carrier (sizes ∘ Sum.inl)) (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit)) sizes values (arguments.val ()).2

private theorem callee_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (callee element capacity).Realizable := by
  let computation := callee element capacity
  let renamed := element.renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)
  have viewed := (renamedPairView_realizable (boundedArray element capacity) element
    (Sum.inl : Parameter → Parameter ⊕ Unit)).withPrecondition computation.precondition (by intros; trivial)
  have packed := viewed.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have appended := viewed.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have live := packed.followedBy
    (boundedArrayAtSize_realizable element capacity Sum.inl (.inr ()) renamed (fun _ => True)
      (fun _ _ value => value) (by intro sizes valid value; exact renameParameters_bits element Sum.inl sizes value)) rfl
    (by intro sizes arguments valid; exact ⟨valid, trivial⟩)
  have polynomial := live.reinterpretOutput (renamed.arrayOfLength (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit)))
    (fun sizes values => arrayParameterEquiv renamed (.inr ()) sizes values) (by intros; rfl)
    (by intro sizes values; exact (array_X_encode_bits renamed (.inr ()) sizes values).symm)
  have complete := (arraySnoc_realizable renamed (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit))).onResults
    computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => arrayParameterEquiv renamed (.inr ()) sizes
          (fun index => (arguments.val ()).1.2 (Fin.cast arguments.property.symm index))
      | true => (arguments.val ()).2) (by intros; trivial) (by
        intro choice
        cases choice
        · exact polynomial
        · exact appended)
  apply complete.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  rfl

private noncomputable def rankBounds (capacity : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ :=
  fun _ => capacity

private noncomputable def frame (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :=
  (extendedSizeFrame (rankBounds capacity) (source element capacity)).onResults
    (fun _ : Unit => source element capacity) (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => fun _ => (arguments.val ()).1.1
      | true => arguments.val ()) (by intros; trivial)

private theorem frame_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (frame element capacity).Realizable := by
  let context := fun _ : Unit => source element capacity
  have count := (pairProjection_realizable (boundedArray element capacity) element false).followedBy
    (boundedArrayCount_realizable element capacity) rfl (by intros; trivial)
  have header : (Computation.mk context (computedSizeDomain (rankBounds capacity)) (fun _ _ => True)
      (fun _ arguments _ => (arguments.val ()).1.1)).Realizable := by
    apply Realizable.namedRecordOutputs
    intro name
    cases name
    exact count
  apply (extendedSizeFrame_realizable (rankBounds capacity) (source element capacity)).onResults
    context (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => fun _ => (arguments.val ()).1.1
      | true => arguments.val ()) (by intros; trivial)
  intro choice
  cases choice
  · exact header
  · exact Realizable.argument context () (fun _ _ => True)

/-- Append at the decoded count, retaining the old size assignment with the live result array. -/
noncomputable def boundedArraySnocCall (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (frame element capacity).followedBy
    ((callee element capacity).atComputedUnarySizes (extendedSizeBounds (rankBounds capacity))) rfl
    (by intro sizes arguments valid; rfl)

/-- Frame preparation and live-array appending reuse the generic computed-size call. -/
theorem boundedArraySnocCall_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (boundedArraySnocCall element capacity).Realizable :=
  (frame_realizable element capacity).followedBy
    ((callee_realizable element capacity).atComputedUnarySizes (extendedSizeBounds (rankBounds capacity))) rfl
    (by intro sizes arguments valid; rfl)

/-- The callee receives the stored count rather than the capacity bound. -/
theorem boundedArraySnocCall_count (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnocCall element capacity).Arguments sizes //
      (boundedArraySnocCall element capacity).precondition sizes arguments}) :
    (((boundedArraySnocCall element capacity).compute sizes arguments).1 (.inr ())).val =
      (arguments.val ()).1.1.val := rfl

/-- The new last live element is precisely the supplied appended value. -/
theorem boundedArraySnocCall_last (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnocCall element capacity).Arguments sizes //
      (boundedArraySnocCall element capacity).precondition sizes arguments}) :
    let result := (boundedArraySnocCall element capacity).compute sizes arguments
    result.2 ⟨(arguments.val ()).1.1.val, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change (arguments.val ()).1.1.val < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      omega⟩ = (arguments.val ()).2 := by
  let result := (boundedArraySnocCall element capacity).compute sizes arguments
  let actual := computedSizeAssignment (extendedSizeBounds (rankBounds capacity)) sizes result.1
  let index : Fin (MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1)) :=
    ⟨(arguments.val ()).1.1.val, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change (arguments.val ()).1.1.val < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      omega⟩
  dsimp only [boundedArraySnocCall, Computation.followedBy, Computation.atComputedUnarySizes, frame,
    Computation.onResults, extendedSizeFrame, callee, snocValues]
  change Fin.snoc (n := MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit)))
    (α := fun _ => element.Carrier sizes) _ (arguments.val ()).2 (Fin.cast (by simp) index) = _
  have atLast : Fin.cast (by simp) index = Fin.last (MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit))) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last, index, actual, MvPolynomial.eval_X]
    rfl
  rw [atLast, Fin.snoc_last]

/-- Every old live element retains its value and position. -/
theorem boundedArraySnocCall_get (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnocCall element capacity).Arguments sizes //
      (boundedArraySnocCall element capacity).precondition sizes arguments})
    (position : Fin (arguments.val ()).1.1.val) :
    let result := (boundedArraySnocCall element capacity).compute sizes arguments
    result.2 ⟨position.val, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change position.val < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      omega⟩ = (arguments.val ()).1.2 position := by
  let result := (boundedArraySnocCall element capacity).compute sizes arguments
  let actual := computedSizeAssignment (extendedSizeBounds (rankBounds capacity)) sizes result.1
  let index : Fin (MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1)) :=
    ⟨position.val, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change position.val < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      omega⟩
  let old : Fin (MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit))) :=
    ⟨position.val, by
      simp only [MvPolynomial.eval_X]
      change position.val < (result.1 (.inr ())).val
      rw [boundedArraySnocCall_count]
      exact position.isLt⟩
  dsimp only [boundedArraySnocCall, Computation.followedBy, Computation.atComputedUnarySizes, frame,
    Computation.onResults, extendedSizeFrame, callee, snocValues]
  change Fin.snoc (n := MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit)))
    (α := fun _ => element.Carrier sizes) _ (arguments.val ()).2 (Fin.cast (by simp) index) = _
  have before : Fin.cast (by simp) index = old.castSucc := by apply Fin.ext; rfl
  rw [before, Fin.snoc_castSucc]

private theorem live_bits (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnocCall element capacity).Arguments sizes //
      (boundedArraySnocCall element capacity).precondition sizes arguments}) :
    let result := (boundedArraySnocCall element capacity).compute sizes arguments
    ArrayEncoding.bits ((callee element capacity).outputDomain.encode
      (computedSizeAssignment (extendedSizeBounds (rankBounds capacity)) sizes result.1) result.2) =
    ArrayEncoding.bits (ArrayEncoding.encode (element.encode sizes) ((arguments.val ()).1.1.val + 1)
      (Fin.snoc (α := fun _ => element.Carrier sizes) (arguments.val ()).1.2 (arguments.val ()).2)) := by
  dsimp only
  let result := (boundedArraySnocCall element capacity).compute sizes arguments
  let actual := computedSizeAssignment (extendedSizeBounds (rankBounds capacity)) sizes result.1
  have lengthEquation : MvPolynomial.eval actual (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1) =
      (arguments.val ()).1.1.val + 1 := by
    simp only [map_add, map_one, MvPolynomial.eval_X]
    rfl
  let values : Fin ((arguments.val ()).1.1.val + 1) → element.Carrier sizes :=
    fun index => result.2 (Fin.cast lengthEquation.symm index)
  have ordered : values = Fin.snoc (α := fun _ => element.Carrier sizes) (arguments.val ()).1.2 (arguments.val ()).2 := by
    funext index
    refine Fin.lastCases ?_ ?_ index
    · rw [Fin.snoc_last]
      exact boundedArraySnocCall_last element capacity sizes arguments
    · intro position
      rw [Fin.snoc_castSucc]
      exact boundedArraySnocCall_get element capacity sizes arguments position
  change ArrayEncoding.bits (((element.renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)).arrayOfLength
    (MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1)).encode actual result.2) = _
  rw [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, ArrayEncoding.bits_encode]
  simp only [renameParameters_bits]
  change (List.ofFn (fun index => ArrayEncoding.bits (element.encode sizes (result.2 index)))).flatten = _
  have aligned := List.ofFn_congr lengthEquation
    (fun index => ArrayEncoding.bits (element.encode sizes (result.2 index)))
  have preserved := congrArg (fun entries : Fin ((arguments.val ()).1.1.val + 1) → element.Carrier sizes =>
    (List.ofFn (fun index => ArrayEncoding.bits (element.encode sizes (entries index)))).flatten) ordered
  exact (congrArg List.flatten aligned).trans preserved

private noncomputable def payloadCapacity (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :=
  SizeSubstitution.polynomial (extendedSizeBounds (rankBounds capacity)) (callee element capacity).outputDomain.widthPolynomial

private theorem payloadCapacity_eq (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    payloadCapacity element capacity = (capacity + 1) * element.widthPolynomial := by
  change SizeSubstitution.polynomial (extendedSizeBounds (rankBounds capacity))
    ((MvPolynomial.X (Sum.inr () : Parameter ⊕ Unit) + 1) * MvPolynomial.rename Sum.inl element.widthPolynomial) = _
  simp [SizeSubstitution.polynomial, MvPolynomial.bind₁_rename, MvPolynomial.bind₁_X_left,
    extendedSizeBounds, rankBounds, Function.comp_def]

private theorem payloadFits (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes (capacity * element.widthPolynomial) ≤ MvPolynomial.eval sizes (payloadCapacity element capacity) := by
  rw [payloadCapacity_eq]
  simp only [map_mul, map_add, map_one]
  nlinarith

private noncomputable def payloadPrefix (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  unaryMap (bitVectors (payloadCapacity element capacity)) (bitVectors (capacity * element.widthPolynomial))
    (fun _ _ => True) (fun sizes word => word.val.setWidth (MvPolynomial.eval sizes (capacity * element.widthPolynomial)))

private theorem payloadPrefix_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (payloadPrefix element capacity).Realizable := by
  apply Realizable.Internal.fieldProjection (bitVectors (payloadCapacity element capacity))
    (bitVectors (capacity * element.widthPolynomial)) 0
  intro sizes word
  let bits := ArrayEncoding.bits word.val
  refine ⟨[], bits.drop (MvPolynomial.eval sizes (capacity * element.widthPolynomial)), ?_, by simp⟩
  change bits = [] ++ ArrayEncoding.bits (word.val.setWidth (MvPolynomial.eval sizes (capacity * element.widthPolynomial))) ++
    bits.drop (MvPolynomial.eval sizes (capacity * element.widthPolynomial))
  rw [bits_setWidth_take _ (payloadFits element capacity sizes)]
  exact (List.take_append_drop _ bits).symm

private noncomputable def payload (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :=
  ((boundedArraySnocCall element capacity).followedBy
    (boundedSigmaPayload (computedSizeDomain (extendedSizeBounds (rankBounds capacity)))
      (computedSizeAssignment (extendedSizeBounds (rankBounds capacity))) (callee element capacity).outputDomain
      (payloadCapacity element capacity) (computedSizeWidth_bound _ _)) rfl (by intros; trivial)).followedBy
    (payloadPrefix element capacity) rfl (by intros; trivial)

private theorem payload_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (payload element capacity).Realizable :=
  ((boundedArraySnocCall_realizable element capacity).followedBy
    (boundedSigmaPayload_realizable (computedSizeDomain (extendedSizeBounds (rankBounds capacity)))
      (computedSizeAssignment (extendedSizeBounds (rankBounds capacity))) (callee element capacity).outputDomain
      (payloadCapacity element capacity) (computedSizeWidth_bound _ _)) rfl (by intros; trivial)).followedBy
    (payloadPrefix_realizable element capacity) rfl (by intros; trivial)

private theorem payload_correct (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (payload element capacity).Arguments sizes // (payload element capacity).precondition sizes arguments}) :
    (payload element capacity).compute sizes arguments =
      (ArrayEncoding.encode (element.encode sizes) ((arguments.val ()).1.1.val + 1)
        (Fin.snoc (α := fun _ => element.Carrier sizes) (arguments.val ()).1.2 (arguments.val ()).2)).setWidth
          (MvPolynomial.eval sizes (capacity * element.widthPolynomial)) := by
  apply ArrayEncoding.bits_injective
  have actual := live_bits element capacity sizes arguments
  have padded := ArrayEncoding.bits_setWidth_congr (capacity := MvPolynomial.eval sizes (capacity * element.widthPolynomial)) actual
  let result := (boundedArraySnocCall element capacity).compute sizes arguments
  let word := (callee element capacity).outputDomain.encode
    (computedSizeAssignment (extendedSizeBounds (rankBounds capacity)) sizes result.1) result.2
  dsimp only [payload, Computation.followedBy, payloadPrefix, unaryMap]
  change ArrayEncoding.bits ((word.setWidth (MvPolynomial.eval sizes (payloadCapacity element capacity))).setWidth
    (MvPolynomial.eval sizes (capacity * element.widthPolynomial))) = _
  rw [BitVec.setWidth_setWidth_of_le _ (payloadFits element capacity sizes)]
  exact padded

/-- Append one live element while retaining the bounded array's original capacity. -/
noncomputable def boundedArraySnoc (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := source element capacity
  outputDomain := boundedArray element capacity
  precondition sizes arguments := (arguments ()).1.1.val < MvPolynomial.eval sizes capacity
  compute sizes arguments := ⟨⟨(arguments.val ()).1.1.val + 1, Nat.succ_lt_succ arguments.property⟩,
    Fin.snoc (α := fun _ => element.Carrier sizes) (arguments.val ()).1.2 (arguments.val ()).2⟩

/-- Increment the header and append the live payload through certified computed-size calls. -/
theorem boundedArraySnoc_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (boundedArraySnoc element capacity).Realizable := by
  let computation := boundedArraySnoc element capacity
  have count := ((pairProjection_realizable (boundedArray element capacity) element false).followedBy
    (boundedArrayCount_realizable element capacity) rfl (by intros; trivial)).withPrecondition
    computation.precondition (by intros; trivial)
  have header := count.followedBy (boundedUnarySuccessor_realizable capacity) rfl (by
    intro sizes arguments valid
    exact valid)
  have contents := (payload_realizable element capacity).withPrecondition computation.precondition (by intros; trivial)
  have paired := Realizable.pairOutputs computation.inputDomains (boundedUnary capacity)
    (bitVectors (capacity * element.widthPolynomial)) computation.precondition _ _ header contents
  apply paired.withEncodedOutput computation.outputDomain computation.compute (by intros; rfl)
  intro sizes arguments
  have exactPayload := payload_correct element capacity sizes ⟨arguments.val, trivial⟩
  exact congrArg (fun word => CallingConvention.encoded
    ((boundedUnary capacity).prod (bitVectors (capacity * element.widthPolynomial))) sizes
      (⟨(arguments.val ()).1.1.val + 1, Nat.succ_lt_succ arguments.property⟩, word)) exactPayload.symm

/-- Appending increases the actual count by exactly one. -/
theorem boundedArraySnoc_count (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnoc element capacity).Arguments sizes //
      (boundedArraySnoc element capacity).precondition sizes arguments}) :
    ((boundedArraySnoc element capacity).compute sizes arguments).1.val = (arguments.val ()).1.1.val + 1 := rfl

/-- Existing live elements retain their values and positions. -/
theorem boundedArraySnoc_get (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnoc element capacity).Arguments sizes //
      (boundedArraySnoc element capacity).precondition sizes arguments}) (index : Fin (arguments.val ()).1.1.val) :
    ((boundedArraySnoc element capacity).compute sizes arguments).2 index.castSucc = (arguments.val ()).1.2 index := by
  dsimp only [boundedArraySnoc]
  exact Fin.snoc_castSucc _ _ _

/-- The appended element is the new last live value. -/
theorem boundedArraySnoc_last (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedArraySnoc element capacity).Arguments sizes //
      (boundedArraySnoc element capacity).precondition sizes arguments}) :
    ((boundedArraySnoc element capacity).compute sizes arguments).2 (Fin.last (arguments.val ()).1.1.val) = (arguments.val ()).2 := by
  dsimp only [boundedArraySnoc]
  exact Fin.snoc_last _ _

end Polytime2.Computation
