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

import Polytime2.Examples.SMP.PreparedMasks
import Polytime2.Examples.SMP.PreparedMonolith

/-! # Reading exact typed columns at the prepared input sizes -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation EncodedDomain

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Fixed sort enumerations specialize the existing finite scalar codec. -/
noncomputable def enumeration (sort : SortIndex (L := L) (Carrier := Carrier)) :
    SortCarrier sort ≃ Fin (@Fintype.card (SortCarrier sort) (Fintype.ofFinite _)) :=
  @Fintype.equivFin (SortCarrier sort) (Fintype.ofFinite _)

noncomputable def preparedColumnDomain (sort : SortIndex (L := L) (Carrier := Carrier)) :
    EncodedDomain (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) :=
  let scalar := EncodedDomain.fixed (enumeration sort)
  scalar.prod (scalar.array (.inr (.inr ())))

/-- The sort count and generator count are the actual public prepared sizes.
Reading the contiguous payload needs no transpose or elementwise conversion. -/
noncomputable def readExactColumns (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Unit :=
  unaryMap
    ((boundedArray (typedColumn generators (entry sort)).outputDomain coordinates).renameParameters Sum.inl)
    ((preparedColumnDomain (L := L) (Carrier := Carrier) (Parameter := Parameter) sort).array (.inr (.inl sort)))
    (fun current packed => packed.1.val = current (.inr (.inl sort)) ∧
      MvPolynomial.eval (current ∘ Sum.inl) generators = current (.inr (.inr ())))
    (fun _ packed position =>
      let column := packed.val.2 (Fin.cast packed.property.1.symm position)
      (column.1, fun generator => column.2 (Fin.cast packed.property.2.symm generator)))

theorem readExactColumns_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    (readExactColumns coordinates generators sort).Realizable := by
  apply Realizable.Internal.fieldProjection _ _
    (MvPolynomial.rename Sum.inl (boundedUnary coordinates).widthPolynomial)
  intro current packed
  let original := current ∘ (Sum.inl : Parameter → WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  let values := packed.val.2
  let source := (typedColumn generators (entry sort)).outputDomain
  let target := preparedColumnDomain (L := L) (Carrier := Carrier) (Parameter := Parameter) sort
  have columnBits (column : source.Carrier original) :
      ArrayEncoding.bits (target.encode current
        (column.1, fun generator => column.2 (Fin.cast packed.property.2.symm generator))) =
      ArrayEncoding.bits (source.encode original column) := by
    simp only [source, target, typedColumn, coordinateBlockMap, preparedColumnDomain,
      bits_prod_encode, array_encode_bits, arrayOfLength_encode_bits, ArrayEncoding.bits_encode,
      constant_encode_bits, elementDomain, fixed_encode_bits, enumeration,
      ArrayEncoding.bits_cast, ArrayEncoding.bits_append]
    apply congrArg (List.append _)
    exact congrArg List.flatten
      (List.ofFn_congr packed.property.2 (fun generator => ArrayEncoding.bits
        (BitVec.ofNat (Nat.clog 2 (@Fintype.card (SortCarrier (L := L) (Carrier := Carrier) sort)
          (Fintype.ofFinite _))) ((enumeration sort) (column.2 generator)).val))).symm
  have payloadBits : ArrayEncoding.bits
      ((target.array (.inr (.inl sort))).encode current
        (fun position =>
          let column := values (Fin.cast packed.property.1.symm position)
          (column.1, fun generator => column.2 (Fin.cast packed.property.2.symm generator)))) =
      ArrayEncoding.bits (ArrayEncoding.encode (source.encode original) packed.val.1.val values) := by
    simp only [array_encode_bits, ArrayEncoding.bits_encode]
    simp_rw [columnBits]
    exact congrArg List.flatten
      (List.ofFn_congr packed.property.1 (fun position => ArrayEncoding.bits
        (source.encode original (values position)))).symm
  refine ⟨ArrayEncoding.bits ((boundedUnary coordinates).encode original packed.val.1),
    List.replicate (MvPolynomial.eval original (coordinates * source.widthPolynomial) -
      packed.val.1.val * source.width original) false, ?_, ?_⟩
  · rw [payloadBits, renameParameters_bits]
    change ArrayEncoding.bits (((boundedUnary coordinates).prod
      (bitVectors (coordinates * source.widthPolynomial))).encode original
        (packed.val.1, (ArrayEncoding.encode (source.encode original) packed.val.1.val values).setWidth _)) = _
    rw [bits_prod_encode, bits_setWidth _ (by
      simp only [map_mul]
      exact Nat.mul_le_mul_right (source.width original) (Nat.le_of_lt_succ packed.val.1.isLt))]
    exact (List.append_assoc _ _ _).symm
  · simp only [ArrayEncoding.bits, List.length_ofFn, MvPolynomial.eval_rename]
    rfl

/-- Assemble generators and target as the one public exact multisorted input.
The source-coordinate labels are absent from this output domain. -/
noncomputable def preparedInput (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Unit where
  inputDomains _ := (packedDomain (L := L) (Carrier := Carrier) coordinates generators).renameParameters Sum.inl
  outputDomain := (Multisorted.inputDomain (enumeration (L := L) (Carrier := Carrier))).renameParameters
    (Sum.inr : Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) →
      WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  precondition current arguments :=
    (∀ sort, (arguments () sort).1.1.val = current (.inr (.inl sort))) ∧
      MvPolynomial.eval (current ∘ Sum.inl) generators = current (.inr (.inr ()))
  compute current arguments :=
    let columns sort := (readExactColumns coordinates generators sort).compute current
      ⟨(fun _ => (arguments.val () sort).1), ⟨arguments.property.1 sort, arguments.property.2⟩⟩
    ((fun generator sort position => (columns sort position).2 generator),
      fun sort position => (columns sort position).1)

theorem preparedInput_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (preparedInput (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let computation := preparedInput (L := L) (Carrier := Carrier) coordinates generators
  let columns sort := (preparedColumnDomain (L := L) (Carrier := Carrier) (Parameter := Parameter) sort).array (.inr (.inl sort))
  have fieldReady sort : (Computation.mk computation.inputDomains (columns sort) computation.precondition
      (fun current arguments => (readExactColumns coordinates generators sort).compute current
        ⟨(fun _ => (arguments.val () sort).1), ⟨arguments.property.1 sort, arguments.property.2⟩⟩)).Realizable := by
    let column := (typedColumn generators (entry sort)).outputDomain
    let source := boundedArray (bitVectors (coordinates + 1)) coordinates
    have first := (packedSortView_realizable coordinates generators sort).followedBy
      (pairProjection_realizable ((boundedArray column coordinates).renameParameters Sum.inl)
        (source.renameParameters Sum.inl) false) rfl (by intros; trivial)
    apply (readExactColumns_realizable coordinates generators sort).onResults
    intro name
    cases name
    exact first.withSpecification _ _ (by intros; trivial) (by intros; rfl)
  have assembled := Realizable.recordOutputs computation.inputDomains (Nat.card (SICatalogue L Carrier))
    columns computation.precondition
    (fun sort current arguments position =>
      ((computation.compute current arguments).2 sort position,
        fun generator => (computation.compute current arguments).1 generator sort position))
    fieldReady
  apply assembled.withEncodedOutput computation.outputDomain computation.compute
  · intro current
    simp only [computation, preparedInput, renameParameters_width, width, Multisorted.inputDomain]
    rw [reindex_widthPolynomial]
    simp [columns, preparedColumnDomain, Function.comp_def]
  · intro current arguments
    apply congrArg CallingConvention.tape
    simp only [computation, preparedInput, renameParameters_bits, Multisorted.inputDomain]
    rw [reindex_encode_bits]
    simp only [bits_record_encode, columns, preparedColumnDomain, array_encode_bits,
      ArrayEncoding.bits_encode, bits_prod_encode, fixed_encode_bits]
    rfl

/-- The public runtime data are exactly the mathematical prepared input. -/
theorem preparedInput_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate) :
    let frame := (packedFrame (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩
    let current := computedSizeAssignment
      (extendedSizeBounds (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)) hostSizes frame.1
    (preparedInput (L := L) (Carrier := Carrier) coordinates generators).compute current
      ⟨(fun _ => frame.2), ⟨(by intro sort; rfl), rfl⟩⟩ =
        inputData (conversionGenerators coordinates generators hostSizes arguments)
          (conversionTarget coordinates generators hostSizes arguments) valid := by
  apply Prod.ext
  · funext generator sort position
    exact packSort_generator coordinates generators hostSizes arguments sort position generator
  · funext sort position
    exact packSort_target coordinates generators hostSizes arguments valid sort position

/-- Final payload construction exposes only the exact SMP input and its masks.
All source labels and original-size working data stay in the caller. -/
noncomputable def preparedPayload (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Unit where
  inputDomains := (preparedInput (L := L) (Carrier := Carrier) coordinates generators).inputDomains
  outputDomain := (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))).renameParameters
    (Sum.inr : Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) →
      WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  precondition current arguments :=
    (preparedInput (L := L) (Carrier := Carrier) coordinates generators).precondition current arguments ∧
      (dependencyMasks (L := L) (Carrier := Carrier) coordinates generators).precondition current arguments
  compute current arguments :=
    ((preparedInput (L := L) (Carrier := Carrier) coordinates generators).compute current
      ⟨arguments.val, arguments.property.1⟩,
      (dependencyMasks (L := L) (Carrier := Carrier) coordinates generators).compute current
        ⟨arguments.val, arguments.property.2⟩)

theorem preparedPayload_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (preparedPayload (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let computation := preparedPayload (L := L) (Carrier := Carrier) coordinates generators
  have inputReady := (preparedInput_realizable (L := L) (Carrier := Carrier) coordinates generators).withSpecification
    computation.precondition (fun current arguments => (computation.compute current arguments).1)
    (by intro current arguments valid; exact valid.1) (by intros; rfl)
  have masksReady := (dependencyMasks_realizable (L := L) (Carrier := Carrier) coordinates generators).withSpecification
    computation.precondition (fun current arguments => (computation.compute current arguments).2)
    (by intro current arguments valid; exact valid.2) (by intros; rfl)
  have paired := Realizable.pairOutputs computation.inputDomains
    (preparedInput (L := L) (Carrier := Carrier) coordinates generators).outputDomain
    (dependencyMasks (L := L) (Carrier := Carrier) coordinates generators).outputDomain computation.precondition
    (fun current arguments => (computation.compute current arguments).1)
    (fun current arguments => (computation.compute current arguments).2) inputReady masksReady
  apply paired.withEncodedOutput computation.outputDomain computation.compute
  · intro current
    simp [computation, preparedPayload, Multisorted.preparedDomain, preparedInput,
      dependencyMasks, width, MvPolynomial.eval_rename]
  · intro current arguments
    apply congrArg CallingConvention.tape
    simp only [computation, preparedPayload, Multisorted.preparedDomain, preparedInput,
      dependencyMasks, renameParameters_bits, ArrayEncoding.bits_cast, ArrayEncoding.bits_append]

/-- On accepted targets, the computed payload is the exact mathematical
preparation, including its stored dependency coordinates. -/
theorem preparedPayload_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate) :
    let frame := (packedFrame (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩
    let current := computedSizeAssignment
      (extendedSizeBounds (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)) hostSizes frame.1
    (preparedPayload (L := L) (Carrier := Carrier) coordinates generators).compute current
      ⟨(fun _ => frame.2), ⟨⟨(by intro sort; rfl), rfl⟩, (by intro sort; rfl)⟩⟩ =
        (inputData (conversionGenerators coordinates generators hostSizes arguments)
          (conversionTarget coordinates generators hostSizes arguments) valid,
          dependencies (L := L) (conversionGenerators coordinates generators hostSizes arguments)) := by
  apply Prod.ext
  · exact preparedInput_correct coordinates generators hostSizes arguments valid
  · exact dependencyMasks_correct coordinates generators hostSizes arguments


end Polytime2.SMP.Prepared
