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

import Polytime2.Examples.SMP.PreparedInput
import Polytime2.Computation.ComputedRecord
import Polytime2.Computation.ComputedProjection

/-! # Exact SMP preparation at the original size assignment -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation EncodedDomain

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Prepare converted coordinate data at the computed multiplicities, then
retain only the exact prepared sizes and public mathematical payload. -/
noncomputable def prepareConverted (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
    (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))
  precondition _ _ := True
  compute hostSizes arguments :=
    let bounds := sizeBounds (L := L) (Carrier := Carrier) coordinates generators
    let frame := (packedFrame (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments.val, trivial⟩
    let current := computedSizeAssignment (extendedSizeBounds bounds) hostSizes frame.1
    ⟨(fun parameter => frame.1 (.inr parameter)),
      (preparedPayload (L := L) (Carrier := Carrier) coordinates generators).compute current
        ⟨(fun _ => frame.2), ⟨⟨(by intro sort; rfl), rfl⟩, (by intro sort; rfl)⟩⟩⟩

set_option maxHeartbeats 1000000 in
theorem prepareConverted_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepareConverted (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let bounds := sizeBounds (L := L) (Carrier := Carrier) coordinates generators
  let fullBounds := extendedSizeBounds bounds
  let packed := (packedDomain (L := L) (Carrier := Carrier) coordinates generators).renameParameters
    (Sum.inl : Parameter → WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  have framed := (packedFrame_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (recordComputedFrame_realizable fullBounds packed) rfl (by intros; trivial)
  have called := framed.followedBy
    ((preparedPayload_realizable (L := L) (Carrier := Carrier) coordinates generators).atComputedSizes fullBounds)
    rfl (by
      intro sizes arguments valid
      exact ⟨⟨(by intro sort; rfl), rfl⟩, (by intro sort; rfl)⟩)
  have result := called.followedBy
    (projectComputedFrame_realizable bounds (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))))
    rfl (by intros; trivial)
  exact result.withSpecification (fun _ _ => True)
    (prepareConverted (L := L) (Carrier := Carrier) coordinates generators).compute
    (by intros; trivial) (by intros; rfl)

/-- Coordinate conversion and exact-size preparation form one certified
computation at the original coordinate and generator size polynomials. -/
noncomputable def prepareInput (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (prepareConverted coordinates generators) rfl (by intros; trivial)

/-- Output size values are the exact sort counts and original generator count;
original working sizes are absent from the result. -/
theorem prepareInput_sizes (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) hostSizes
      (((prepareInput (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
        ⟨arguments, trivial⟩).1) = sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) := by
  funext parameter
  cases parameter with
  | inl sort => rfl
  | inr singleton => cases singleton; rfl

/-- The original-size computation returns precisely the natural mathematical
prepared input and dependency masks on every accepted coordinate image. -/
theorem prepareInput_payload (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate) :
    ((prepareInput (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments, trivial⟩).2 =
      (inputData (conversionGenerators coordinates generators hostSizes arguments)
        (conversionTarget coordinates generators hostSizes arguments) valid,
        dependencies (L := L) (conversionGenerators coordinates generators hostSizes arguments)) :=
  preparedPayload_correct coordinates generators hostSizes arguments valid

/-- Original-size preparation preserves the SMP question and all monolith
guarantees of the public prepared interface. -/
theorem prepareInput_specification (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate) :
    let output := (prepareInput (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩
    Multisorted.IsPrepared (L := L) (fun sort => catalogueMonolith L Carrier (entry sort))
      (graph (L := L) (Carrier := Carrier)) (Nat.card Carrier * Nat.card Carrier) output.2.1 output.2.2 ∧
    (Multisorted.IsMember (L := L) output.2.1 ↔
      conversionTarget coordinates generators hostSizes arguments ∈ Substructure.closure L
        (Set.range (conversionGenerators coordinates generators hostSizes arguments))) := by
  dsimp only
  rw [prepareInput_payload coordinates generators hostSizes arguments valid]
  exact ⟨inputData_isPrepared _ _ valid, inputData_membership _ _ valid⟩


end Polytime2.SMP.Prepared
