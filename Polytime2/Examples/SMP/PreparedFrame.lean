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

import Polytime2.Examples.SMP.PreparedPacking
import Polytime2.Arrays.PackingRead
import Polytime2.Computation.ComputedCall

/-! # A shared computed-size frame for all packed SMP sorts

The finite catalogue fixes the number of counts. Runtime sizes contain every
sort multiplicity and the generator count, alongside the original sizes needed
only during conversion. Source labels remain internal conversion data.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {Parameter : Type} [Fintype Parameter]

/-- Exact packed columns and original source labels for each fixed sort. -/
noncomputable def packedDomain (coordinates generators : MvPolynomial Parameter ℕ) :
    EncodedDomain Parameter :=
  EncodedDomain.record (Nat.card (SICatalogue L Carrier)) (fun sort =>
    (EncodedDomain.boundedArray (typedColumn generators (entry sort)).outputDomain coordinates).prod
      (EncodedDomain.boundedArray (EncodedDomain.bitVectors (coordinates + 1)) coordinates))

noncomputable def packedSorts (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := packedDomain (L := L) (Carrier := Carrier) coordinates generators
  precondition _ _ := True
  compute sizes arguments sort :=
    ((packSort coordinates generators (entry sort)).compute sizes ⟨arguments.val, trivial⟩,
      (packSources coordinates generators (entry sort)).compute sizes ⟨arguments.val, trivial⟩)

theorem packedSorts_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (packedSorts (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  apply Realizable.recordOutputs
  intro sort
  exact Realizable.pairOutputs _ _ _ (fun _ _ => True) _ _
    (packSort_realizable coordinates generators (entry sort))
    (packSources_realizable coordinates generators (entry sort))

/-- Compute the shared size assignment and attach all packed fields, using
ordinary composition rather than a conversion-specific machine controller. -/
noncomputable def packedFrame (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (extendedSizeFrame (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
    (packedDomain (L := L) (Carrier := Carrier) coordinates generators)).onResults
      (packedSorts (L := L) (Carrier := Carrier) coordinates generators).inputDomains (fun _ _ => True)
      (fun choice sizes arguments => match choice with
      | false => (sizeComputation (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨(fun _ => (convertedImages (L := L) (Carrier := Carrier) coordinates generators).compute sizes
            ⟨arguments.val, trivial⟩), trivial⟩
      | true => (packedSorts (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments.val, trivial⟩)
      (by intros; trivial)

theorem packedFrame_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (packedFrame (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  apply (extendedSizeFrame_realizable (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
    (packedDomain (L := L) (Carrier := Carrier) coordinates generators)).onResults
  intro choice
  cases choice
  · exact (convertedImages_realizable coordinates generators).followedBy
      (sizeComputation_realizable coordinates generators) rfl (by intros; trivial)
  · exact packedSorts_realizable coordinates generators

/-- Expose a sort's two internal packed fields using the common record and
pair operations at renamed original sizes. -/
noncomputable def packedSortView (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    Computation (Parameter ⊕ Multisorted.Parameter (Nat.card (SICatalogue L Carrier))) Unit :=
  let column := (typedColumn generators (entry sort)).outputDomain
  let source := EncodedDomain.boundedArray (EncodedDomain.bitVectors (coordinates + 1)) coordinates
  let fields := fun sort : SortIndex (L := L) (Carrier := Carrier) =>
    (EncodedDomain.boundedArray (typedColumn generators (entry sort)).outputDomain coordinates).prod source
  (recordProjectionAtNames (Nat.card (SICatalogue L Carrier)) fields sort Sum.inl).followedBy
    (renamedPairView (EncodedDomain.boundedArray column coordinates) source Sum.inl) rfl (by intros; trivial)

theorem packedSortView_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    (packedSortView (L := L) (Carrier := Carrier) coordinates generators sort).Realizable :=
  (recordProjectionAtNames_realizable _ _ _ _).followedBy
    (renamedPairView_realizable _ _ _) rfl (by intros; trivial)

/-- Read the source coordinates at precisely the same runtime count as the
sort values. These labels are internal to dependency construction. -/
noncomputable def readPackedSources (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    Computation (Parameter ⊕ Multisorted.Parameter (Nat.card (SICatalogue L Carrier))) Unit :=
  (boundedArrayAtSize (EncodedDomain.bitVectors (coordinates + 1)) coordinates
    Sum.inl (.inr (.inl sort)) ((EncodedDomain.bitVectors (coordinates + 1)).renameParameters Sum.inl)
    (fun _ => True) (fun _ _ value => value)).onResults
      (fun _ => (packedDomain (L := L) (Carrier := Carrier) coordinates generators).renameParameters Sum.inl)
      (fun current arguments => (arguments () sort).2.1.val = current (.inr (.inl sort)))
      (fun _ _ arguments => (arguments.val () sort).2)
      (by intro current arguments; exact ⟨arguments.property, trivial⟩)

theorem readPackedSources_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    (readPackedSources (L := L) (Carrier := Carrier) coordinates generators sort).Realizable := by
  let column := (typedColumn generators (entry sort)).outputDomain
  let source := EncodedDomain.boundedArray (EncodedDomain.bitVectors (coordinates + 1)) coordinates
  have second := (packedSortView_realizable coordinates generators sort).followedBy
    (pairProjection_realizable ((EncodedDomain.boundedArray column coordinates).renameParameters Sum.inl)
      (source.renameParameters Sum.inl) true) rfl (by intros; trivial)
  apply (boundedArrayAtSize_realizable (EncodedDomain.bitVectors (coordinates + 1)) coordinates
    (Sum.inl : Parameter → Parameter ⊕ Multisorted.Parameter (Nat.card (SICatalogue L Carrier)))
    (.inr (.inl sort)) ((EncodedDomain.bitVectors (coordinates + 1)).renameParameters Sum.inl)
    (fun _ => True) (fun _ _ value => value) (by intros; exact EncodedDomain.renameParameters_bits _ _ _ _)).onResults
  intro name
  cases name
  exact second.withSpecification _ _ (by intros; trivial) (by intros; rfl)


end Polytime2.SMP.Prepared
