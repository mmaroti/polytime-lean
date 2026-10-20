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

import Polytime2.Examples.SMP.Multisorted
import Polytime2.Examples.SMP.DistinctDependencies
import Polytime2.Examples.SMP.MonolithOperations
import Polytime2.Arrays.Packing

/-! # Exact prepared coordinates from the shared packing correspondence

The fixed catalogue determines the sort family. Only multiplicities depend on
runtime input, and every retained coordinate corresponds to one actual factor.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]

abbrev SortIndex := Fin (Nat.card (SICatalogue L Carrier))

noncomputable def entry (sort : SortIndex (L := L) (Carrier := Carrier)) : SICatalogue L Carrier :=
  catalogueRank.symm sort

abbrev SortCarrier (sort : SortIndex (L := L) (Carrier := Carrier)) := SICarrier L Carrier (entry sort)

variable {coordinates generators : ℕ}

/-- A catalogue sort is active exactly at source coordinates with its image. -/
noncomputable def flags (input : Fin generators → Fin coordinates → Carrier)
    (sort : SortIndex (L := L) (Carrier := Carrier)) : Fin coordinates → Bool :=
  fun coordinate => @decide (images (L := L) input coordinate = (entry sort).1) (Classical.propDecidable _)

@[simp] theorem flags_eq_true (input : Fin generators → Fin coordinates → Carrier)
    (sort : SortIndex (L := L) (Carrier := Carrier)) (coordinate : Fin coordinates) :
    flags (L := L) input sort coordinate = true ↔ images (L := L) input coordinate = (entry sort).1 := by
  classical
  simp [flags]

/-- One actual size per fixed sort, followed by the original generator count. -/
noncomputable def sizes (input : Fin generators → Fin coordinates → Carrier) :
    Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) → ℕ :=
  Sum.elim (fun sort => ArrayPacking.count (flags (L := L) input sort)) (fun _ => generators)

theorem sort_size_le (input : Fin generators → Fin coordinates → Carrier)
    (sort : SortIndex (L := L) (Carrier := Carrier)) : sizes (L := L) input (.inl sort) ≤ coordinates :=
  ArrayPacking.count_le (flags (L := L) input sort)

/-- The exact sort-local order is the generic stable packing order. -/
noncomputable def activeCoordinates (input : Fin generators → Fin coordinates → Carrier)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    Fin (sizes (L := L) input (.inl sort)) ≃o {coordinate : Fin coordinates // images (L := L) input coordinate = (entry sort).1} :=
  (ArrayPacking.selection (flags (L := L) input sort)).trans
    { toFun := fun coordinate => ⟨coordinate.val, (flags_eq_true input sort coordinate.val).mp coordinate.property⟩
      invFun := fun coordinate => ⟨coordinate.val, (flags_eq_true input sort coordinate.val).mpr coordinate.property⟩
      left_inv := by intro coordinate; rfl
      right_inv := by intro coordinate; rfl
      map_rel_iff' := by intros; rfl }

/-- No factors are omitted or duplicated when inactive slots are removed. -/
noncomputable def coordinateFactor (input : Fin generators → Fin coordinates → Carrier) :
    Multisorted.Coordinate (sizes (L := L) input) ≃ FactorIndex (L := L) input :=
  (Equiv.sigmaCongrRight (fun sort => (activeCoordinates (L := L) input sort).toEquiv)).trans (rankedSlotEquiv (L := L) input).symm

theorem coordinateFactor_entry (input : Fin generators → Fin coordinates → Carrier)
    (coordinate : Multisorted.Coordinate (sizes (L := L) input)) :
    factorEntry (L := L) input (coordinateFactor (L := L) input coordinate) = entry coordinate.1 := by
  rcases coordinate with ⟨sort, position⟩
  apply catalogueRank.injective
  have same := congrArg Sigma.fst ((rankedSlotEquiv (L := L) input).apply_symm_apply
    ⟨sort, activeCoordinates (L := L) input sort position⟩)
  change catalogueRank (factorEntry (L := L) input ((rankedSlotEquiv (L := L) input).symm
    ⟨sort, activeCoordinates (L := L) input sort position⟩)) = sort at same
  change catalogueRank (factorEntry (L := L) input ((rankedSlotEquiv (L := L) input).symm
    ⟨sort, activeCoordinates (L := L) input sort position⟩)) = catalogueRank (entry sort)
  exact same.trans (catalogueRank.apply_symm_apply sort).symm

/-- Stable dense coordinates retain their original source-coordinate identity. -/
theorem coordinateFactor_source (input : Fin generators → Fin coordinates → Carrier)
    (coordinate : Multisorted.Coordinate (sizes (L := L) input)) :
    (coordinateFactor (L := L) input coordinate).1 =
      (activeCoordinates (L := L) input coordinate.1 coordinate.2).val := by
  rcases coordinate with ⟨sort, position⟩
  have same := congrArg (fun slot : ActiveSlot (L := L) input => slot.2.val)
    ((activeSlotEquiv (L := L) input).apply_symm_apply
      ⟨entry sort, activeCoordinates (L := L) input sort position⟩)
  change ((activeSlotEquiv (L := L) input).symm
    ⟨entry sort, activeCoordinates (L := L) input sort position⟩).1 =
      (activeCoordinates (L := L) input sort position).val at same
  exact same

/-- Transport between catalogue carriers is an algebra isomorphism. -/
noncomputable def carrierCast {first second : SICatalogue L Carrier} (equal : first = second) :
    SICarrier L Carrier first ≃[L] SICarrier L Carrier second := by
  cases equal
  exact FirstOrder.Language.Equiv.refl _ _

noncomputable def coordinateCarrier (input : Fin generators → Fin coordinates → Carrier)
    (coordinate : Multisorted.Coordinate (sizes (L := L) input)) :
    Factor input (coordinateFactor (L := L) input coordinate) ≃[L] SortCarrier coordinate.1 :=
  carrierCast (coordinateFactor_entry input coordinate)

/-- The exact multisorted product and the original factor product are
isomorphic, using only reindexing and catalogue-carrier transports. -/
noncomputable def tupleEquiv (input : Fin generators → Fin coordinates → Carrier) :
    (∀ factor, Factor (L := L) input factor) ≃[L] Multisorted.Tuple (SortCarrier (L := L) (Carrier := Carrier)) (sizes (L := L) input) := by
  let reindexed := (_root_.Equiv.piCongrLeft (fun factor => Factor (L := L) input factor) (coordinateFactor (L := L) input)).symm
  let transported := _root_.Equiv.piCongrRight (fun coordinate => (coordinateCarrier (L := L) input coordinate).toEquiv)
  let curried := _root_.Equiv.piCurry (fun sort (_ : Fin (sizes (L := L) input (.inl sort))) => SortCarrier sort)
  let equivalence := reindexed.trans (transported.trans curried)
  refine ⟨equivalence, ?_, ?_⟩
  · intro arity symbol arguments
    funext sort position
    exact (coordinateCarrier (L := L) input ⟨sort, position⟩).map_fun symbol
      (fun index => arguments index (coordinateFactor (L := L) input ⟨sort, position⟩))
  · intro arity symbol
    exact isEmptyElim symbol

/-- Runtime multiplicities agree with the previous mathematical factor counts. -/
theorem sort_size_eq_card (input : Fin generators → Fin coordinates → Carrier)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    sizes (L := L) input (.inl sort) =
      Nat.card {coordinate : Fin coordinates // images (L := L) input coordinate = (entry sort).1} :=
  (Nat.card_fin _).symm.trans (Nat.card_congr (activeCoordinates (L := L) input sort).toEquiv)

theorem total_sort_size (input : Fin generators → Fin coordinates → Carrier) :
    (∑ sort : SortIndex (L := L) (Carrier := Carrier), sizes (L := L) input (.inl sort)) =
      Nat.card (FactorIndex (L := L) input) := by
  have sigma : Nat.card (Multisorted.Coordinate (sizes (L := L) input)) =
      ∑ sort : SortIndex (L := L) (Carrier := Carrier), Nat.card (Fin (sizes (L := L) input (.inl sort))) :=
    Nat.card_sigma
  have counts : (∑ sort : SortIndex (L := L) (Carrier := Carrier), Nat.card (Fin (sizes (L := L) input (.inl sort)))) =
      ∑ sort : SortIndex (L := L) (Carrier := Carrier), sizes (L := L) input (.inl sort) := by
    simp only [Nat.card_fin]
  exact (sigma.trans counts).symm.trans (Nat.card_congr (coordinateFactor (L := L) input))

@[simp] theorem tupleEquiv_apply (input : Fin generators → Fin coordinates → Carrier)
    (tuple : ∀ factor, Factor (L := L) input factor)
    (sort : SortIndex (L := L) (Carrier := Carrier)) (position : Fin (sizes (L := L) input (.inl sort))) :
    tupleEquiv input tuple sort position =
      coordinateCarrier (L := L) input ⟨sort, position⟩ (tuple (coordinateFactor (L := L) input ⟨sort, position⟩)) := rfl

/-- Generators and target are ordinary multisorted tuples at their exact sizes. -/
noncomputable def inputData (input : Fin generators → Fin coordinates → Carrier) (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate) :
    Multisorted.Input (SortCarrier (L := L) (Carrier := Carrier)) (sizes (L := L) input) :=
  ((fun generator => tupleEquiv input (CoordinateReduction.generators (L := L) input generator)),
    tupleEquiv input (CoordinateReduction.target (L := L) input targetValue valid))

/-- Exact-size reindexing preserves and reflects the original SMP question. -/
theorem inputData_membership (input : Fin generators → Fin coordinates → Carrier) (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate) :
    Multisorted.IsMember (L := L) (inputData input targetValue valid) ↔
      targetValue ∈ Substructure.closure L (Set.range input) := by
  exact (generated_membership_iff (tupleEquiv input).toHom (tupleEquiv input).injective
    (CoordinateReduction.generators (L := L) input) (CoordinateReduction.target (L := L) input targetValue valid)).trans
    (CoordinateReduction.membership input targetValue valid)

/-- Surjectivity onto every exact output coordinate survives the reindexing. -/
theorem inputData_subdirect (input : Fin generators → Fin coordinates → Carrier) (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (sort : SortIndex (L := L) (Carrier := Carrier)) (position : Fin (sizes (L := L) input (.inl sort)))
    (value : SortCarrier sort) :
    ∃ tuple ∈ Multisorted.generated (L := L) (inputData input targetValue valid), tuple sort position = value := by
  let coordinate := (⟨sort, position⟩ : Multisorted.Coordinate (sizes (L := L) input))
  let equivalence := coordinateCarrier (L := L) input coordinate
  obtain ⟨tuple, member, equal⟩ := generators_subdirect (L := L) input
    (coordinateFactor (L := L) input coordinate) (equivalence.symm value)
  refine ⟨tupleEquiv input tuple, ?_, ?_⟩
  · exact (generated_image_iff (tupleEquiv input).toHom (CoordinateReduction.generators (L := L) input) _).mpr
      ⟨tuple, member, rfl⟩
  · change equivalence (tuple (coordinateFactor (L := L) input coordinate)) = value
    rw [equal, equivalence.apply_symm_apply]

end Polytime2.SMP.Prepared
