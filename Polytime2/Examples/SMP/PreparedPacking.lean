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

import Polytime2.Examples.SMP.PreparedCounts
import Polytime2.Examples.SMP.ConversionData
import Polytime2.Arrays.PackingResult
import Polytime2.Arrays.Indices
import Polytime2.Computation.ComputedFrame

/-! # Certified stable packing of typed SMP sort columns

Inactive slots are internal to conversion. Packing retains precisely the active
columns, with the target and all generators sharing one selection order.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {Parameter : Type} [Fintype Parameter]

omit [Finite Carrier] in
private theorem sortCarrier_nonempty (selected : SICatalogue L Carrier) :
    Nonempty (SICarrier L Carrier selected) := by
  classical
  by_contra empty
  have : IsEmpty (SICarrier L Carrier selected) := not_nonempty_iff.mp empty
  apply (catalogueMonolith_least L Carrier selected).1
  apply Setoid.ext
  intro value
  exact isEmptyElim value

/-- Invalid slots have an arbitrary specialization-only value. They never
appear in an accepted packed result. -/
noncomputable def slotValue (selected : SICatalogue L Carrier)
    (slot : Option (SIValue L Carrier)) : SICarrier L Carrier selected := by
  classical
  exact match slot with
    | some value => if same : value.1 = selected then carrierCast same value.2
      else Classical.choice (sortCarrier_nonempty selected)
    | none => Classical.choice (sortCarrier_nonempty selected)

omit [Finite Carrier] in
@[simp] theorem slotValue_some (selected : SICatalogue L Carrier)
    (value : SICarrier L Carrier selected) : slotValue selected (some ⟨selected, value⟩) = value := by
  classical
  simp [slotValue, carrierCast]

/-- Apply the sort's fixed lookup to both the target and every generator,
without constructing an intermediate array of tagged sort values. -/
noncomputable def typedColumn (generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : Computation Parameter Unit :=
  coordinateBlockMap generators (elementDomain (SICarrier L Carrier selected))
    (fun _ block => slotValue selected (block.bind (fun values => values selected)))

theorem typedColumn_realizable (generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : (typedColumn generators selected).Realizable :=
  coordinateBlockMap_realizable _ _ _

/-- Typed columns are packed directly from the shared coordinate conversion. -/
noncomputable def sortColumns (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : Computation Parameter Unit :=
  mapArray ((coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain)
    (typedColumn generators selected).outputDomain coordinates
    (fun sizes value => (typedColumn generators selected).compute sizes ⟨(fun _ => value), trivial⟩)

theorem sortColumns_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : (sortColumns coordinates generators selected).Realizable :=
  mapArray_realizable _ _ _ _ (typedColumn_realizable generators selected)

/-- Pack all data for one sort with the catalogue's common coordinate mask. -/
noncomputable def packSort (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : Computation Parameter Unit :=
  (arrayPack (typedColumn generators selected).outputDomain coordinates).onResults
    (sortColumns coordinates generators selected).inputDomains (fun _ _ => True)
    (fun choice sizes arguments => match choice with
    | true => (sortColumns coordinates generators selected).compute sizes ⟨arguments.val, trivial⟩
    | false => (catalogueFlags coordinates selected).compute sizes
        ⟨(fun _ => (convertedImages (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments.val, trivial⟩), trivial⟩)
    (by intros; trivial)

theorem packSort_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : (packSort coordinates generators selected).Realizable := by
  apply (arrayPack_realizable (typedColumn generators selected).outputDomain coordinates).onResults
  intro choice
  cases choice
  · exact (convertedImages_realizable coordinates generators).followedBy
      (catalogueFlags_realizable coordinates selected) rfl (by intros; trivial)
  · exact sortColumns_realizable coordinates generators selected

/-- A selected padded generator slot is already the actual quotient value. -/
theorem sortColumns_generator_factor (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (factor : FactorIndex (L := L) (conversionGenerators coordinates generators hostSizes arguments))
    (selected : SICatalogue L Carrier) (same : factorEntry _ factor = selected)
    (generator : Fin (MvPolynomial.eval hostSizes generators)) :
    (((sortColumns coordinates generators selected).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩) factor.1).2 generator =
      carrierCast same (CoordinateReduction.generators (L := L)
        (conversionGenerators coordinates generators hostSizes arguments) generator factor) := by
  subst selected
  change slotValue (factorEntry _ factor)
    ((((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨arguments, trivial⟩ factor.1).2.2 generator).bind
        (fun block => block (factorEntry _ factor))) = _
  rw [convertAllCoordinates_generator_blocks]
  simp only [Option.bind_some]
  change slotValue (factorEntry _ factor)
    (quotientBlock (factorEntry _ factor).1
      (restricted (L := L) (conversionGenerators coordinates generators hostSizes arguments) generator factor.1)
      (factorEntry _ factor)) =
    quotientMap (factorEntry _ factor).2.val
      (restricted (L := L) (conversionGenerators coordinates generators hostSizes arguments) generator factor.1)
  rw [quotientBlock_entry, slotValue_some]

/-- Each packed count is exactly its mathematical sort multiplicity. -/
theorem packSort_count (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (sort : SortIndex (L := L) (Carrier := Carrier)) :
    ((packSort coordinates generators (entry sort)).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩).1.val =
      sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl sort) := rfl

/-- Packing preserves the exact public generator tuples and their order. -/
theorem packSort_generator (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (sort : SortIndex (L := L) (Carrier := Carrier))
    (position : Fin (sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl sort)))
    (generator : Fin (MvPolynomial.eval hostSizes generators)) :
    ((((packSort coordinates generators (entry sort)).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩).2 position).2 generator) =
      tupleEquiv (conversionGenerators coordinates generators hostSizes arguments)
        (CoordinateReduction.generators (L := L)
          (conversionGenerators coordinates generators hostSizes arguments) generator) sort position := by
  let input := conversionGenerators (L := L) coordinates generators hostSizes arguments
  let factor := coordinateFactor (L := L) input ⟨sort, position⟩
  have sameSource := coordinateFactor_source (L := L) input ⟨sort, position⟩
  have selected := sortColumns_generator_factor coordinates generators hostSizes arguments factor
    (entry sort) (coordinateFactor_entry input ⟨sort, position⟩) generator
  rw [sameSource] at selected
  exact selected

/-- Every accepted target slot is the actual quotient of the original target. -/
theorem sortColumns_target_factor (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate)
    (factor : FactorIndex (L := L) (conversionGenerators coordinates generators hostSizes arguments))
    (selected : SICatalogue L Carrier) (same : factorEntry _ factor = selected) :
    (((sortColumns coordinates generators selected).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩) factor.1).1 =
      carrierCast same (CoordinateReduction.target (L := L)
        (conversionGenerators coordinates generators hostSizes arguments)
        (conversionTarget coordinates generators hostSizes arguments) valid factor) := by
  subst selected
  let value : (factorEntry (L := L)
      (conversionGenerators coordinates generators hostSizes arguments) factor).1 :=
    ⟨conversionTarget coordinates generators hostSizes arguments factor.1, valid factor.1⟩
  change slotValue (factorEntry _ factor)
    ((checkedQuotientBlock (factorEntry _ factor).1 value.val).bind
      (fun block => block (factorEntry _ factor))) = _
  rw [checkedQuotientBlock_of_mem _ value]
  simp only [Option.bind_some]
  change slotValue (factorEntry _ factor)
    (quotientBlock (factorEntry _ factor).1 value (factorEntry _ factor)) =
      quotientMap (factorEntry _ factor).2.val value
  rw [quotientBlock_entry, slotValue_some]

/-- Packing preserves the target in the same exact coordinate order as the
generators, whenever every original target coordinate belongs to its image. -/
theorem packSort_target (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators hostSizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators hostSizes arguments) coordinate)
    (sort : SortIndex (L := L) (Carrier := Carrier))
    (position : Fin (sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl sort))) :
    (((packSort coordinates generators (entry sort)).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩).2 position).1 =
      (inputData (conversionGenerators coordinates generators hostSizes arguments)
        (conversionTarget coordinates generators hostSizes arguments) valid).2 sort position := by
  let input := conversionGenerators (L := L) coordinates generators hostSizes arguments
  let factor := coordinateFactor (L := L) input ⟨sort, position⟩
  have sameSource := coordinateFactor_source (L := L) input ⟨sort, position⟩
  have selected := sortColumns_target_factor coordinates generators hostSizes arguments valid factor
    (entry sort) (coordinateFactor_entry input ⟨sort, position⟩)
  rw [sameSource] at selected
  exact selected

/-- Retain original source coordinates in the same order as the packed values.
These internal arrays let dependency masks compare original coordinates. -/
noncomputable def packSources (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : Computation Parameter Unit :=
  (arrayPack (EncodedDomain.bitVectors (coordinates + 1)) coordinates).onResults
    (sortColumns coordinates generators selected).inputDomains (fun _ _ => True)
    (fun choice sizes arguments => match choice with
    | true => (arrayIndices coordinates).compute sizes ⟨(fun impossible => impossible.elim), trivial⟩
    | false => (catalogueFlags coordinates selected).compute sizes
        ⟨(fun _ => (convertedImages (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments.val, trivial⟩), trivial⟩)
    (by intros; trivial)

theorem packSources_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (selected : SICatalogue L Carrier) : (packSources coordinates generators selected).Realizable := by
  apply (arrayPack_realizable (EncodedDomain.bitVectors (coordinates + 1)) coordinates).onResults
  intro choice
  cases choice
  · exact (convertedImages_realizable coordinates generators).followedBy
      (catalogueFlags_realizable coordinates selected) rfl (by intros; trivial)
  · exact (arrayIndices_realizable coordinates).onResults _ (fun _ _ => True)
      (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)

/-- Stored source labels are exactly the coordinates used by the mathematical
dependency lookup, with no modular overflow. -/
theorem packSources_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (sort : SortIndex (L := L) (Carrier := Carrier))
    (position : Fin (sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl sort))) :
    (((packSources coordinates generators (entry sort)).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩).2 position).toNat =
      (activeCoordinates (L := L) (conversionGenerators coordinates generators hostSizes arguments) sort position).val.val := by
  change (BitVec.ofNat (MvPolynomial.eval hostSizes (coordinates + 1))
    (activeCoordinates (L := L) (conversionGenerators coordinates generators hostSizes arguments) sort position).val.val).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact ((activeCoordinates (L := L) (conversionGenerators coordinates generators hostSizes arguments)
    sort position).val.isLt.trans (Nat.lt_succ_self _)).trans (by
      simpa only [map_add, map_one] using
        (Nat.lt_two_pow_self (n := MvPolynomial.eval hostSizes coordinates + 1)))

end Polytime2.SMP.Prepared
