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

import Polytime2.Examples.SMP.CountedConversion

/-! # Fixed catalogue order for the converted coordinate data

Each catalogue sort has one polynomial-capacity coordinate array. Inactive
positions remain explicit; the original coordinate index is the sort-local
slot, so no runtime permutation or input-dependent size assignment is needed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Select one fixed catalogue slot, preserving an outside-image rejection. -/
noncomputable def selectSort (entry : SICatalogue L Carrier) : Computation Empty Unit :=
  finiteOperation (fun _ => elementDomain (Option (SIBlock L Carrier)))
    (elementDomain (Option (SIValue L Carrier)))
    (fun _ values => (values ()).bind (fun block => block entry))

theorem selectSort_realizable (entry : SICatalogue L Carrier) : (selectSort entry).Realizable :=
  finiteOperation_realizable _ _ _

/-- A single coordinate supplies the selected sort's target and generator column. -/
noncomputable def coordinateSort (generators : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    Computation Parameter Unit where
  inputDomains _ := (coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain
  outputDomain := (elementDomain (Option (SIValue L Carrier))).constant.prod
    ((elementDomain (Option (SIValue L Carrier))).constant.arrayOfLength generators)
  precondition _ _ := True
  compute _ arguments :=
    ((arguments.val ()).2.1.bind (fun block => block entry),
      fun index => ((arguments.val ()).2.2 index).bind (fun block => block entry))

theorem coordinateSort_realizable (generators : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    (coordinateSort generators entry).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let block : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let value : EncodedDomain Parameter := (elementDomain (Option (SIValue L Carrier))).constant
  let payload := block.prod (block.arrayOfLength generators)
  have select := (selectSort_realizable entry).withConstantSizes (Parameter := Parameter)
  have target := ((pairProjection_realizable image payload true).followedBy
    (pairProjection_realizable block (block.arrayOfLength generators) false) rfl (by intros; trivial)).followedBy
      select rfl (by intros; trivial)
  have mapped := mapArray_realizable block value generators
    (fun _ values => values.bind (fun block => block entry)) select
  have columns := ((pairProjection_realizable image payload true).followedBy
    (pairProjection_realizable block (block.arrayOfLength generators) true) rfl (by intros; trivial)).followedBy
      mapped rfl (by intros; trivial)
  exact Realizable.pairOutputs (coordinateSort generators entry).inputDomains value
    (value.arrayOfLength generators) (fun _ _ => True) _ _ target columns

/-- All coordinate slots for one sort, in original coordinate order. -/
noncomputable def sortCoordinates (coordinates generators : MvPolynomial Parameter ℕ)
    (entry : SICatalogue L Carrier) : Computation Parameter Unit :=
  mapArray ((coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain)
    (coordinateSort generators entry).outputDomain coordinates
    (fun sizes value => (coordinateSort generators entry).compute sizes ⟨(fun _ => value), trivial⟩)

theorem sortCoordinates_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (entry : SICatalogue L Carrier) : (sortCoordinates coordinates generators entry).Realizable :=
  mapArray_realizable _ _ _ _ (coordinateSort_realizable generators entry)

/-- Sort arrays occur in the fixed nondecreasing congruence-count order. -/
noncomputable def orderedCoordinates (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := EncodedDomain.record (Nat.card (SICatalogue L Carrier))
    (fun _ => ((elementDomain (Option (SIValue L Carrier))).constant.prod
      ((elementDomain (Option (SIValue L Carrier))).constant.arrayOfLength generators)).arrayOfLength coordinates)
  precondition _ _ := True
  compute sizes arguments := fun rank =>
    (sortCoordinates coordinates generators ((catalogueRank (L := L) (Carrier := Carrier)).symm rank)).compute sizes ⟨arguments.val, trivial⟩

theorem orderedCoordinates_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (orderedCoordinates (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  Realizable.recordOutputs _ _ _ _ _ (fun rank => sortCoordinates_realizable coordinates generators (catalogueRank.symm rank))

/-- Acceptance remains explicit even when an image has no nontrivial SI sort. -/
noncomputable def coordinateAccepted (generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain
  outputDomain := EncodedDomain.booleans.constant
  precondition _ _ := True
  compute _ arguments := (arguments.val ()).2.1.isSome

theorem coordinateAccepted_realizable (generators : MvPolynomial Parameter ℕ) :
    (coordinateAccepted (L := L) (Carrier := Carrier) generators).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let block : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let payload := block.prod (block.arrayOfLength generators)
  have target := (pairProjection_realizable image payload true).followedBy
    (pairProjection_realizable block (block.arrayOfLength generators) false) rfl (by intros; trivial)
  exact target.followedBy ((finitePredicate_realizable (elementDomain (Option (SIBlock L Carrier)))
    (fun _ value => value.isSome)).withConstantSizes (Parameter := Parameter)) rfl (by intros; trivial)

/-- Keep one target-acceptance bit per original coordinate. -/
noncomputable def conversionAcceptance (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  mapArray ((coordinateAccepted (L := L) (Carrier := Carrier) generators).inputDomains ())
    EncodedDomain.booleans.constant coordinates
    (fun sizes value => (coordinateAccepted (L := L) (Carrier := Carrier) generators).compute sizes
      ⟨(fun _ => value), trivial⟩)

theorem conversionAcceptance_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (conversionAcceptance (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  mapArray_realizable _ _ _ _ (coordinateAccepted_realizable generators)

/-- Organize already converted data, retaining acceptance flags and exact counts. -/
noncomputable def organizeConversion (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := (conversionAcceptance (L := L) (Carrier := Carrier) coordinates generators).outputDomain.prod
    ((orderedCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain.prod
      (convertedCounts (L := L) (Carrier := Carrier) coordinates generators).outputDomain)
  precondition _ _ := True
  compute sizes arguments :=
    ((conversionAcceptance (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩,
      ( (orderedCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩,
        (convertedCounts (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩))

theorem organizeConversion_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (organizeConversion (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  have data := Realizable.pairOutputs _ _ _ (fun _ _ => True) _ _
    (orderedCoordinates_realizable (L := L) (Carrier := Carrier) coordinates generators)
    (convertedCounts_realizable coordinates generators)
  exact Realizable.pairOutputs _ _ _ (fun _ _ => True) _ _
    (conversionAcceptance_realizable coordinates generators) data

/-- An ordered padded instance, counts, and rejection flags at the original sizes. -/
noncomputable def orderedConversion (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (organizeConversion coordinates generators) rfl (by intros; trivial)

theorem orderedConversion_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertAllCoordinates_realizable coordinates generators).followedBy
    (organizeConversion_realizable coordinates generators) rfl (by intros; trivial)

/-- Acceptance is exactly membership in the generated coordinate image. -/
theorem orderedConversion_accepted (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (coordinate : Fin (MvPolynomial.eval sizes coordinates)) :
    ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).1 coordinate = true ↔
      conversionTarget coordinates generators sizes arguments coordinate ∈
        CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate := by
  change (checkedQuotientBlock _ _).isSome = true ↔ _
  simp only [Option.isSome_iff_ne_none, ne_eq, checkedQuotientBlock_none, not_not]
  rfl

/-- Any false acceptance bit supplies an original-coordinate nonmembership witness. -/
theorem orderedConversion_reject (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (rejected : ((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).1 coordinate = false) :
    conversionTarget coordinates generators sizes arguments ∉
      Substructure.closure (M := Fin (MvPolynomial.eval sizes coordinates) → Carrier) L
        (Set.range (conversionGenerators coordinates generators sizes arguments)) := by
  apply coordinate_obstruction _ _ coordinate
  intro member
  have accepted := (orderedConversion_accepted coordinates generators sizes arguments coordinate).mpr member
  rw [rejected] at accepted
  contradiction

/-- Sort ordering preserves every active generator's actual quotient value. -/
theorem orderedConversion_generator (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (generator : Fin (MvPolynomial.eval sizes generators))
    (factor : CoordinateReduction.FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments)) :
    (((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2.1 (catalogueRank (CoordinateReduction.factorEntry _ factor)) factor.1).2 generator =
      some ⟨CoordinateReduction.factorEntry _ factor,
        CoordinateReduction.generators (L := L) (conversionGenerators coordinates generators sizes arguments) generator factor⟩ := by
  change Option.bind
    (((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ factor.1).2.2 generator)
    (fun block : SIBlock L Carrier => block (catalogueRank.symm (catalogueRank (CoordinateReduction.factorEntry _ factor)))) = _
  rw [Equiv.symm_apply_apply, convertAllCoordinates_generator_blocks]
  exact quotientBlock_entry (CoordinateReduction.factorEntry _ factor) _

/-- Sort ordering preserves every accepted target's actual quotient value. -/
theorem orderedConversion_target (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
    (factor : CoordinateReduction.FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments)) :
    (((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2.1 (catalogueRank (CoordinateReduction.factorEntry _ factor)) factor.1).1 =
      some ⟨CoordinateReduction.factorEntry _ factor,
        CoordinateReduction.target (L := L) (conversionGenerators coordinates generators sizes arguments)
          (conversionTarget coordinates generators sizes arguments) valid factor⟩ := by
  let input := conversionGenerators (L := L) coordinates generators sizes arguments
  let value : CoordinateReduction.images (L := L) input factor.1 :=
    ⟨conversionTarget coordinates generators sizes arguments factor.1, valid factor.1⟩
  change Option.bind (checkedQuotientBlock _ value.val)
    (fun block => block (catalogueRank.symm (catalogueRank (CoordinateReduction.factorEntry _ factor)))) = _
  rw [Equiv.symm_apply_apply, checkedQuotientBlock_of_mem]
  exact quotientBlock_entry (CoordinateReduction.factorEntry _ factor) value

/-- Every rank-ordered count remains exact after organizing the payload. -/
theorem orderedConversion_count (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (rank : Fin (Nat.card (SICatalogue L Carrier))) :
    (((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2.2 rank).toNat =
      (List.ofFn (fun coordinate => @decide
        (CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate =
          ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) (Classical.propDecidable _))).count true :=
  catalogueCount_correct coordinates (catalogueRank.symm rank) sizes _

/-- Stored sort counts sum to the exact number of mathematical SI factors. -/
theorem orderedConversion_total_count (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    (∑ rank : Fin (Nat.card (SICatalogue L Carrier)),
      (((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
        ⟨arguments, trivial⟩).2.2 rank).toNat) =
      Nat.card (CoordinateReduction.FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments)) := by
  rw [CoordinateReduction.factor_count_eq]
  apply Finset.sum_congr rfl
  intro rank member
  rw [orderedConversion_count, count_flags_card]
  simp only [decide_eq_true_eq]

/-- In an accepted instance, active ordered slots are exactly the ranked factor
positions of `rankedSlotEquiv`, including empty generator families. -/
theorem orderedConversion_active (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (orderedConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
    (rank : Fin (Nat.card (SICatalogue L Carrier)))
    (coordinate : Fin (MvPolynomial.eval sizes coordinates)) :
    ((((orderedConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2.1 rank coordinate).1).isSome = true ↔
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate =
        ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1 := by
  let input := conversionGenerators (L := L) coordinates generators sizes arguments
  let value : CoordinateReduction.images (L := L) input coordinate :=
    ⟨conversionTarget coordinates generators sizes arguments coordinate, valid coordinate⟩
  change ((checkedQuotientBlock _ value.val).bind
    (fun block => block ((catalogueRank (L := L) (Carrier := Carrier)).symm rank))).isSome = true ↔ _
  rw [checkedQuotientBlock_of_mem]
  exact quotientBlock_active _ value _

theorem orderedConversion_tm0 :
    (orderedConversion (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (orderedConversion_realizable _ _).tm0

end Polytime2.SMP
