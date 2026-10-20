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

import Polytime2.Examples.SMP.PreparedProjection

/-! # Monolith quotient isomorphisms on exact multisorted coordinates -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {coordinates generators : ℕ}

/-- The fixed finite graph table agrees with each distinct dependency value,
even when several monolith pairs select the same dependency. -/
theorem monolithBlock_distinct
    (input : Fin generators → Fin coordinates → Carrier)
    (parent : FactorIndex (L := L) input)
    (value : Quotient (catalogueMonolith L Carrier (factorEntry input parent)).val)
    (child : CoordinateReduction.dependencySet input parent) :
    monolithBlock (factorEntry input parent) value (factorEntry input child.val) =
      some ⟨factorEntry input child.val, distinctMonolithPrefix input parent value child⟩ := by
  classical
  rcases child with ⟨child, member⟩
  obtain ⟨pair, rfl⟩ := member
  obtain ⟨parentValue, rfl⟩ :=
    quotientMap_surjective (catalogueMonolith L Carrier (factorEntry input parent)) value
  obtain ⟨source, rfl⟩ := quotientMap_surjective (factorEntry input parent).2.val parentValue
  rw [monolithBlock_source]
  rw [ite_eq_left (show factorEntry input (dependencyFactor input parent pair) ∈
    Set.range (dependencyEntry (factorEntry input parent)) from ⟨pair, rfl⟩)]
  rw [show quotientBlock (factorEntry input parent).1 source
      (factorEntry input (dependencyFactor input parent pair)) =
      some (⟨dependencyEntry (factorEntry input parent) pair,
        quotientMap (dependencyEntry (factorEntry input parent) pair).2.val source⟩ : SIValue L Carrier)
    from quotientBlock_entry (dependencyEntry (factorEntry input parent) pair) source]
  have same := congrFun (repeat_distinctMonolithPrefix input parent
    (quotientMap (catalogueMonolith L Carrier (factorEntry input parent))
      (quotientMap (factorEntry input parent).2.val source))) pair
  change distinctMonolithPrefix input parent _ ⟨dependencyFactor input parent pair, _⟩ =
    monolithPrefix (factorEntry input parent) _ pair at same
  rw [dependency_commutes] at same
  exact congrArg (fun selected => some
    (⟨factorEntry input (dependencyFactor input parent pair), selected⟩ : SIValue L Carrier)) same.symm

/-- Transport a monolith quotient along equality of its catalogue entry. -/
noncomputable def monolithCast {first second : SICatalogue L Carrier}
    (equal : first = second) :
    Quotient (catalogueMonolith L Carrier first).val ≃[L]
      Quotient (catalogueMonolith L Carrier second).val := by
  cases equal
  exact FirstOrder.Language.Equiv.refl L _

omit [Finite Carrier] in
@[simp] theorem monolithCast_quotientMap {first second : SICatalogue L Carrier}
    (equal : first = second) (value : SICarrier L Carrier first) :
    monolithCast equal (quotientMap (catalogueMonolith L Carrier first) value) =
      quotientMap (catalogueMonolith L Carrier second) (carrierCast equal value) := by
  cases equal
  rfl

/-- Read a typed value from the fixed tagged catalogue table. -/
noncomputable def graphValue (parent child : SICatalogue L Carrier)
    (value : Quotient (catalogueMonolith L Carrier parent).val) :
    Option (SICarrier L Carrier child) := by
  classical
  exact (monolithBlock parent value child).bind fun selected =>
    if equal : selected.1 = child then some (carrierCast equal selected.2) else none

private theorem graphValue_of_block (parent first second : SICatalogue L Carrier)
    (same : first = second)
    (query : Quotient (catalogueMonolith L Carrier parent).val)
    (value : SICarrier L Carrier first)
    (table : monolithBlock parent query first = some ⟨first, value⟩) :
    graphValue parent second query = some (carrierCast same value) := by
  classical
  cases same
  simp [graphValue, table, carrierCast]

private theorem graphValue_cast {first second : SICatalogue L Carrier}
    (same : first = second) (child : SICatalogue L Carrier)
    (value : Quotient (catalogueMonolith L Carrier first).val) :
    graphValue second child (monolithCast same value) = graphValue first child value := by
  cases same
  rfl

/-- A specialization-only graph lookup on the actual sort carriers. -/
noncomputable def graph (parent child : SortIndex (L := L) (Carrier := Carrier))
    (value : Quotient (catalogueMonolith L Carrier (entry parent)).val) :
    Option (SortCarrier (L := L) (Carrier := Carrier) child) :=
  graphValue (entry parent) (entry child) value

/-- The monolith quotient of each fixed sort is isomorphic to the actual
projection onto its runtime dependency coordinates. -/
noncomputable def monolithEquiv
    (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    Quotient (catalogueMonolith L Carrier (entry parent.1)).val ≃[L]
      Multisorted.projectedDependencies (L := L)
        (inputData input targetValue valid) (dependencies (L := L) input) parent :=
  (projectedEquiv input targetValue valid parent).comp
    ((projectedMonolithEquiv input (coordinateFactor (L := L) input parent)).comp
      (monolithCast (coordinateFactor_entry input parent)).symm)

/-- Transport respects the quotient of each original parent value. -/
theorem monolithEquiv_quotientMap
    (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (value : Factor input (coordinateFactor (L := L) input parent)) :
    (monolithEquiv input targetValue valid parent
      (quotientMap (catalogueMonolith L Carrier (entry parent.1))
        (coordinateCarrier (L := L) input parent value))).val =
      dependencyTupleEquiv input parent
        (distinctMonolithPrefix input (coordinateFactor (L := L) input parent)
          (quotientMap (catalogueMonolith L Carrier
            (factorEntry input (coordinateFactor (L := L) input parent))) value)) := by
  change dependencyTupleEquiv input parent
    ((projectedMonolithEquiv input (coordinateFactor (L := L) input parent)
      ((monolithCast (coordinateFactor_entry input parent)).symm
        (quotientMap (catalogueMonolith L Carrier (entry parent.1))
          (carrierCast (coordinateFactor_entry input parent) value)))).val) = _
  rw [← monolithCast_quotientMap (coordinateFactor_entry input parent) value, FirstOrder.Language.Equiv.symm_apply_apply]
  rfl

/-- The transported monolith isomorphism agrees with the fixed sort table. -/
theorem monolithEquiv_graph
    (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (value : Quotient (catalogueMonolith L Carrier (entry parent.1)).val)
    (child : dependencies (L := L) input parent) :
    some ((monolithEquiv input targetValue valid parent value).val child) =
      graph parent.1 child.val.1 value := by
  let original := (monolithCast (coordinateFactor_entry input parent)).symm value
  have same : value = monolithCast (coordinateFactor_entry input parent) original :=
    ((monolithCast (coordinateFactor_entry input parent)).apply_symm_apply value).symm
  change some (coordinateCarrier (L := L) input child.val
    (distinctMonolithPrefix input (coordinateFactor (L := L) input parent)
      original (dependencyEquiv input parent child))) =
    graphValue (entry parent.1) (entry child.val.1) value
  conv_rhs => rw [same, graphValue_cast]
  exact (graphValue_of_block _ _ _ (coordinateFactor_entry input child.val) original _
    (monolithBlock_distinct input (coordinateFactor (L := L) input parent)
      original (dependencyEquiv input parent child))).symm

/-- The full graph equation survives exact coordinate packing. The projection
is taken from the generated relation, so no ambient-product assumption is used. -/
theorem monolith_graph (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    (fun tuple : Multisorted.Tuple (SortCarrier (L := L) (Carrier := Carrier))
        (sizes (L := L) input) =>
      ((fun child : dependencies (L := L) input parent =>
        tuple child.val.1 child.val.2), tuple parent.1 parent.2)) ''
      (Multisorted.generated (L := L) (inputData input targetValue valid) : Set _) =
    {pair | pair.1 = (monolithEquiv input targetValue valid parent
      (quotientMap (catalogueMonolith L Carrier (entry parent.1)) pair.2)).val} := by
  let factor := coordinateFactor (L := L) input parent
  let parentEquiv := coordinateCarrier (L := L) input parent
  let childEquiv := dependencyTupleEquiv input parent
  have oldGraph := distinct_dependency_graph input factor
  ext pair
  constructor
  · rintro ⟨tuple, member, rfl⟩
    obtain ⟨source, sourceMember, rfl⟩ :=
      (generated_image_iff (tupleEquiv input).toHom
        (CoordinateReduction.generators (L := L) input) tuple).mp member
    have sourceGraph := (Set.ext_iff.mp oldGraph _).mp ⟨source, sourceMember, rfl⟩
    change (fun child : dependencies (L := L) input parent =>
      tupleEquiv input source child.val.1 child.val.2) = _
    rw [dependency_projection_commutes]
    change childEquiv (fun child => source child.val) =
      (monolithEquiv input targetValue valid parent
        (quotientMap (catalogueMonolith L Carrier (entry parent.1))
          (coordinateCarrier (L := L) input parent (source factor)))).val
    rw [monolithEquiv_quotientMap]
    exact congrArg childEquiv sourceGraph
  · intro graph
    let oldParent := parentEquiv.symm pair.2
    let oldChildren := childEquiv.symm pair.1
    have oldEquation : oldChildren = distinctMonolithPrefix input factor
        (quotientMap (catalogueMonolith L Carrier (factorEntry input factor)) oldParent) := by
      apply childEquiv.injective
      calc
        childEquiv oldChildren = pair.1 := childEquiv.apply_symm_apply _
        _ = (monolithEquiv input targetValue valid parent
            (quotientMap (catalogueMonolith L Carrier (entry parent.1))
              (parentEquiv oldParent))).val := by
          rw [parentEquiv.apply_symm_apply]; exact graph
        _ = _ := monolithEquiv_quotientMap input targetValue valid parent oldParent
    obtain ⟨source, sourceMember, equal⟩ :=
      (Set.ext_iff.mp oldGraph (oldChildren, oldParent)).mpr oldEquation
    refine ⟨tupleEquiv input source, ?_, ?_⟩
    · exact (generated_image_iff (tupleEquiv input).toHom
        (CoordinateReduction.generators (L := L) input) _).mpr
          ⟨source, sourceMember, rfl⟩
    · apply Prod.ext
      · change (fun child : dependencies (L := L) input parent =>
          tupleEquiv input source child.val.1 child.val.2) = pair.1
        rw [dependency_projection_commutes]
        exact (congrArg childEquiv (congrArg Prod.fst equal)).trans
          (childEquiv.apply_symm_apply pair.1)
      · change parentEquiv (source factor) = pair.2
        exact (congrArg parentEquiv (congrArg Prod.snd equal)).trans
          (parentEquiv.apply_symm_apply pair.2)

/-- The exact multisorted instance satisfies the public preparation contract,
with a specialization-only monolith and graph table. -/
theorem inputData_isPrepared
    (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier)
    (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate) :
    Multisorted.IsPrepared (L := L)
      (fun sort => catalogueMonolith L Carrier (entry sort))
      (graph (L := L) (Carrier := Carrier)) (Nat.card Carrier * Nat.card Carrier)
      (inputData input targetValue valid) (dependencies (L := L) input) := by
  refine ⟨(fun sort => catalogueMonolith_least L Carrier (entry sort)),
    catalogue_order_monotone, ?_, ?_⟩
  · intro coordinate value
    exact inputData_subdirect input targetValue valid coordinate.1 coordinate.2 value
  · intro coordinate
    exact ⟨dependencies_bound input coordinate, dependencies_earlier input coordinate,
      dependencies_simple input coordinate, monolithEquiv input targetValue valid coordinate,
      monolithEquiv_graph input targetValue valid coordinate,
      monolith_graph input targetValue valid coordinate⟩

end Polytime2.SMP.Prepared
