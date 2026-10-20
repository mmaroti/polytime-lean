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

import Polytime2.Examples.SMP.PreparedDependencies

/-! # Transporting the generated dependency projection to exact coordinates -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {coordinates generators : ℕ}

/-- The same coordinate and carrier transports give an algebra isomorphism on
the product indexed by the actual distinct dependencies. -/
noncomputable def dependencyTupleEquiv (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    (∀ child : CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent), Factor input child.val) ≃[L]
      (∀ child : Multisorted.dependencySet (dependencies (L := L) input) parent, SortCarrier (L := L) (Carrier := Carrier) child.val.1) := by
  let reindexed := (_root_.Equiv.piCongrLeft
    (fun child : CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent) => Factor input child.val)
    (dependencyEquiv (L := L) input parent)).symm
  let transported := _root_.Equiv.piCongrRight (fun child : Multisorted.dependencySet (dependencies (L := L) input) parent => (coordinateCarrier (L := L) input child.val).toEquiv)
  refine ⟨reindexed.trans transported, ?_, ?_⟩
  · intro arity symbol arguments
    funext child
    exact (coordinateCarrier (L := L) input child.val).map_fun symbol
      (fun index => arguments index (dependencyEquiv input parent child))
  · intro arity symbol
    exact isEmptyElim symbol

@[simp] theorem dependencyTupleEquiv_apply (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (tuple : ∀ child : CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent), Factor input child.val)
    (child : Multisorted.dependencySet (dependencies (L := L) input) parent) :
    dependencyTupleEquiv input parent tuple child =
      coordinateCarrier (L := L) input child.val (tuple (dependencyEquiv input parent child)) := rfl

/-- Projection commutes with the full tuple reindexing. -/
theorem dependency_projection_commutes (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) (tuple : ∀ factor, Factor (L := L) input factor) :
    (fun child : Multisorted.dependencySet (dependencies (L := L) input) parent =>
      tupleEquiv input tuple child.val.1 child.val.2) =
      dependencyTupleEquiv input parent
        (fun child : CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent) => tuple child.val) := by
  funext child
  rcases child with ⟨⟨sort, position⟩, member⟩
  rfl

/-- The projected subalgebra is the transported original projection, rather
than the whole ambient dependency product. -/
theorem projectedDependencies_eq_map (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier) (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    Multisorted.projectedDependencies (L := L) (inputData input targetValue valid) (dependencies (L := L) input) parent =
      (CoordinateReduction.projectedDependencies input (coordinateFactor (L := L) input parent)).map
        (dependencyTupleEquiv input parent).toHom := by
  let oldProjection := fun (tuple : ∀ factor, Factor (L := L) input factor) =>
    fun child : CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent) => tuple child.val
  let newProjection := fun (tuple : Multisorted.Tuple (SortCarrier (L := L) (Carrier := Carrier)) (sizes (L := L) input)) =>
    fun child : Multisorted.dependencySet (dependencies (L := L) input) parent => tuple child.val.1 child.val.2
  apply SetLike.ext
  intro value
  change (∃ tuple ∈ Multisorted.generated (L := L) (inputData input targetValue valid), newProjection tuple = value) ↔
    ∃ selected ∈ CoordinateReduction.projectedDependencies input (coordinateFactor (L := L) input parent),
      dependencyTupleEquiv input parent selected = value
  constructor
  · rintro ⟨tuple, member, equal⟩
    obtain ⟨source, sourceMember, sourceEqual⟩ :=
      (generated_image_iff (tupleEquiv input).toHom (CoordinateReduction.generators (L := L) input) tuple).mp member
    subst tuple
    refine ⟨oldProjection source, ⟨source, sourceMember, rfl⟩, ?_⟩
    exact (dependency_projection_commutes input parent source).symm.trans equal
  · rintro ⟨selected, member, equal⟩
    obtain ⟨source, sourceMember, projected⟩ := member
    refine ⟨tupleEquiv input source, ?_, ?_⟩
    · exact (generated_image_iff (tupleEquiv input).toHom (CoordinateReduction.generators (L := L) input) _).mpr
        ⟨source, sourceMember, rfl⟩
    · calc
        newProjection (tupleEquiv input source) = dependencyTupleEquiv input parent (oldProjection source) :=
          dependency_projection_commutes input parent source
        _ = dependencyTupleEquiv input parent selected := congrArg (dependencyTupleEquiv input parent) projected
        _ = value := equal

/-- Restrict the dependency-product isomorphism to its generated projections. -/
noncomputable def projectedEquiv (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier) (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    CoordinateReduction.projectedDependencies input (coordinateFactor (L := L) input parent) ≃[L]
      Multisorted.projectedDependencies (L := L) (inputData input targetValue valid) (dependencies (L := L) input) parent := by
  let equivalence := dependencyTupleEquiv input parent
  have membership value :
      value ∈ CoordinateReduction.projectedDependencies input (coordinateFactor (L := L) input parent) ↔
      equivalence value ∈ Multisorted.projectedDependencies (L := L) (inputData input targetValue valid) (dependencies (L := L) input) parent := by
    rw [projectedDependencies_eq_map]
    constructor
    · intro member; exact ⟨value, member, rfl⟩
    · rintro ⟨source, member, equal⟩
      exact equivalence.injective equal ▸ member
  refine ⟨equivalence.toEquiv.subtypeEquiv membership, ?_, ?_⟩
  · intro arity symbol arguments
    apply Subtype.ext
    exact equivalence.map_fun symbol (fun index => (arguments index).val)
  · intro arity symbol
    exact isEmptyElim symbol

@[simp] theorem projectedEquiv_apply (input : Fin generators → Fin coordinates → Carrier)
    (targetValue : Fin coordinates → Carrier) (valid : ∀ coordinate, targetValue coordinate ∈ images (L := L) input coordinate)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (tuple : CoordinateReduction.projectedDependencies input (coordinateFactor (L := L) input parent)) :
    (projectedEquiv input targetValue valid parent tuple).val = dependencyTupleEquiv input parent tuple.val := rfl

end Polytime2.SMP.Prepared
