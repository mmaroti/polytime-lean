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

import Polytime2.Examples.SMP.PreparedCoordinates

/-! # Exact dependency masks and their fixed catalogue description

Dependency sets are transported by the same coordinate equivalence as values.
Membership reduces to a fixed catalogue lookup and equality of source indices.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {coordinates generators : ℕ}

/-- Fixed dependency sorts, viewed as one specialization lookup value. -/
noncomputable def dependencySorts (parent : SICatalogue L Carrier) : Set (SICatalogue L Carrier) :=
  Set.range (dependencyEntry parent)

omit [Finite Carrier] in
private theorem factor_eq_of_source_entry (input : Fin generators → Fin coordinates → Carrier)
    (first second : FactorIndex (L := L) input) (source : first.1 = second.1)
    (sameEntry : factorEntry (L := L) input first = factorEntry (L := L) input second) : first = second := by
  rcases first with ⟨firstIndex, firstRelation⟩
  rcases second with ⟨secondIndex, secondRelation⟩
  dsimp only at source
  subst secondIndex
  exact congrArg (Sigma.mk firstIndex) (eq_of_heq (Sigma.mk.inj sameEntry).2)

/-- The dependency relation requires no runtime algebra enumeration. Its sort
set is fixed by specialization, and dependencies retain the source coordinate. -/
theorem factor_dependency_iff (input : Fin generators → Fin coordinates → Carrier)
    (parent child : FactorIndex (L := L) input) :
    child ∈ CoordinateReduction.dependencySet input parent ↔
      child.1 = parent.1 ∧ factorEntry (L := L) input child ∈ dependencySorts (factorEntry (L := L) input parent) := by
  constructor
  · rintro ⟨pair, equal⟩
    constructor
    · rw [← equal]; rfl
    · exact ⟨pair, by rw [← equal]; rfl⟩
  · rintro ⟨source, pair, sameEntry⟩
    exact ⟨pair, factor_eq_of_source_entry input _ child source.symm sameEntry⟩

/-- Runtime masks use exact multisorted coordinates, with no inactive slots. -/
noncomputable def dependencies (input : Fin generators → Fin coordinates → Carrier) :
    Multisorted.Dependencies (sizes (L := L) input) :=
  fun sort position child childPosition => @decide
    (coordinateFactor (L := L) input ⟨child, childPosition⟩ ∈
      CoordinateReduction.dependencySet input (coordinateFactor (L := L) input ⟨sort, position⟩))
    (Classical.propDecidable _)

@[simp] theorem dependencies_mem (input : Fin generators → Fin coordinates → Carrier)
    (parent child : Multisorted.Coordinate (sizes (L := L) input)) :
    child ∈ Multisorted.dependencySet (dependencies input) parent ↔
      coordinateFactor (L := L) input child ∈ CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent) := by
  classical
  rcases parent with ⟨sort, position⟩
  rcases child with ⟨childSort, childPosition⟩
  simp [Multisorted.dependencySet, dependencies]

/-- This equation is the operational mask specification: a finite sort lookup
and source-coordinate equality, followed by the shared stable packing maps. -/
theorem dependencies_lookup (input : Fin generators → Fin coordinates → Carrier)
    (sort child : SortIndex (L := L) (Carrier := Carrier))
    (position : Fin (sizes (L := L) input (.inl sort))) (childPosition : Fin (sizes (L := L) input (.inl child))) :
    dependencies input sort position child childPosition = @decide
      ((activeCoordinates (L := L) input child childPosition).val = (activeCoordinates (L := L) input sort position).val ∧
        entry child ∈ dependencySorts (entry sort)) (Classical.propDecidable _) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [dependencies, decide_eq_true_eq, factor_dependency_iff, coordinateFactor_source, coordinateFactor_entry]

/-- The dependency subtype itself is unchanged up to the exact coordinate
bijection, so cardinality and projected algebra guarantees can be transported. -/
noncomputable def dependencyEquiv (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    Multisorted.dependencySet (dependencies input) parent ≃
      CoordinateReduction.dependencySet input (coordinateFactor (L := L) input parent) where
  toFun child := ⟨coordinateFactor (L := L) input child.val, (dependencies_mem input parent child.val).mp child.property⟩
  invFun child := ⟨(coordinateFactor (L := L) input).symm child.val,
    (dependencies_mem input parent _).mpr (by
      rw [(coordinateFactor (L := L) input).apply_symm_apply]
      exact child.property)⟩
  left_inv child := Subtype.ext ((coordinateFactor (L := L) input).symm_apply_apply child.val)
  right_inv child := Subtype.ext ((coordinateFactor (L := L) input).apply_symm_apply child.val)

theorem dependencies_bound (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input)) :
    Nat.card (Multisorted.dependencySet (dependencies input) parent) ≤ Nat.card Carrier * Nat.card Carrier :=
  (Nat.card_congr (dependencyEquiv input parent)).le.trans
    (CoordinateReduction.dependencySet_bound input (coordinateFactor (L := L) input parent))

private theorem coordinateFactor_rank (input : Fin generators → Fin coordinates → Carrier)
    (coordinate : Multisorted.Coordinate (sizes (L := L) input)) :
    catalogueRank (factorEntry (L := L) input (coordinateFactor (L := L) input coordinate)) = coordinate.1 :=
  (congrArg catalogueRank (coordinateFactor_entry input coordinate)).trans (catalogueRank.apply_symm_apply coordinate.1)

/-- Every dependency is in a strictly earlier catalogue sort; the lexicographic
coordinate order therefore agrees with the original dependency ordering. -/
theorem dependencies_earlier (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (child : Multisorted.dependencySet (dependencies input) parent) :
    toLex (child.val.1.val, child.val.2.val) < toLex (parent.1.val, parent.2.val) := by
  obtain ⟨pair, equal⟩ := (dependencies_mem input parent child.val).mp child.property
  have smaller : catalogueRank (factorEntry (L := L) input (coordinateFactor (L := L) input child.val)) <
      catalogueRank (factorEntry (L := L) input (coordinateFactor (L := L) input parent)) := by
    rw [← equal]
    exact dependency_rank_lt (factorEntry (L := L) input (coordinateFactor (L := L) input parent)) pair
  rw [coordinateFactor_rank input child.val, coordinateFactor_rank input parent] at smaller
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl smaller)

/-- Simple sorts retain the empty dependency product. -/
theorem dependencies_simple (input : Fin generators → Fin coordinates → Carrier)
    (parent : Multisorted.Coordinate (sizes (L := L) input))
    (simple : Nat.card (Congruence L (SortCarrier parent.1)) = 2) :
    Multisorted.dependencySet (dependencies input) parent = ∅ := by
  have sourceSimple : Nat.card (Congruence L (Factor input (coordinateFactor (L := L) input parent))) = 2 :=
    (congruence_count_equiv (coordinateCarrier (L := L) input parent)).trans simple
  have empty := CoordinateReduction.simple_dependencySet_empty input (coordinateFactor (L := L) input parent) sourceSimple
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro child member
  have sourceMember := (dependencies_mem input parent child).mp member
  rw [empty] at sourceMember
  exact sourceMember

end Polytime2.SMP.Prepared
