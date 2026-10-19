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

import Polytime2.Examples.SMP.Catalogue

/-! # The fixed SI catalogue is closed under monolith dependencies

Every required quotient factor is represented by the kernel of a composite map
from the same original subalgebra. Its congruence count is strictly smaller than
its parent's, so the full catalogue can be ordered once at specialization time.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier]

/-- Decompose the monolith quotient using the existing separating-pair theorem. -/
noncomputable abbrev MonolithPair (entry : SICatalogue L Carrier) :=
  SeparatingPair (Quotient (catalogueMonolith L Carrier entry).val)

/-- Dependency arity is bounded by the squared fixed algebra cardinality. -/
theorem monolithPair_bound (entry : SICatalogue L Carrier) :
    Nat.card (MonolithPair entry) ≤ Nat.card Carrier * Nat.card Carrier := by
  have imageBound : Nat.card entry.1 ≤ Nat.card Carrier :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have factorBound : Nat.card (SICarrier L Carrier entry) ≤ Nat.card entry.1 :=
    Nat.card_le_card_of_surjective (quotientMap entry.2.val) (quotientMap_surjective _)
  have quotientBound : Nat.card (Quotient (catalogueMonolith L Carrier entry).val) ≤
      Nat.card (SICarrier L Carrier entry) :=
    Nat.card_le_card_of_surjective (quotientMap (catalogueMonolith L Carrier entry))
      (quotientMap_surjective _)
  exact decomposition_factor_bound.trans
    (Nat.mul_le_mul (quotientBound.trans (factorBound.trans imageBound))
      (quotientBound.trans (factorBound.trans imageBound)))

/-- A dependency is an SI image of the same original coordinate image algebra. -/
noncomputable def dependencyMap (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    entry.1 →[L] DecompositionFactor L (Quotient (catalogueMonolith L Carrier entry).val) pair :=
  ((quotientMap (decompositionRelation pair)).comp (quotientMap (catalogueMonolith L Carrier entry))).comp
    (quotientMap entry.2.val)

theorem dependencyMap_surjective (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    Function.Surjective (dependencyMap entry pair) :=
  ((quotientMap_surjective (decompositionRelation pair)).comp
    (quotientMap_surjective (catalogueMonolith L Carrier entry))).comp (quotientMap_surjective entry.2.val)

/-- No catalogue enlargement is needed for recursive quotient factors. -/
noncomputable def dependencyEntry (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    SICatalogue L Carrier :=
  imageEntry L Carrier entry.1 (dependencyMap entry pair) (dependencyMap_surjective entry pair)
    (decomposition_si pair)

/-- Canonicalization retains an algebra isomorphism with the required factor. -/
noncomputable def dependencyEquiv (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    SICarrier L Carrier (dependencyEntry entry pair) ≃[L]
      DecompositionFactor L (Quotient (catalogueMonolith L Carrier entry).val) pair :=
  kernelEquiv (dependencyMap entry pair) (dependencyMap_surjective entry pair)

/-- All dependencies have the same coordinate image, so their slots are active
whenever their parent's slot is active. -/
theorem dependency_same_image (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    (dependencyEntry entry pair).1 = entry.1 := rfl

/-- Sorting the fixed catalogue by congruence count places every dependency
strictly before its parent; no runtime recursion or sorting is necessary. -/
theorem dependency_earlier (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    Nat.card (Congruence L (SICarrier L Carrier (dependencyEntry entry pair))) <
      Nat.card (Congruence L (SICarrier L Carrier entry)) := by
  rw [congruence_count_equiv (dependencyEquiv entry pair)]
  exact lt_of_le_of_lt (congruence_count_le (quotientMap (decompositionRelation pair))
    (quotientMap_surjective _)) (quotient_congruence_count_lt (catalogueMonolith L Carrier entry)
      (catalogueMonolith_least L Carrier entry).1)

/-- Earlier catalogue coordinates jointly encode the complete monolith quotient. -/
noncomputable def monolithPrefix (entry : SICatalogue L Carrier) :
    Quotient (catalogueMonolith L Carrier entry).val →[L]
      (∀ pair : MonolithPair entry, SICarrier L Carrier (dependencyEntry entry pair)) :=
  assemble (fun pair => (dependencyEquiv entry pair).symm.toHom.comp
    (quotientMap (decompositionRelation pair)))

theorem monolithPrefix_injective (entry : SICatalogue L Carrier) :
    Function.Injective (monolithPrefix entry) := by
  intro first second equal
  apply decomposition_injective (L := L)
  funext pair
  exact (dependencyEquiv entry pair).symm.injective (congrFun equal pair)

/-- The quotient is isomorphic to its earlier-coordinate image, using Mathlib's
existing range algebra and equivalence construction. -/
noncomputable def monolithPrefixEquiv (entry : SICatalogue L Carrier) :
    Quotient (catalogueMonolith L Carrier entry).val ≃[L] (monolithPrefix entry).range :=
  (show Quotient (catalogueMonolith L Carrier entry).val ↪[L]
      (∀ pair : MonolithPair entry, SICarrier L Carrier (dependencyEntry entry pair)) from
    { toFun := monolithPrefix entry
      inj' := monolithPrefix_injective entry
      map_fun' := (monolithPrefix entry).map_fun
      map_rel' := fun {_} symbol => isEmptyElim symbol }).equivRange

/-- Canonical quotient maps agree with the graph maps on original image values. -/
theorem dependency_commutes (entry : SICatalogue L Carrier) (pair : MonolithPair entry)
    (value : entry.1) :
    monolithPrefix entry (quotientMap (catalogueMonolith L Carrier entry) (quotientMap entry.2.val value)) pair =
      quotientMap (dependencyEntry entry pair).2.val value := by
  apply (dependencyEquiv entry pair).injective
  change (dependencyEquiv entry pair) ((dependencyEquiv entry pair).symm _) =
    kernelLift (dependencyMap entry pair) (quotientMap (kernel (dependencyMap entry pair)) value)
  rw [FirstOrder.Language.Equiv.apply_symm_apply, kernelLift_quotientMap]
  rfl

/-- Actual catalogue values satisfy the full graph equation. Each value of the
parent factor occurs, and its earlier values encode exactly its monolith class. -/
theorem dependency_graph (entry : SICatalogue L Carrier) :
    Set.range (fun value : entry.1 =>
      ((fun pair : MonolithPair entry => quotientMap (dependencyEntry entry pair).2.val value),
        quotientMap entry.2.val value)) =
      {tuple | tuple.1 = monolithPrefix entry (quotientMap (catalogueMonolith L Carrier entry) tuple.2)} := by
  ext tuple
  constructor
  · rintro ⟨value, rfl⟩
    funext pair
    exact (dependency_commutes entry pair value).symm
  · intro graph
    obtain ⟨value, equal⟩ := quotientMap_surjective entry.2.val tuple.2
    refine ⟨value, ?_⟩
    apply Prod.ext
    · rw [graph, ← equal]
      funext pair
      exact (dependency_commutes entry pair value).symm
    · exact equal

end Polytime2.SMP
