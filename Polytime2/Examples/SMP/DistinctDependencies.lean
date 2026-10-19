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

import Polytime2.Examples.SMP.CoordinateReduction

/-! # Monolith graphs indexed by distinct earlier coordinates -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.CoordinateReduction

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier Index Generator : Type} [L.Structure Carrier] [Finite Carrier]

/-- Repeating the distinct dependency coordinates is an algebra embedding. -/
noncomputable def dependencyRepeat (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    (∀ dependency : dependencySet input factor, Factor input dependency.val) ↪[L]
      (∀ pair : MonolithPair (factorEntry input factor), Factor input (dependencyFactor input factor pair)) where
  toFun := reindexProduct (Set.rangeFactorization (dependencyFactor input factor))
  inj' := reindexProduct_injective _ Set.rangeFactorization_surjective
  map_fun' := (reindexProduct (L := L) (Carrier := fun dependency : dependencySet input factor => Factor input dependency.val)
    (Set.rangeFactorization (dependencyFactor input factor))).map_fun
  map_rel' symbol := isEmptyElim symbol

/-- The quotient image already lies in the product of distinct coordinates. -/
theorem monolithPrefix_in_repeat (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input)
    (value : Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val) :
    monolithPrefix (factorEntry input factor) value ∈ (dependencyRepeat input factor).toHom.range := by
  have member : monolithPrefix (factorEntry input factor) value ∈ Set.range (monolithPrefix (factorEntry input factor)) :=
    ⟨value, rfl⟩
  rw [← generated_dependency_prefix input factor] at member
  obtain ⟨tuple, _, equal⟩ := member
  exact ⟨(fun dependency => tuple dependency.val), equal⟩

/-- The monolith quotient maps to the product indexed by the actual set J_i. -/
noncomputable def distinctMonolithPrefix (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val →[L]
      (∀ dependency : dependencySet input factor, Factor input dependency.val) :=
  liftThrough (dependencyRepeat input factor) (monolithPrefix (factorEntry input factor))
    (monolithPrefix_in_repeat input factor)

@[simp] theorem repeat_distinctMonolithPrefix (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input)
    (value : Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val) :
    dependencyRepeat input factor (distinctMonolithPrefix input factor value) =
      monolithPrefix (factorEntry input factor) value :=
  liftThrough_apply _ _ _ _

theorem distinctMonolithPrefix_injective (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    Function.Injective (distinctMonolithPrefix input factor) := by
  intro first second equal
  apply monolithPrefix_injective (factorEntry input factor)
  simpa only [repeat_distinctMonolithPrefix] using congrArg (dependencyRepeat input factor) equal

/-- The full monolith graph equation uses a set of earlier coordinates, with
no duplicate indices in its projected product. -/
theorem distinct_dependency_graph (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      ((fun dependency : dependencySet input factor => tuple dependency.val), tuple factor)) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor input factor)) =
      {tuple | tuple.1 = distinctMonolithPrefix input factor
        (quotientMap (catalogueMonolith L Carrier (factorEntry input factor)) tuple.2)} := by
  ext selected
  constructor
  · rintro ⟨tuple, generated, rfl⟩
    apply (dependencyRepeat input factor).injective
    rw [repeat_distinctMonolithPrefix]
    have member := (Set.ext_iff.mp (generated_dependency_graph input factor)
      ((fun pair => tuple (dependencyFactor input factor pair)), tuple factor)).mp
      ⟨tuple, generated, rfl⟩
    exact member
  · intro graph
    have member := (Set.ext_iff.mp (generated_dependency_graph input factor)
      (dependencyRepeat input factor selected.1, selected.2)).mpr (by
        change dependencyRepeat input factor selected.1 = _
        rw [graph, repeat_distinctMonolithPrefix])
    obtain ⟨tuple, generated, equal⟩ := member
    refine ⟨tuple, generated, ?_⟩
    apply Prod.ext
    · apply (dependencyRepeat input factor).injective
      exact congrArg Prod.fst equal
    · exact congrArg (fun point :
        (∀ pair : MonolithPair (factorEntry input factor), Factor input (dependencyFactor input factor pair)) ×
          Factor input factor => point.2) equal

/-- The range is precisely the actual earlier-coordinate projection of R. -/
theorem distinct_dependency_prefix (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      fun dependency : dependencySet input factor => tuple dependency.val) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor input factor)) =
      Set.range (distinctMonolithPrefix input factor) := by
  have graph := congrArg (Set.image Prod.fst) (distinct_dependency_graph input factor)
  rw [Set.image_image] at graph
  exact graph.trans (graph_projection_range _
    (quotientMap_surjective (catalogueMonolith L Carrier (factorEntry input factor))) _)

/-- The actual projected subalgebra on the distinct dependency coordinates. -/
noncomputable def projectedDependencies (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :=
  (Substructure.closure L (Set.range (generators (L := L) input))).map
    (reindexProduct (L := L) (Carrier := fun factor => Factor input factor)
      (fun dependency : dependencySet input factor => dependency.val))

theorem projectedDependencies_eq_range (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    projectedDependencies input factor = (distinctMonolithPrefix input factor).range := by
  apply SetLike.coe_injective
  exact distinct_dependency_prefix input factor

/-- The monolith quotient is isomorphic to the actual projection of R onto J_i. -/
noncomputable def projectedMonolithEquiv (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val ≃[L]
      projectedDependencies input factor where
  toEquiv := Equiv.ofBijective
    (fun value => ⟨distinctMonolithPrefix input factor value, by
      rw [projectedDependencies_eq_range]
      exact ⟨value, rfl⟩⟩)
    ⟨(by intro first second equal; exact distinctMonolithPrefix_injective input factor (congrArg Subtype.val equal)),
      (by
        intro value
        have member : value.val ∈ (distinctMonolithPrefix input factor).range := by
          simpa only [projectedDependencies_eq_range] using value.property
        obtain ⟨source, equal⟩ := member
        exact ⟨source, Subtype.ext equal⟩)⟩
  map_fun' symbol arguments := Subtype.ext ((distinctMonolithPrefix input factor).map_fun symbol arguments)
  map_rel' symbol := isEmptyElim symbol

@[simp] theorem projectedMonolithEquiv_apply (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input)
    (value : Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val) :
    (projectedMonolithEquiv input factor value : ∀ dependency : dependencySet input factor, Factor input dependency.val) =
      distinctMonolithPrefix input factor value := rfl

end Polytime2.SMP.CoordinateReduction
