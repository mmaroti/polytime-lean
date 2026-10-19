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

import Polytime2.Examples.SMP.CatalogueOrder

/-! # Mathematical conversion from an SMP instance to subdirect SI factors -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.CoordinateReduction

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier Index Generator : Type} [L.Structure Carrier] [Finite Carrier]

/-- The actual generated image in one input coordinate. -/
def images (input : Generator → Index → Carrier) (index : Index) : L.Substructure Carrier :=
  Substructure.closure L (Set.range (fun generator => input generator index))

/-- Original generators, restricted to their proved coordinate images. -/
def restricted (input : Generator → Index → Carrier) (generator : Generator)
    (index : Index) : images (L := L) input index :=
  ⟨input generator index, Substructure.subset_closure ⟨generator, rfl⟩⟩

omit [L.IsAlgebraic] [Finite Carrier] in
/-- Each restricted column generates its entire coordinate algebra. -/
theorem images_full (input : Generator → Index → Carrier) (index : Index) :
    Substructure.closure L (Set.range (fun generator => restricted (L := L) input generator index)) = ⊤ := by
  let image := images (L := L) input index
  apply Substructure.map_injective_of_injective (f := image.subtype.toHom) Subtype.val_injective
  rw [Substructure.map_closure, ← Set.range_comp]
  change images (L := L) input index = (⊤ : L.Substructure image).map image.subtype.toHom
  apply SetLike.ext
  intro value
  constructor
  · intro member; exact ⟨⟨value, member⟩, trivial, rfl⟩
  · rintro ⟨point, _, rfl⟩; exact point.property

omit [Finite Carrier] in
/-- Restricting to coordinate images makes the generated relation subdirect. -/
theorem restricted_subdirect (input : Generator → Index → Carrier) :
    IsSubdirect (Substructure.closure L (Set.range (restricted (L := L) input)) :
      Set (∀ index, images (L := L) input index)) :=
  generated_subdirect _ (images_full input)

/-- The inclusion back into the original product is an algebra homomorphism. -/
def inclusion (input : Generator → Index → Carrier) :
    (∀ index, images (L := L) input index) →[L] (Index → Carrier) :=
  assemble (fun index => (images (L := L) input index).subtype.toHom.comp (projection index))

omit [Finite Carrier] in
theorem inclusion_injective (input : Generator → Index → Carrier) :
    Function.Injective (inclusion (L := L) input) := by
  intro first second equal
  funext index
  exact Subtype.ext (congrFun equal index)

/-- Each image activates all its SI quotients in the fixed catalogue. -/
abbrev FactorIndex (input : Generator → Index → Carrier) :=
  Σ index, {relation : Congruence L (images (L := L) input index) //
    IsSubdirectlyIrreducible L (Quotient relation.val)}

noncomputable abbrev Factor (input : Generator → Index → Carrier) (factor : FactorIndex (L := L) input) :=
  Quotient factor.2.val.val

/-- The mathematical factor has precisely the tag used by the encoded block. -/
def factorEntry (input : Generator → Index → Carrier) (factor : FactorIndex (L := L) input) :
    SICatalogue L Carrier := ⟨images (L := L) input factor.1, factor.2⟩

/-- The quotient maps are applied to the corresponding original coordinates. -/
noncomputable def embedding (input : Generator → Index → Carrier) :
    (∀ index, images (L := L) input index) →[L] (∀ factor, Factor (L := L) input factor) :=
  assemble (fun factor => (quotientMap factor.2.val).comp (projection factor.1))

theorem embedding_injective (input : Generator → Index → Carrier) :
    Function.Injective (embedding (L := L) input) := by
  intro first second equal
  funext index
  apply decomposition_injective (L := L) (Carrier := images (L := L) input index)
  funext pair
  exact congrFun equal ⟨index, decompositionRelation pair, decomposition_si pair⟩

omit [Finite Carrier] in
/-- Every output factor is proved SI, rather than merely marked by a tag. -/
theorem factors_si (input : Generator → Index → Carrier) (factor : FactorIndex (L := L) input) :
    IsSubdirectlyIrreducible L (Factor (L := L) input factor) := factor.2.property

/-- The transformed generators are actual elements of the heterogeneous product. -/
noncomputable def generators (input : Generator → Index → Carrier) (generator : Generator) :
    ∀ factor, Factor (L := L) input factor :=
  embedding (L := L) input (restricted (L := L) input generator)

omit [Finite Carrier] in
/-- Surjective quotient maps preserve subdirectness of the generated relation. -/
theorem generators_subdirect (input : Generator → Index → Carrier) :
    IsSubdirect (Substructure.closure L (Set.range (generators (L := L) input)) :
      Set (∀ factor, Factor (L := L) input factor)) := by
  intro factor value
  obtain ⟨source, equal⟩ := quotientMap_surjective factor.2.val value
  obtain ⟨tuple, generated, coordinateEq⟩ := restricted_subdirect (L := L) input factor.1 source
  refine ⟨embedding input tuple, ?_, ?_⟩
  · exact (generated_image_iff (embedding input) (restricted input) _).mpr ⟨tuple, generated, rfl⟩
  · exact (congrArg (quotientMap factor.2.val) coordinateEq).trans equal

/-- A target in all coordinate images transforms without a membership assumption. -/
noncomputable def target (input : Generator → Index → Carrier) (value : Index → Carrier)
    (valid : ∀ index, value index ∈ images (L := L) input index) :
    ∀ factor, Factor (L := L) input factor :=
  embedding (L := L) input (fun index => ⟨value index, valid index⟩)

/-- The conversion preserves and reflects the original SMP membership question. -/
theorem membership (input : Generator → Index → Carrier) (value : Index → Carrier)
    (valid : ∀ index, value index ∈ images (L := L) input index) :
    target (L := L) input value valid ∈ Substructure.closure L (Set.range (generators (L := L) input)) ↔
      value ∈ Substructure.closure L (Set.range input) := by
  have converted := generated_membership_iff (embedding (L := L) input) (embedding_injective input)
    (restricted input) (fun index => ⟨value index, valid index⟩)
  have original := generated_membership_iff (inclusion (L := L) input) (inclusion_injective input)
    (restricted input) (fun index => ⟨value index, valid index⟩)
  exact converted.trans original.symm

/-- The original generated algebra is isomorphic onto the generated SI relation. -/
noncomputable def reductionEquiv (input : Generator → Index → Carrier) :
    Substructure.closure L (Set.range input) ≃[L]
      Substructure.closure L (Set.range (generators (L := L) input)) :=
  (generatedEquiv (embedding input) (embedding_injective input) (restricted input)).comp
    (generatedEquiv (inclusion input) (inclusion_injective input) (restricted input)).symm

/-- Monolith dependencies are active factors of the very same global instance. -/
noncomputable def dependencyFactor (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) (pair : MonolithPair (factorEntry input factor)) :
    FactorIndex (L := L) input :=
  ⟨factor.1, (dependencyEntry (factorEntry input factor) pair).2⟩

/-- Each dependency belongs strictly earlier in the fixed congruence-count order. -/
theorem dependencyFactor_earlier (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) (pair : MonolithPair (factorEntry input factor)) :
    Nat.card (Congruence L (Factor input (dependencyFactor input factor pair))) <
      Nat.card (Congruence L (Factor input factor)) :=
  dependency_earlier (factorEntry input factor) pair

/-- The global order uses the fixed sort rank before the original coordinate. -/
noncomputable def factorKey [LinearOrder Index] (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) : ℕ ×ₗ Index :=
  toLex ((catalogueRank (factorEntry input factor)).val, factor.1)

theorem dependencyFactor_key_lt [LinearOrder Index] (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) (pair : MonolithPair (factorEntry input factor)) :
    factorKey input (dependencyFactor input factor pair) < factorKey input factor :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl (dependency_rank_lt (factorEntry input factor) pair))

/-- Distinct earlier dependency coordinates, with duplicate quotient slots removed. -/
noncomputable def dependencySet (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) : Set (FactorIndex (L := L) input) :=
  Set.range (dependencyFactor input factor)

/-- Deduplicating cannot increase the fixed specialization bound. -/
theorem dependencySet_bound (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    Nat.card (dependencySet input factor) ≤ Nat.card Carrier * Nat.card Carrier :=
  (Nat.card_le_card_of_surjective (Set.rangeFactorization (dependencyFactor input factor))
    Set.rangeFactorization_surjective).trans (monolithPair_bound (factorEntry input factor))

/-- Every distinct dependency is strictly earlier, hence the parent is excluded. -/
theorem dependencySet_earlier [LinearOrder Index] (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) (dependency : dependencySet input factor) :
    factorKey input dependency.val < factorKey input factor := by
  obtain ⟨pair, equal⟩ := dependency.property
  rw [← equal]
  exact dependencyFactor_key_lt input factor pair

/-- Simple factors need no earlier coordinates: their monolith quotient is encoded
by the empty dependency product. -/
theorem simple_dependencySet_empty (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input)
    (simple : Nat.card (Congruence L (Factor input factor)) = 2) : dependencySet input factor = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro dependency member
  obtain ⟨pair, rfl⟩ := member
  have smaller := dependency_earlier (factorEntry input factor) pair
  have lower := catalogue_congruences_two_le (dependencyEntry (factorEntry input factor) pair)
  change Nat.card (Congruence L (SICarrier L Carrier (factorEntry input factor))) = 2 at simple
  omega

/-- The full graph equation holds for projections of the generated global
relation, not just for tuples in the ambient product of image algebras. -/
theorem generated_dependency_graph (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      ((fun pair : MonolithPair (factorEntry input factor) => tuple (dependencyFactor input factor pair)), tuple factor)) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor input factor)) =
      {tuple | tuple.1 = monolithPrefix (factorEntry input factor)
        (quotientMap (catalogueMonolith L Carrier (factorEntry input factor)) tuple.2)} := by
  change _ = {tuple : (∀ pair : MonolithPair (factorEntry input factor),
      SICarrier L Carrier (dependencyEntry (factorEntry input factor) pair)) ×
        SICarrier L Carrier (factorEntry input factor) | tuple.1 =
          monolithPrefix (factorEntry input factor)
            (quotientMap (catalogueMonolith L Carrier (factorEntry input factor)) tuple.2)}
  rw [← dependency_graph (factorEntry input factor)]
  ext selected
  constructor
  · rintro ⟨tuple, generated, rfl⟩
    obtain ⟨source, _, rfl⟩ := (generated_image_iff (embedding input) (restricted input) tuple).mp generated
    exact ⟨source factor.1, rfl⟩
  · rintro ⟨value, rfl⟩
    obtain ⟨source, generated, equal⟩ := restricted_subdirect (L := L) input factor.1 value
    refine ⟨embedding input source,
      (generated_image_iff (embedding input) (restricted input) _).mpr ⟨source, generated, rfl⟩, ?_⟩
    apply Prod.ext
    · funext pair
      exact congrArg (quotientMap (dependencyEntry (factorEntry input factor) pair).2.val) equal
    · exact congrArg (quotientMap factor.2.val) equal

/-- The projected earlier-coordinate algebra is exactly the range used by the
monolith-quotient isomorphism; no extra tuples appear in the projection. -/
theorem generated_dependency_prefix (input : Generator → Index → Carrier)
    (factor : FactorIndex (L := L) input) :
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      fun pair : MonolithPair (factorEntry input factor) => tuple (dependencyFactor input factor pair)) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor input factor)) =
      Set.range (monolithPrefix (factorEntry input factor)) := by
  have graph := congrArg (Set.image Prod.fst) (generated_dependency_graph input factor)
  rw [Set.image_image] at graph
  exact graph.trans (graph_projection_range _
    (quotientMap_surjective (catalogueMonolith L Carrier (factorEntry input factor))) _)

/-- Active padded positions, grouped by their fixed catalogue sort. -/
abbrev ActiveSlot (input : Generator → Index → Carrier) :=
  Σ entry : SICatalogue L Carrier, {index : Index // images (L := L) input index = entry.1}

/-- There are neither missing nor duplicate factors in the padded sort layout. -/
noncomputable def activeSlotEquiv (input : Generator → Index → Carrier) :
    FactorIndex (L := L) input ≃ ActiveSlot (L := L) input where
  toFun factor := ⟨factorEntry input factor, factor.1, rfl⟩
  invFun slot := by
    rcases slot with ⟨⟨image, relation⟩, index, equal⟩
    dsimp at equal
    subst image
    exact ⟨index, relation⟩
  left_inv := by rintro ⟨index, relation⟩; rfl
  right_inv := by
    rintro ⟨⟨image, relation⟩, index, equal⟩
    dsimp at equal
    subst image
    rfl

/-- Rank-ordered active positions correspond bijectively to mathematical factors. -/
noncomputable def rankedSlotEquiv (input : Generator → Index → Carrier) :
    FactorIndex (L := L) input ≃
      Σ rank : Fin (Nat.card (SICatalogue L Carrier)),
        {index : Index // images (L := L) input index = (catalogueRank.symm rank).1} :=
  (activeSlotEquiv input).trans (Equiv.sigmaCongrLeft' catalogueRank)

/-- Dense sort-local positions enumerate only active coordinates, in original
coordinate order. Their lengths are ordinary counts, not new size parameters. -/
noncomputable def denseSortEquiv [Fintype Index] [LinearOrder Index]
    (input : Generator → Index → Carrier) (entry : SICatalogue L Carrier) :
    {index : Index // images (L := L) input index = entry.1} ≃o
      Fin (Nat.card {index : Index // images (L := L) input index = entry.1}) := by
  classical
  exact (Fintype.orderIsoFinOfCardEq _ (Nat.card_eq_fintype_card.symm)).symm

/-- The ordered padded positions have a canonical dense sort-local numbering. -/
noncomputable def denseSlotEquiv [Fintype Index] [LinearOrder Index]
    (input : Generator → Index → Carrier) :
    FactorIndex (L := L) input ≃
      Σ rank : Fin (Nat.card (SICatalogue L Carrier)),
        Fin (Nat.card {index : Index // images (L := L) input index = (catalogueRank.symm rank).1}) :=
  (rankedSlotEquiv input).trans (Equiv.sigmaCongrRight (fun rank =>
    (denseSortEquiv input (catalogueRank.symm rank)).toEquiv))

/-- Summing actual sort counts gives exactly the total number of SI factors. -/
theorem factor_count_eq [Finite Index] (input : Generator → Index → Carrier) :
    Nat.card (FactorIndex (L := L) input) =
      ∑ rank : Fin (Nat.card (SICatalogue L Carrier)),
        Nat.card {index : Index // images (L := L) input index = (catalogueRank.symm rank).1} := by
  rw [Nat.card_congr (rankedSlotEquiv input), Nat.card_sigma]

/-- The full catalogue still gives a linear bound, fixed by specialization. -/
theorem factor_count_bound {count : ℕ} (input : Generator → Fin count → Carrier) :
    Nat.card (FactorIndex (L := L) input) ≤ count * Nat.card (SICatalogue L Carrier) := by
  have injective : Function.Injective (fun factor : FactorIndex (L := L) input =>
      (factor.1, factorEntry input factor)) := by
    rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ equal
    have indices : firstIndex = secondIndex := congrArg Prod.fst equal
    subst secondIndex
    have entries := congrArg Prod.snd equal
    exact congrArg (Sigma.mk firstIndex) (eq_of_heq (Sigma.mk.inj entries).2)
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective _ injective

end Polytime2.SMP.CoordinateReduction
