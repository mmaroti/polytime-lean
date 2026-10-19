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

import Polytime2.Examples.SMP.Generation
import Mathlib.ModelTheory.Quotients
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-! # Finite congruences and quotient maps for specialization

Congruences reuse Mathlib setoids, with operation compatibility as a subtype
property. The maximal separating congruences supply the SI decomposition.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type} [L.Structure Carrier]

/-- An equivalence relation is a congruence precisely when operations preserve it. -/
def Compatible (relation : Setoid Carrier) : Prop :=
  ∀ {arity} (symbol : L.Functions arity) (left right : Fin arity → Carrier),
    (∀ index, relation (left index) (right index)) →
      relation (Structure.funMap symbol left) (Structure.funMap symbol right)

/-- No additional congruence structure or second equivalence-relation API is needed. -/
abbrev Congruence (L : Language.{0, 0}) (Carrier : Type) [L.Structure Carrier] :=
  {relation : Setoid Carrier // Compatible (L := L) relation}

omit [L.IsAlgebraic] in
theorem compatible_equality : Compatible (L := L) (⊥ : Setoid Carrier) := by
  intro arity symbol left right related
  change Structure.funMap symbol left = Structure.funMap symbol right
  exact congrArg (Structure.funMap symbol) (funext fun index => related index)

/-- Congruence catalogues are finite because their underlying binary relations are finite. -/
instance congruenceFinite [Finite Carrier] : Finite (Congruence L Carrier) := by
  apply Finite.of_injective (fun relation : Congruence L Carrier =>
    {pair : Carrier × Carrier | relation.val pair.1 pair.2})
  intro first second equal
  apply Subtype.ext
  apply Setoid.ext
  intro left right
  exact Set.ext_iff.mp equal (left, right)

/-- Reuse Mathlib's quotient operations and their compatibility interface. -/
instance congruencePrestructure (relation : Congruence L Carrier) : L.Prestructure relation.val where
  toStructure := inferInstance
  fun_equiv := fun {_} symbol left right related => relation.property symbol left right related
  rel_equiv := fun {_} symbol _ _ _ => isEmptyElim symbol

/-- Every quotient projection is an actual algebra homomorphism. -/
def quotientMap (relation : Congruence L Carrier) : Carrier →[L] Quotient relation.val where
  toFun value := Quotient.mk relation.val value
  map_fun' symbol arguments := by
    simpa only [congruencePrestructure, Function.comp_def] using
      (funMap_quotient_mk' relation.val symbol arguments).symm
  map_rel' symbol := isEmptyElim symbol

/-- Quotient projections are surjective, including for singleton factors. -/
theorem quotientMap_surjective (relation : Congruence L Carrier) :
    Function.Surjective (quotientMap relation) := Quotient.mk_surjective

omit [L.IsAlgebraic] in
/-- Fixed finite precomputation can select a maximal congruence separating any
specified unequal pair. No decomposition is assumed as specialization input. -/
theorem maximal_separating [Finite Carrier] (left right : Carrier) (different : left ≠ right) :
    ∃ relation : Congruence L Carrier, ¬ relation.val left right ∧
      ∀ larger : Congruence L Carrier, relation.val ≤ larger.val →
        ¬ larger.val left right → larger.val = relation.val := by
  classical
  let candidates : Set (Congruence L Carrier) := {relation | ¬ relation.val left right}
  have nonempty : candidates.Nonempty := by
    refine ⟨⟨⊥, compatible_equality⟩, ?_⟩
    exact different
  obtain ⟨relation, separated, maximal⟩ := candidates.toFinite.exists_maximal nonempty
  refine ⟨relation, separated, ?_⟩
  intro larger contains separated
  exact le_antisymm (maximal separated contains) contains

/-- Pull a congruence back along a certified homomorphism. -/
def pullback {Target : Type} [L.Structure Target]
    (map : Carrier →[L] Target) (relation : Congruence L Target) : Congruence L Carrier :=
  ⟨Setoid.comap map relation.val, by
    intro arity symbol left right related
    change relation.val (map (Structure.funMap symbol left)) (map (Structure.funMap symbol right))
    rw [map.map_fun, map.map_fun]
    exact relation.property symbol _ _ related⟩

omit [L.IsAlgebraic] in
/-- Surjective homomorphisms embed congruence catalogues by pullback. -/
theorem pullback_injective {Target : Type} [L.Structure Target]
    (map : Carrier →[L] Target) (surjective : Function.Surjective map) :
    Function.Injective (pullback map) := by
  intro first second equal
  apply Subtype.ext
  apply Setoid.comap_injective map surjective
  exact congrArg Subtype.val equal

omit [L.IsAlgebraic] in
/-- A quotient cannot have more congruences than its source algebra. -/
theorem congruence_count_le {Target : Type} [L.Structure Target] [Finite Carrier]
    (map : Carrier →[L] Target) (surjective : Function.Surjective map) :
    Nat.card (Congruence L Target) ≤ Nat.card (Congruence L Carrier) :=
  Nat.card_le_card_of_injective (pullback map) (pullback_injective map surjective)

/-- Pulling equality back along the quotient map recovers exactly its congruence. -/
theorem quotient_kernel (relation : Congruence L Carrier) :
    Setoid.comap (quotientMap relation) (⊥ : Setoid (Quotient relation.val)) = relation.val := by
  apply Setoid.ext
  intro left right
  exact Quotient.eq

/-- Proper quotients strictly reduce the number of congruences. This is the
ordering measure required by monolith preparation. -/
theorem quotient_congruence_count_lt [Finite Carrier] (relation : Congruence L Carrier)
    (nontrivial : relation.val ≠ ⊥) :
    Nat.card (Congruence L (Quotient relation.val)) < Nat.card (Congruence L Carrier) := by
  by_contra notSmaller
  have onto := ((pullback_injective (quotientMap relation) (quotientMap_surjective relation)).bijective_of_nat_card_le
    (Nat.le_of_not_gt notSmaller)).2
  obtain ⟨larger, equal⟩ := onto ⟨⊥, compatible_equality⟩
  have contains : relation.val ≤ (pullback (quotientMap relation) larger).val := by
    intro first second related
    change larger.val (quotientMap relation first) (quotientMap relation second)
    rw [show quotientMap relation first = quotientMap relation second from Quotient.sound related]
  apply nontrivial
  exact le_antisymm (by simpa only [equal] using contains) bot_le

end Polytime2.SMP
