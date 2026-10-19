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

import Polytime2.Examples.SMP.Congruence

/-! # SI quotients separating the elements of a fixed finite algebra -/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type} [L.Structure Carrier]

/-- An SI algebra has a least congruence strictly above equality: its monolith. -/
def IsSubdirectlyIrreducible (L : Language.{0, 0}) (Carrier : Type) [L.Structure Carrier] : Prop :=
  ∃ monolith : Congruence L Carrier,
    IsLeast {relation : Congruence L Carrier | relation.val ≠ ⊥} monolith

omit [L.IsAlgebraic] in
/-- A pair identified by every nonequality congruence witnesses a monolith. -/
theorem si_of_common_pair (left right : Carrier) (different : left ≠ right)
    (common : ∀ relation : Congruence L Carrier, relation.val ≠ ⊥ → relation.val left right) :
    IsSubdirectlyIrreducible L Carrier := by
  classical
  let nontrivial : Set (Setoid Carrier) := {relation | Compatible (L := L) relation ∧ relation ≠ ⊥}
  let monolith : Setoid Carrier := sInf nontrivial
  have compatible : Compatible (L := L) monolith := by
    intro arity symbol first second related
    change ∀ relation ∈ nontrivial, relation (Structure.funMap symbol first) (Structure.funMap symbol second)
    intro relation valid
    exact valid.1 symbol first second (fun index => related index relation valid)
  have related : monolith left right := by
    intro relation valid
    exact common ⟨relation, valid.1⟩ valid.2
  have notEquality : monolith ≠ ⊥ := by
    intro equal
    rw [equal] at related
    exact different related
  refine ⟨⟨monolith, compatible⟩, notEquality, ?_⟩
  intro relation valid
  change monolith ≤ relation.val
  exact sInf_le (s := nontrivial) ⟨relation.property, valid⟩

omit [L.IsAlgebraic] in
/-- Isomorphic algebras have SI congruence structure. -/
theorem si_of_equiv {Target : Type} [L.Structure Target] (equivalence : Carrier ≃[L] Target)
    (si : IsSubdirectlyIrreducible L Carrier) : IsSubdirectlyIrreducible L Target := by
  classical
  obtain ⟨monolith, nontrivial, least⟩ := si
  have witness : ∃ first second, first ≠ second ∧ monolith.val first second := by
    by_contra absent
    apply nontrivial
    apply le_antisymm
    · intro first second related
      by_contra different
      exact absent ⟨first, second, different, related⟩
    · exact bot_le
  obtain ⟨first, second, different, related⟩ := witness
  apply si_of_common_pair (equivalence first) (equivalence second)
    (fun equal => different (equivalence.injective equal))
  intro relation valid
  have lifted : (pullback equivalence.toHom relation).val ≠ ⊥ := by
    intro equal
    apply valid
    apply Setoid.comap_injective equivalence equivalence.surjective
    have kernelEquality : Setoid.comap equivalence (⊥ : Setoid Target) = ⊥ := by
      apply Setoid.ext
      intro left right
      exact equivalence.injective.eq_iff
    exact equal.trans kernelEquality.symm
  exact least lifted related

/-- Maximal separation yields an SI quotient, with the separated pair as a
common pair for all nontrivial quotient congruences. -/
theorem maximal_quotient_si (left right : Carrier) (relation : Congruence L Carrier)
    (separated : ¬ relation.val left right)
    (maximal : ∀ larger : Congruence L Carrier, relation.val ≤ larger.val →
      ¬ larger.val left right → larger.val = relation.val) :
    IsSubdirectlyIrreducible L (Quotient relation.val) := by
  apply si_of_common_pair (quotientMap relation left) (quotientMap relation right)
  · intro equal
    exact separated (Quotient.exact equal)
  · intro quotientRelation nontrivial
    by_contra unrelated
    let lifted := pullback (quotientMap relation) quotientRelation
    have contains : relation.val ≤ lifted.val := by
      intro first second related
      change quotientRelation.val (quotientMap relation first) (quotientMap relation second)
      have equal : quotientMap relation first = quotientMap relation second := Quotient.sound related
      rw [equal]
    have equal : lifted.val = relation.val := maximal lifted contains unrelated
    apply nontrivial
    apply Setoid.comap_injective (quotientMap relation) (quotientMap_surjective relation)
    exact equal.trans (quotient_kernel relation).symm

/-- Every unequal pair in a finite algebra is separated by a surjective SI quotient. -/
theorem exists_si_separating [Finite Carrier] (left right : Carrier) (different : left ≠ right) :
    ∃ relation : Congruence L Carrier, ¬ relation.val left right ∧
      IsSubdirectlyIrreducible L (Quotient relation.val) := by
  obtain ⟨relation, separated, maximal⟩ := maximal_separating (L := L) left right different
  exact ⟨relation, separated, maximal_quotient_si left right relation separated maximal⟩

end Polytime2.SMP
