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

import Polytime2.Examples.SMP.SI
import Mathlib.SetTheory.Cardinal.Finite

/-! # A finite subdirect SI decomposition constructed from separating pairs -/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier Generator : Type} [L.Structure Carrier] [Finite Carrier]

/-- Factor slots are fixed finite data at specialization time. -/
abbrev SeparatingPair (Carrier : Type) := {pair : Carrier × Carrier // pair.1 ≠ pair.2}

/-- Choose a proved SI quotient for each unequal pair of elements. -/
noncomputable def decompositionRelation (pair : SeparatingPair Carrier) : Congruence L Carrier :=
  Classical.choose (exists_si_separating (L := L) pair.val.1 pair.val.2 pair.property)

/-- The chosen quotient distinguishes the pair for which it was selected. -/
theorem decomposition_separates (pair : SeparatingPair Carrier) :
    ¬ (decompositionRelation (L := L) pair).val pair.val.1 pair.val.2 :=
  (Classical.choose_spec (exists_si_separating (L := L) pair.val.1 pair.val.2 pair.property)).1

/-- Actual quotient carriers, rather than a second label-based algebra. -/
noncomputable abbrev DecompositionFactor (L : Language.{0, 0}) [L.IsAlgebraic]
    (Carrier : Type) [L.Structure Carrier] [Finite Carrier] (pair : SeparatingPair Carrier) :=
  Quotient (decompositionRelation (L := L) pair).val

/-- Every factor in the selected decomposition is SI. -/
theorem decomposition_si (pair : SeparatingPair Carrier) :
    IsSubdirectlyIrreducible L (DecompositionFactor L Carrier pair) :=
  (Classical.choose_spec (exists_si_separating (L := L) pair.val.1 pair.val.2 pair.property)).2

/-- All selected projections together give the embedding into the SI product. -/
noncomputable def decompositionMap : Carrier →[L] (∀ pair, DecompositionFactor L Carrier pair) :=
  assemble (fun pair => quotientMap (decompositionRelation pair))

/-- Joint separation proves injectivity, including for singleton source algebras. -/
theorem decomposition_injective : Function.Injective (decompositionMap (L := L) (Carrier := Carrier)) := by
  intro left right equal
  by_contra different
  let pair : SeparatingPair Carrier := ⟨(left, right), different⟩
  exact decomposition_separates (L := L) pair (Quotient.exact (congrFun equal pair))

/-- Each factor projection is surjective independently of the other factors. -/
theorem decomposition_surjective (pair : SeparatingPair Carrier) :
    Function.Surjective (fun value => decompositionMap (L := L) value pair) :=
  quotientMap_surjective (decompositionRelation pair)

/-- The SI embedding preserves and reflects generated membership. -/
theorem decomposition_membership (generators : Generator → Carrier) (target : Carrier) :
    decompositionMap (L := L) target ∈ Substructure.closure L
      (Set.range (fun generator => decompositionMap (L := L) (generators generator))) ↔
      target ∈ Substructure.closure L (Set.range generators) :=
  generated_membership_iff _ decomposition_injective generators target

/-- A generating list transforms into a subdirect generating list. -/
theorem decomposition_subdirect (generators : Generator → Carrier)
    (generates : Substructure.closure L (Set.range generators) = ⊤) :
    IsSubdirect (Substructure.closure L
      (Set.range (fun generator => decompositionMap (L := L) (generators generator))) :
        Set (∀ pair, DecompositionFactor L Carrier pair)) := by
  apply generated_subdirect
  intro pair
  change Substructure.closure L (Set.range (fun generator =>
    quotientMap (decompositionRelation pair) (generators generator))) = ⊤
  apply SetLike.coe_injective
  rw [generated_image_full _ generators generates]
  exact Set.eq_univ_of_forall (decomposition_surjective (L := L) pair)

/-- A fixed algebra needs at most its squared cardinality many SI factor slots. -/
theorem decomposition_factor_bound :
    Nat.card (SeparatingPair Carrier) ≤ Nat.card Carrier * Nat.card Carrier := by
  simpa only [Nat.card_prod] using
    Nat.card_le_card_of_injective (fun pair : SeparatingPair Carrier => pair.val) Subtype.val_injective

end Polytime2.SMP
