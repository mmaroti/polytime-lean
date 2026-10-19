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

import Polytime2.Examples.SMP.MonolithCatalogue
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-! # A specialization-fixed order of SI catalogue slots -/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier]

/-- The enumeration breaks ties once, independently of runtime input sizes. -/
noncomputable def catalogueKey (entry : SICatalogue L Carrier) : ℕ ×ₗ ℕ :=
  toLex (Nat.card (Congruence L (SICarrier L Carrier entry)),
    (@Fintype.equivFin (SICatalogue L Carrier) (Fintype.ofFinite _ ) entry).val)

private theorem catalogueKey_injective : Function.Injective (catalogueKey (L := L) (Carrier := Carrier)) := by
  intro first second equal
  apply (@Fintype.equivFin (SICatalogue L Carrier) (Fintype.ofFinite _)).injective
  apply Fin.ext
  exact congrArg (fun key : ℕ ×ₗ ℕ => (ofLex key).2) equal

/-- Rank is ordinary fixed finite specialization data. -/
noncomputable def catalogueRank : SICatalogue L Carrier ≃ Fin (Nat.card (SICatalogue L Carrier)) := by
  letI : Fintype (SICatalogue L Carrier) := Fintype.ofFinite _
  letI : LinearOrder (SICatalogue L Carrier) := LinearOrder.lift' catalogueKey catalogueKey_injective
  exact (Fintype.orderIsoFinOfCardEq (SICatalogue L Carrier) (Nat.card_eq_fintype_card.symm)).symm.toEquiv

/-- Lower congruence count always precedes a higher one, regardless of ties. -/
theorem catalogueRank_lt {first second : SICatalogue L Carrier}
    (smaller : Nat.card (Congruence L (SICarrier L Carrier first)) <
      Nat.card (Congruence L (SICarrier L Carrier second))) :
    catalogueRank first < catalogueRank second := by
  let : Fintype (SICatalogue L Carrier) := Fintype.ofFinite _
  let : LinearOrder (SICatalogue L Carrier) := LinearOrder.lift' catalogueKey catalogueKey_injective
  change (Fintype.orderIsoFinOfCardEq (SICatalogue L Carrier) (Nat.card_eq_fintype_card.symm)).symm first <
    (Fintype.orderIsoFinOfCardEq (SICatalogue L Carrier) (Nat.card_eq_fintype_card.symm)).symm second
  apply (OrderIso.lt_iff_lt _).mpr
  change catalogueKey first < catalogueKey second
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl smaller)

/-- Increasing fixed rank gives the required nondecreasing congruence counts. -/
theorem catalogueRank_monotone {first second : SICatalogue L Carrier}
    (ordered : catalogueRank first ≤ catalogueRank second) :
    Nat.card (Congruence L (SICarrier L Carrier first)) ≤
      Nat.card (Congruence L (SICarrier L Carrier second)) := by
  by_contra reversed
  exact (not_lt_of_ge ordered) (catalogueRank_lt (Nat.lt_of_not_ge reversed))

/-- The exported rank enumeration is nondecreasing in congruence count. -/
theorem catalogue_order_monotone : Monotone (fun rank : Fin (Nat.card (SICatalogue L Carrier)) =>
    Nat.card (Congruence L (SICarrier L Carrier (catalogueRank.symm rank)))) := by
  intro first second ordered
  apply catalogueRank_monotone
  simpa only [Equiv.apply_symm_apply] using ordered

/-- Every SI sort has at least equality and one strictly larger congruence. -/
theorem catalogue_congruences_two_le (entry : SICatalogue L Carrier) :
    2 ≤ Nat.card (Congruence L (SICarrier L Carrier entry)) := by
  let bottom : Congruence L (SICarrier L Carrier entry) := ⟨⊥, compatible_equality⟩
  let monolith := catalogueMonolith L Carrier entry
  have different : monolith ≠ bottom := by
    intro equal
    exact (catalogueMonolith_least L Carrier entry).1 (congrArg Subtype.val equal)
  have injective : Function.Injective (fun choice : Bool => if choice then monolith else bottom) := by
    intro first second equal
    cases first <;> cases second <;> first | rfl | exact False.elim (different equal) | exact False.elim (different equal.symm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_le_card_of_injective _ injective

/-- Simple sorts (exactly two congruences) precede all nonsimple SI sorts. -/
theorem simple_rank_lt {simple other : SICatalogue L Carrier}
    (simple_count : Nat.card (Congruence L (SICarrier L Carrier simple)) = 2)
    (other_count : Nat.card (Congruence L (SICarrier L Carrier other)) ≠ 2) :
    catalogueRank simple < catalogueRank other := by
  apply catalogueRank_lt
  have lower := catalogue_congruences_two_le other
  omega

/-- Every monolith dependency has a strictly earlier fixed catalogue rank. -/
theorem dependency_rank_lt (entry : SICatalogue L Carrier) (pair : MonolithPair entry) :
    catalogueRank (dependencyEntry entry pair) < catalogueRank entry :=
  catalogueRank_lt (dependency_earlier entry pair)

end Polytime2.SMP
