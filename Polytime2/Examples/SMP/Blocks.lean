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

/-! # Fixed-capacity SI blocks and their finite-table implementation

Each original coordinate reserves one slot per entry of the fixed SI catalogue.
Only quotients of its coordinate image are active. This includes every factor
needed by monolith preparation without runtime recursion.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier]

/-- A fixed-capacity block of tagged mathematical quotient values. -/
abbrev SIBlock (L : Language.{0, 0}) [L.IsAlgebraic] (Carrier : Type)
    [L.Structure Carrier] := SICatalogue L Carrier → Option (SIValue L Carrier)

/-- Active slots are exactly the SI quotients of the coordinate image algebra. -/
noncomputable def quotientBlock (subalgebra : L.Substructure Carrier)
    (value : subalgebra) : SIBlock L Carrier := fun entry => by
  classical
  exact if equal : entry.1 = subalgebra then
    some ⟨entry, quotientMap entry.2.val ⟨value.val, by simpa only [equal] using value.property⟩⟩
  else none

omit [Finite Carrier] in
/-- Activity depends only on the source image, never on a particular value. -/
theorem quotientBlock_active (subalgebra : L.Substructure Carrier) (value : subalgebra)
    (entry : SICatalogue L Carrier) :
    (quotientBlock subalgebra value entry).isSome = true ↔ subalgebra = entry.1 := by
  classical
  unfold quotientBlock
  by_cases equal : entry.1 = subalgebra
  · rw [dite_eq_left equal]
    exact ⟨fun _ => equal.symm, fun _ => rfl⟩
  · rw [dite_eq_right equal]
    constructor
    · intro impossible; cases impossible
    · intro reversed; exact False.elim (equal reversed.symm)

omit [Finite Carrier] in
/-- Every active catalogue entry contains its actual canonical quotient value. -/
theorem quotientBlock_entry (entry : SICatalogue L Carrier) (value : entry.1) :
    quotientBlock entry.1 value entry = some ⟨entry, quotientMap entry.2.val value⟩ := by
  classical
  simp [quotientBlock]

/-- The selected separating quotients occur in the full catalogue block. -/
theorem quotientBlock_local (subalgebra : L.Substructure Carrier) (value : subalgebra)
    (pair : SeparatingPair subalgebra) :
    quotientBlock subalgebra value (decompositionEntry L Carrier subalgebra pair) =
      some ⟨decompositionEntry L Carrier subalgebra pair,
        quotientMap (decompositionRelation pair) value⟩ := by
  exact quotientBlock_entry (decompositionEntry L Carrier subalgebra pair) value

/-- Padding loses no information: every image embeds in its fixed-capacity block. -/
theorem quotientBlock_injective (subalgebra : L.Substructure Carrier) :
    Function.Injective (quotientBlock (L := L) subalgebra) := by
  intro first second equal
  apply decomposition_injective (L := L)
  funext pair
  have selected := congrFun equal (decompositionEntry L Carrier subalgebra pair)
  rw [quotientBlock_local, quotientBlock_local] at selected
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj selected)).2

/-- Values outside the image are rejected explicitly, before quotient maps run. -/
noncomputable def checkedQuotientBlock (subalgebra : L.Substructure Carrier)
    (value : Carrier) : Option (SIBlock L Carrier) := by
  classical
  exact if member : value ∈ subalgebra then some (quotientBlock subalgebra ⟨value, member⟩) else none

omit [Finite Carrier] in
/-- Valid values are converted by the actual quotient block map. -/
theorem checkedQuotientBlock_of_mem (subalgebra : L.Substructure Carrier) (value : subalgebra) :
    checkedQuotientBlock (L := L) subalgebra value.val = some (quotientBlock subalgebra value) := by
  classical
  simp [checkedQuotientBlock, value.property]

omit [Finite Carrier] in
theorem checkedQuotientBlock_none (subalgebra : L.Substructure Carrier) (value : Carrier) :
    checkedQuotientBlock (L := L) subalgebra value = none ↔ value ∉ subalgebra := by
  classical
  simp [checkedQuotientBlock]

/-- Selection, validation, and all quotient values form one fixed finite table. -/
noncomputable def quotientBlockComputation : Computation Empty Bool :=
  finiteTable (subalgebraDomain L Carrier) (elementDomain Carrier)
    (elementDomain (Option (SIBlock L Carrier)))
    (fun subalgebra value => checkedQuotientBlock subalgebra value)

theorem quotientBlockComputation_realizable :
    (quotientBlockComputation (L := L) (Carrier := Carrier)).Realizable :=
  finiteTable_realizable _ _ _ _

end Polytime2.SMP
