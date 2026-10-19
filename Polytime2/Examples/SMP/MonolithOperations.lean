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

import Polytime2.Examples.SMP.Blocks
import Polytime2.Examples.SMP.MonolithCatalogue

/-! # Certified fixed-catalogue graph lookups for monolith preparation

Graph maps are finite specialization data. A query supplies an actual monolith
quotient value and receives its canonical block on the dependency sorts.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier]

/-- Query values use the original quotient algebras, not another label algebra. -/
abbrev MonolithQuery (L : Language.{0, 0}) [L.IsAlgebraic] (Carrier : Type)
    [L.Structure Carrier] :=
  Σ entry : SICatalogue L Carrier, Quotient (catalogueMonolith L Carrier entry).val

instance monolithQueryFinite : Finite (MonolithQuery L Carrier) := inferInstance

/-- A dependency block has one active slot per distinct dependency sort. -/
noncomputable def monolithBlock (entry : SICatalogue L Carrier)
    (value : Quotient (catalogueMonolith L Carrier entry).val) : SIBlock L Carrier := fun child => by
  classical
  exact if member : ∃ pair : MonolithPair entry, dependencyEntry entry pair = child then
    let pair := Classical.choose member
    some ⟨dependencyEntry entry pair, monolithPrefix entry value pair⟩
  else none

/-- The finite graph table agrees with the canonical quotient maps on the
original source image, including when several pairs select the same sort. -/
theorem monolithBlock_source (entry : SICatalogue L Carrier) (value : entry.1)
    (child : SICatalogue L Carrier) :
    monolithBlock entry
      (quotientMap (catalogueMonolith L Carrier entry) (quotientMap entry.2.val value)) child =
      @ite _ (child ∈ Set.range (dependencyEntry entry)) (Classical.propDecidable _)
        (quotientBlock entry.1 value child) none := by
  classical
  unfold monolithBlock
  by_cases member : ∃ pair : MonolithPair entry, dependencyEntry entry pair = child
  · rw [dite_eq_left member, ite_eq_left (show child ∈ Set.range (dependencyEntry entry) from member)]
    let pair := Classical.choose member
    have selected : dependencyEntry entry pair = child := Classical.choose_spec member
    change some (⟨dependencyEntry entry pair,
      monolithPrefix entry (quotientMap (catalogueMonolith L Carrier entry) (quotientMap entry.2.val value)) pair⟩ : SIValue L Carrier) = _
    rw [dependency_commutes, ← selected]
    exact (quotientBlock_entry (dependencyEntry entry pair) value).symm
  · rw [dite_eq_right member, ite_eq_right (show child ∉ Set.range (dependencyEntry entry) from member)]

/-- A public polynomial-time implementation of each finite graph-table query. -/
noncomputable def monolithGraphLookup : Computation Empty Unit :=
  finiteOperation (fun _ => elementDomain (MonolithQuery L Carrier)) (elementDomain (SIBlock L Carrier))
    (fun _ values => monolithBlock (values ()).1 (values ()).2)

theorem monolithGraphLookup_realizable :
    (monolithGraphLookup (L := L) (Carrier := Carrier)).Realizable :=
  finiteOperation_realizable _ _ _

/-- Dependency masks are fixed finite data, also available through a certified table. -/
noncomputable def monolithDependencyLookup : Computation Empty Unit :=
  finiteOperation (fun _ => elementDomain (SICatalogue L Carrier)) (elementDomain (Set (SICatalogue L Carrier)))
    (fun _ values => Set.range (dependencyEntry (values ())))

theorem monolithDependencyLookup_realizable :
    (monolithDependencyLookup (L := L) (Carrier := Carrier)).Realizable :=
  finiteOperation_realizable _ _ _

/-- Quotient a tagged parent value by its precomputed monolith. -/
noncomputable def monolithClassLookup : Computation Empty Unit :=
  finiteOperation (fun _ => elementDomain (SIValue L Carrier)) (elementDomain (MonolithQuery L Carrier))
    (fun _ values => ⟨(values ()).1,
      quotientMap (catalogueMonolith L Carrier (values ()).1) (values ()).2⟩)

theorem monolithClassLookup_realizable :
    (monolithClassLookup (L := L) (Carrier := Carrier)).Realizable :=
  finiteOperation_realizable _ _ _

/-- Evaluate the dependency graph directly on an ordinary tagged parent value. -/
noncomputable def monolithValueLookup : Computation Empty Unit :=
  (monolithClassLookup (L := L) (Carrier := Carrier)).followedBy
    (monolithGraphLookup (L := L) (Carrier := Carrier)) rfl (by intros; trivial)

theorem monolithValueLookup_realizable :
    (monolithValueLookup (L := L) (Carrier := Carrier)).Realizable :=
  monolithClassLookup_realizable.followedBy monolithGraphLookup_realizable rfl (by intros; trivial)

end Polytime2.SMP
