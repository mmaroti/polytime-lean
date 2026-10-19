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

import Polytime2.Examples.SMP.Decomposition
import Polytime2.Examples.SMP.HomQuotient
import Polytime2.Examples.SMP.CoordinateImages

/-! # The fixed catalogue of SI quotients of subalgebras

Catalogue entries retain their mathematical subalgebra and congruence. Values
are elements of the actual quotient, encoded by the existing finite codec.
-/

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language

variable (L : Language.{0, 0}) [L.IsAlgebraic]
variable (Carrier : Type) [L.Structure Carrier] [Finite Carrier]

/-- All SI quotients of subalgebras of the specialized finite algebra. -/
abbrev SICatalogue :=
  Σ subalgebra : L.Substructure Carrier,
    {relation : Congruence L subalgebra //
      IsSubdirectlyIrreducible L (Quotient relation.val)}

/-- The carrier of a catalogue entry is its actual quotient algebra. -/
abbrev SICarrier (entry : SICatalogue L Carrier) := Quotient entry.2.val.val

instance siCatalogueFinite : Finite (SICatalogue L Carrier) := inferInstance

/-- A single finite mathematical domain holds tagged values of every sort. -/
abbrev SIValue := Σ entry : SICatalogue L Carrier, SICarrier L Carrier entry

instance siValueFinite : Finite (SIValue L Carrier) := inferInstance

/-- Inactive slots use `none`; active slots contain a catalogue value. -/
noncomputable def siSlotDomain : EncodedDomain Empty :=
  elementDomain (Option (SIValue L Carrier))

/-- The separating-pair construction selects an entry of this same catalogue. -/
noncomputable def decompositionEntry (subalgebra : L.Substructure Carrier)
    (pair : SeparatingPair subalgebra) : SICatalogue L Carrier :=
  ⟨subalgebra, decompositionRelation pair, decomposition_si pair⟩

/-- A surjective SI image is represented canonically as a quotient of its
original subalgebra, including composites of several quotient maps. -/
noncomputable def imageEntry (subalgebra : L.Substructure Carrier)
    {Target : Type} [L.Structure Target] (map : subalgebra →[L] Target)
    (surjective : Function.Surjective map) (si : IsSubdirectlyIrreducible L Target) :
    SICatalogue L Carrier :=
  ⟨subalgebra, kernel map, si_of_equiv (kernelEquiv map surjective).symm si⟩

/-- Monoliths are selected from the proved SI property, not assumed data. -/
noncomputable def catalogueMonolith (entry : SICatalogue L Carrier) :
    Congruence L (SICarrier L Carrier entry) := Classical.choose entry.2.property

omit [Finite Carrier] in
theorem catalogueMonolith_least (entry : SICatalogue L Carrier) :
    IsLeast {relation : Congruence L (SICarrier L Carrier entry) | relation.val ≠ ⊥}
      (catalogueMonolith L Carrier entry) := Classical.choose_spec entry.2.property

end Polytime2.SMP
