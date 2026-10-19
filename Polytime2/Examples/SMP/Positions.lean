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

import Polytime2.Examples.SMP.CountedConversion
import Polytime2.Arrays.PrefixCount

/-! # Certified dense sort-local positions for every original coordinate -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- At an active coordinate, the stored prefix count is its dense sort-local index. -/
noncomputable def cataloguePositions (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    Computation Parameter Unit :=
  (catalogueFlags length entry).followedBy (prefixCounts length) rfl (by intros; trivial)

theorem cataloguePositions_realizable (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    (cataloguePositions length entry).Realizable :=
  (catalogueFlags_realizable length entry).followedBy (prefixCounts_realizable length) rfl (by intros; trivial)

theorem cataloguePositions_correct (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier)
    (sizes : Parameter → ℕ) (images : Fin (MvPolynomial.eval sizes length) → L.Substructure Carrier)
    (coordinate : Fin (MvPolynomial.eval sizes length)) :
    (((cataloguePositions length entry).compute sizes ⟨(fun _ => images), trivial⟩) coordinate).toNat =
      ((List.ofFn (fun index => @decide (images index = entry.1) (Classical.propDecidable _))).take coordinate.val).count true :=
  prefixCounts_correct _ _ _ _

/-- One polynomial-capacity position table per fixed catalogue rank. -/
noncomputable def cataloguePositionTables (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (subalgebraDomain L Carrier).constant.arrayOfLength length
  outputDomain := EncodedDomain.record (Nat.card (SICatalogue L Carrier))
    (fun _ => (EncodedDomain.bitVectors (length + 1)).arrayOfLength length)
  precondition _ _ := True
  compute sizes arguments := fun rank =>
    (cataloguePositions length ((catalogueRank (L := L) (Carrier := Carrier)).symm rank)).compute sizes
      ⟨arguments.val, trivial⟩

theorem cataloguePositionTables_realizable (length : MvPolynomial Parameter ℕ) :
    (cataloguePositionTables (L := L) (Carrier := Carrier) length).Realizable :=
  Realizable.recordOutputs _ _ _ _ _ (fun rank => cataloguePositions_realizable length (catalogueRank.symm rank))

/-- Read the already computed image algebras before constructing position tables. -/
noncomputable def convertedPositionTables (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (convertedImages (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (cataloguePositionTables (L := L) (Carrier := Carrier) coordinates) rfl (by intros; trivial)

theorem convertedPositionTables_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedPositionTables (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedImages_realizable coordinates generators).followedBy (cataloguePositionTables_realizable coordinates)
    rfl (by intros; trivial)

end Polytime2.SMP
