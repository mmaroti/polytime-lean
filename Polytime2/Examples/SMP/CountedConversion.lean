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

import Polytime2.Examples.SMP.Conversion
import Polytime2.Examples.SMP.Counts

/-! # Attaching stored sort counts to the certified SI conversion -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Read image algebras from the already converted coordinate records. -/
noncomputable def convertedImages (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := (subalgebraDomain L Carrier).constant.arrayOfLength coordinates
  precondition _ _ := True
  compute _ arguments := fun index => (arguments.val () index).1

theorem convertedImages_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedImages (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let slot : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let payload := slot.prod (slot.arrayOfLength generators)
  exact mapArray_realizable (image.prod payload) image coordinates (fun _ value => value.1)
    (pairProjection_realizable image payload false)

/-- Read and count the stored images without computing their closures again. -/
noncomputable def convertedCounts (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (convertedImages (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (catalogueCounts (L := L) (Carrier := Carrier) coordinates) rfl (by intros; trivial)

theorem convertedCounts_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedCounts (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertedImages_realizable coordinates generators).followedBy (catalogueCounts_realizable coordinates)
    rfl (by intros; trivial)

end Polytime2.SMP
