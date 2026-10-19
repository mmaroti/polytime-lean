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

import Polytime2.Examples.SMP.CoordinateImages
import Polytime2.Arrays.Transform

/-! # Computing all coordinate images with the generic array transformer -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Input is column-major: each coordinate contains its generator column.
The result stores the actual generated subalgebra at every coordinate. -/
noncomputable def coordinateImages (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := ((elementDomain Carrier).constant.arrayOfLength generators).arrayOfLength coordinates
  outputDomain := (subalgebraDomain L Carrier).constant.arrayOfLength coordinates
  precondition _ _ := True
  compute _ arguments := fun index => Substructure.closure L (Set.range (arguments.val () index))

/-- Both dimensions and the width of a whole column vary at runtime. -/
theorem coordinateImages_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (coordinateImages (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  exact mapArray_realizable ((elementDomain Carrier).constant.arrayOfLength generators)
    (subalgebraDomain L Carrier).constant coordinates
    (fun _ column => Substructure.closure L (Set.range column))
    (columnClosure_realizable (L := L) (Carrier := Carrier) generators)

end Polytime2.SMP
