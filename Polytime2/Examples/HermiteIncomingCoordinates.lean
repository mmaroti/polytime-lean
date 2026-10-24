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

import Polytime2.Matrices.HermiteIncomingCoordinates
import Polytime2.TM0.Computation

/-! # Incoming-stage coordinate preparation

A nonmonotone row selection checks that positions select mathematical rows,
while the incoming row remains the last selected row.
-/

namespace Polytime2.Examples.HermiteIncomingCoordinates

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingCoordinates rows columns pivots).TM0Realizable :=
  (hermiteIncomingCoordinates_realizable rows columns pivots).tm0

private noncomputable def arguments (position : Fin 2) :
    (hermiteIncomingCoordinates (Parameter := Empty) 4 2 2).Arguments Empty.elim
  | 0 => fun index => ⟨if index.val = 0 then 2 else if index.val = 1 then 0 else 3, by
      norm_num only [map_ofNat]; split <;> (try split) <;> omega⟩
  | 1 => fun index => ⟨if index.val = 0 then 1 else 0, by norm_num only [map_ofNat]; split <;> omega⟩
  | 2 => ⟨position.val, by simpa using position.isLt⟩

example : let result := (hermiteIncomingCoordinates (Parameter := Empty) 4 2 2).compute Empty.elim ⟨arguments ⟨1, by decide⟩, trivial⟩;
    result.1.val = 0 ∧ result.2.1.val = 3 ∧
      result.2.2.1.val = 0 ∧ result.2.2.2.val = 1 := by
  dsimp only [hermiteIncomingCoordinates]
  norm_num [arguments, successorValues, Fin.last]

example : let result := (hermiteIncomingCoordinates (Parameter := Empty) 4 2 2).compute Empty.elim ⟨arguments ⟨0, by decide⟩, trivial⟩;
    result.1.val = 2 ∧ result.2.1.val = 3 ∧
      result.2.2.1.val = 1 ∧ result.2.2.2.val = 0 := by
  dsimp only [hermiteIncomingCoordinates]
  norm_num [arguments, successorValues, Fin.last]

end Polytime2.Examples.HermiteIncomingCoordinates
