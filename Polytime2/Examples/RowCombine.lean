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

import Polytime2.Computations.FiniteTable

/-! # Three separate scalar arguments with a mathematical result -/

namespace Polytime2.Examples.RowCombine

open Polytime2.Computation

private def threeElements : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 3))

def linearCombination : Polytime2.Computation Empty (Fin 3) :=
  finiteTernary threeElements (fun _ (coefficient source target : Fin 3) => coefficient * source + target)

theorem linearCombination_realizable : linearCombination.Realizable := finiteTernary_realizable _ _

example : (linearCombination.compute Empty.elim
    ⟨![ (2 : Fin 3), (1 : Fin 3), (1 : Fin 3) ], True.intro⟩ : Fin 3) = (0 : Fin 3) := rfl

example : (finiteTernary (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (fun _ first _ _ => first)).Realizable := finiteTernary_realizable _ _

end Polytime2.Examples.RowCombine
