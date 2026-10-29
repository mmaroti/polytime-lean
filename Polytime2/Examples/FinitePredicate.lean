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

import Polytime2.Primitives.FiniteOperations

/-! # Fixed finite predicates through their public mathematical specifications -/

namespace Polytime2.Examples.FinitePredicate

open Polytime2.Computation

private noncomputable def threeElements : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 3))

noncomputable def isZero : Polytime2.Computation Empty Unit :=
  finitePredicate threeElements (fun (value : Fin 3) => decide (value = 0))

example : isZero.Realizable := finitePredicate_realizable threeElements _
example : (isZero.compute Empty.elim
    ⟨(fun _ => (0 : Fin 3)), True.intro⟩ : Bool) = true := rfl
example : (isZero.compute Empty.elim
    ⟨(fun _ => (2 : Fin 3)), True.intro⟩ : Bool) = false := rfl

-- The input may have zero width while the Boolean output still has one bit.
example : (finitePredicate (Parameter := Empty) (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (fun _ => true)).Realizable := finitePredicate_realizable _ _

end Polytime2.Examples.FinitePredicate
