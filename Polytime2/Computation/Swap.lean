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

import Polytime2.Computation.Equality
import Polytime2.Computation.Conditional

/-! # Exchanging two mathematical values

Canonical equality tests and conditional selection realize the ordinary swap
permutation on any existing encoded domain, including dependent carriers.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Arguments are the two exchanged values and the value to transform. -/
noncomputable def elementsSwap (domain : EncodedDomain.{0, 0} Parameter) : Computation Parameter (Fin 3) := by
  classical
  exact {
    inputDomains := fun _ => domain
    outputDomain := domain
    precondition := fun _ _ => True
    compute := fun _ arguments => Equiv.swap (arguments.val 0) (arguments.val 1) (arguments.val 2) }

/-- Two equality tests and selections implement the swap without exposing bits. -/
theorem elementsSwap_realizable (domain : EncodedDomain.{0, 0} Parameter) : (elementsSwap domain).Realizable := by
  classical
  let inputs : Fin 3 → EncodedDomain.{0, 0} Parameter := fun _ => domain
  have compare (other : Fin 3) := (elementsEqual_realizable domain).onResults inputs (fun _ _ => True)
    (fun choice _ arguments => if choice then arguments.val other else arguments.val 2) (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument inputs 2 (fun _ _ => True)
      · exact Realizable.argument inputs other (fun _ _ => True))
  have second := Realizable.conditional inputs domain (fun _ _ => True)
    (fun _ arguments => decide (arguments.val 2 = arguments.val 1))
    (fun _ arguments => arguments.val 0) (fun _ arguments => arguments.val 2)
    (compare 1) (Realizable.argument inputs 0 (fun _ _ => True)) (Realizable.argument inputs 2 (fun _ _ => True))
  have complete := Realizable.conditional inputs domain (fun _ _ => True)
    (fun _ arguments => decide (arguments.val 2 = arguments.val 0))
    (fun _ arguments => arguments.val 1)
    (fun _ arguments => if decide (arguments.val 2 = arguments.val 1) then arguments.val 0 else arguments.val 2)
    (compare 0) (Realizable.argument inputs 1 (fun _ _ => True)) second
  apply complete.withSpecification (elementsSwap domain).precondition (elementsSwap domain).compute (by intros; trivial)
  intro sizes arguments valid
  simp [elementsSwap, Equiv.swap_apply_def]

end Polytime2.Computation
