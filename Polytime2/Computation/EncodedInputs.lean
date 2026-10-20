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

import Polytime2.Computation.Conditional
import Polytime2.Computation.Fields

/-! # Restricting mathematical inputs while retaining their canonical bits -/

namespace Polytime2.Computation.Realizable

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- An encoding-preserving input map may restrict a domain without being
surjective. Existing field copying and composition supply its realization. -/
theorem withEncodedInputs {computation : Computation Parameter InputName}
    (ready : computation.Realizable) (inputs : InputName → EncodedDomain Parameter)
    (map : ∀ name sizes, (inputs name).Carrier sizes → (computation.inputDomains name).Carrier sizes)
    (sameEncoding : ∀ name sizes value,
      EncodedDomain.ArrayEncoding.bits ((inputs name).encode sizes value) =
        EncodedDomain.ArrayEncoding.bits ((computation.inputDomains name).encode sizes (map name sizes value)))
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (compatible : ∀ sizes arguments, allowed sizes arguments →
      computation.precondition sizes (fun name => map name sizes (arguments name))) :
    (Computation.mk inputs computation.outputDomain allowed
      (fun sizes arguments => computation.compute sizes
        ⟨(fun name => map name sizes (arguments.val name)), compatible sizes arguments.val arguments.property⟩)).Realizable := by
  apply ready.onResults inputs allowed
    (fun name sizes arguments => map name sizes (arguments.val name))
    (by intro sizes arguments; exact compatible sizes arguments.val arguments.property)
  intro name
  have copied := Internal.fieldProjection (inputs name) (computation.inputDomains name) 0
    (fun _ _ => True) (fun sizes value => map name sizes value.val) (by
      intro sizes value
      exact ⟨[], [], by simpa using sameEncoding name sizes value.val, by simp⟩)
  exact copied.onResults inputs allowed (fun _ _ arguments => arguments.val name)
    (by intros; trivial) (by intro _; exact argument inputs name allowed)

end Polytime2.Computation.Realizable
