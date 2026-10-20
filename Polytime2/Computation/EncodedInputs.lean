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

import Polytime2.Computation.Reindex

/-! # Restricting mathematical inputs while retaining their canonical bits -/

namespace Polytime2.Computation.Realizable

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- An encoding-preserving input map may restrict a domain without being
surjective. The original machine and runtime bound are reused directly. -/
theorem withEncodedInputs {computation : Computation Parameter InputName}
    (ready : computation.Realizable) (inputs : InputName → EncodedDomain Parameter)
    (map : ∀ name sizes, (inputs name).Carrier sizes → (computation.inputDomains name).Carrier sizes)
    (sameWidth : ∀ name sizes,
      (inputs name).width sizes = (computation.inputDomains name).width sizes)
    (sameEncoding : ∀ name sizes value,
      EncodedDomain.ArrayEncoding.bits ((inputs name).encode sizes value) =
        EncodedDomain.ArrayEncoding.bits ((computation.inputDomains name).encode sizes (map name sizes value)))
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (compatible : ∀ sizes arguments, allowed sizes arguments →
      computation.precondition sizes (fun name => map name sizes (arguments name))) :
    (Computation.mk inputs computation.outputDomain allowed
      (fun sizes arguments => computation.compute sizes
        ⟨(fun name => map name sizes (arguments.val name)), compatible sizes arguments.val arguments.property⟩)).Realizable := by
  exact ready.withEncoding map sameWidth (by intros; rfl)
    (fun name sizes value => congrArg CallingConvention.tape (sameEncoding name sizes value))
    compatible (by intros; rfl)

end Polytime2.Computation.Realizable
