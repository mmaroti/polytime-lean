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

import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arrays.Tabulate

/-! # Runtime prefix selection inside a fixed-length traversal

An ordinary coordinate bounded by `length + 1` specifies the active prefix,
including empty and full prefixes. The private traversal representation is an
array of flags. Its width and comparison capacities are derived internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Prepare internal traversal flags from the mathematical active-prefix length. -/
noncomputable def arrayPrefixFlags (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ : Unit => arrayPosition (length + 1)) booleans length
    (fun _ context index => decide (index.val < (context ()).val))

/-- The prefix guard uses the shared comparison for independently bounded coordinates. -/
theorem arrayPrefixFlags_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayPrefixFlags length).Realizable := by
  apply arrayTabulate_realizable
  let step := arrayTransformStep (fun _ : Unit => arrayPosition (length + 1))
    (arrayPosition length) booleans (fun _ context index => decide (index.val < (context ()).val))
  exact (positionsLess_realizable length (length + 1)).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with | false => arguments.val (.inr ()) | true => arguments.val (.inl ()))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr ()) step.precondition
      · exact Realizable.argument step.inputDomains (.inl ()) step.precondition)

/-- A token is selected exactly when its position is strictly before the runtime prefix length. -/
theorem arrayPrefixFlags_selected (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (count : (arrayPosition (length + 1)).Carrier sizes) (index : Fin (MvPolynomial.eval sizes length)) :
    (arrayPrefixFlags length).compute sizes ⟨(fun _ => count), trivial⟩ index = true ↔ index.val < count.val := by
  change decide (index.val < count.val) = true ↔ index.val < count.val
  exact ⟨of_decide_eq_true, fun before => by simp only [before, decide_true]⟩

end Polytime2.Computation.Realizable.Internal
