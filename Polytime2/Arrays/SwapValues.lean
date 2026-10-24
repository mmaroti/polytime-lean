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

import Polytime2.Computation.Swap
import Polytime2.Arrays.Transform

/-! # Swapping two values throughout an array

A pointwise swap updates a permutation's image table. It reuses the generic
array transformer, keeping the array length and element codec unchanged.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Exchange the two context values in every entry of the supplied array. -/
noncomputable def arraySwapValues (domain : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ) := by
  classical
  exact arrayTransform (fun _ : Bool => domain) domain domain length
    (fun _ context value => Equiv.swap (context false) (context true) value)

/-- Pointwise swapping is the certified scalar swap lifted through array transformation. -/
theorem arraySwapValues_realizable (domain : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ) :
    (arraySwapValues domain length).Realizable := by
  classical
  let operation sizes (context : Bool → domain.Carrier sizes) (value : domain.Carrier sizes) :=
    Equiv.swap (context false) (context true) value
  apply arrayTransform_realizable (fun _ : Bool => domain) domain domain length operation
  let step := arrayTransformStep (fun _ : Bool => domain) domain domain operation
  apply (elementsSwap_realizable domain).onResults step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inl false)
      | 1 => arguments.val (.inl true)
      | 2 => arguments.val (.inr ())) (by intros; trivial)
  intro name
  fin_cases name
  · exact Realizable.argument step.inputDomains (.inl false) step.precondition
  · exact Realizable.argument step.inputDomains (.inl true) step.precondition
  · exact Realizable.argument step.inputDomains (.inr ()) step.precondition

end Polytime2.Computation
