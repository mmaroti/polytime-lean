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

import Polytime2.Computation.Layout
import Polytime2.StandardSizeReadContract

/-! # Reading a unary size as a bounded mathematical natural -/

namespace Polytime2.Computation

/-- The count is size `false`; size `true` is its binary result capacity.
There are no ordinary arguments, since both unary headers are implicit inputs. -/
noncomputable def readSize : Computation Bool Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.binaryNaturals true
  precondition sizes _ := sizes false < 2 ^ sizes true
  compute sizes arguments := ⟨sizes false, arguments.property⟩

namespace Realizable.Internal

private def sizeReadPlacement : PublicTape Bool Empty ↪ Bool ⊕ Bool :=
  (Function.Embedding.refl Bool).sumMap
    ⟨(fun _ => false), by intro first second equal; fin_cases first; fin_cases second; rfl⟩

end Realizable.Internal

open Realizable.Internal in
theorem readSize_realizable : readSize.Realizable := by
  refine ofNamedLayout readSize StandardSizeRead.domains StandardSizeRead.argumentReadOnly
    StandardSizeRead.sizeTapes StandardSizeRead.outputTapes StandardSizeRead.algorithm
    StandardSizeRead.entry StandardSizeRead.exit _ _ StandardSizeRead.contract
    sizeReadPlacement (by intro role; fin_cases role <;> rfl)
    (by intro role; fin_cases role <;> rfl)
    (by intro name outside; cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (CallingConvention.encoded (EncodedDomain.binaryNaturals true) sizes)
  apply Fin.ext
  exact correct

end Polytime2.Computation
