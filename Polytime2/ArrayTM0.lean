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

import Polytime2.CallingConventionSimulation
import Polytime2.StandardArrayLookupSizedContract
import Polytime2.StandardArrayUpdate

/-! # Polynomial TM0 realization of standard array access

Both access modes use the same finite-track simulator. Canonical inputs and
arbitrary writable regions satisfy its polynomial input-storage requirement.
-/

namespace Polytime2.Array

-- parameterLevel: names of the caller's unary size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [DecidableEq Parameter]

/-- Lookup's mathematical contract transfers to `TM0.init`, including immutable
arguments and valid scratch on return. -/
theorem lookup_realizes_tm0
    (element : EncodedDomain.{parameterLevel, 0} Parameter) (elementWidth : ℕ)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.TM0Realizes
      (StandardArrayLookupSized.domainsSized element indexCapacity length)
      StandardArrayLookupSized.argumentReadOnly StandardArrayLookupSized.sizeTapes
      (StandardArrayLookupSized.algorithmSized elementWidth)
      (StandardArrayLookup.entry elementWidth)
      (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
        MvPolynomial.eval assignment length)
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
          output ⟨.inr 2, rfl⟩ = input ⟨.inr 1, rfl⟩
            ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) :=
  (StandardArrayLookupSized.contractSized element elementWidth indexCapacity length fixedWidth).tm0

/-- Update overwrites its complete fresh result, including when it initially
contains blanks, and the same mathematical update is realized on TM0. -/
theorem update_realizes_tm0
    (element : EncodedDomain.{parameterLevel, 0} Parameter) (elementWidth : ℕ)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.TM0Realizes
      (StandardArrayUpdate.domainsSized element indexCapacity length)
      StandardArrayUpdate.argumentReadOnlySized StandardArrayUpdate.sizeTapesSized
      (StandardArrayUpdate.algorithmSized elementWidth)
      (StandardArrayUpdate.entry elementWidth)
      (fun assignment input => (input ⟨.inr 0, rfl⟩).val <
        MvPolynomial.eval assignment length)
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
          output ⟨.inr 3, rfl⟩ = Function.update (input ⟨.inr 1, rfl⟩)
            ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) :=
  (StandardArrayUpdate.contractSized element elementWidth indexCapacity length fixedWidth).tm0

end Polytime2.Array
