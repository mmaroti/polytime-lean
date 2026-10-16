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
import Polytime2.StandardMatrixAddressContract

/-! # Row-major addresses as a mathematical computation -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

/-- Sizes are binary capacity, row count, and column count. Arguments are the
row and column indices. Address arithmetic requires only that its result fits;
checking whether the coordinate belongs to a matrix is the caller's task. -/
noncomputable def matrixAddress : Computation (Fin 3) Bool where
  inputDomains _ := EncodedDomain.binaryNaturals 0
  outputDomain := EncodedDomain.binaryNaturals 0
  precondition sizes arguments := sizes 2 < 2 ^ sizes 0 ∧
    (arguments false).val * sizes 2 + (arguments true).val < 2 ^ sizes 0
  compute sizes arguments :=
    ⟨(arguments.val false).val * sizes 2 + (arguments.val true).val, arguments.property.2⟩

namespace Realizable.Internal

private def addressLayout (name : Fin 3 ⊕ Fin 9) : Fin 3 ⊕ (Bool ⊕ (Unit ⊕ Fin 9)) :=
  match name with
  | .inl parameter => .inl parameter
  | .inr 1 => .inr (.inl false)
  | .inr 6 => .inr (.inl true)
  | .inr 7 => .inr (.inr (.inl ()))
  | .inr privateTape => .inr (.inr (.inr privateTape))

private def addressSource : Fin 3 ⊕ (Bool ⊕ (Unit ⊕ Fin 9)) → Fin 3 ⊕ Fin 9
  | .inl parameter => .inl parameter
  | .inr (.inl false) => .inr 1
  | .inr (.inl true) => .inr 6
  | .inr (.inr (.inl _)) => .inr 7
  | .inr (.inr (.inr name)) => .inr name

private theorem addressLayout_leftInverse : Function.LeftInverse addressSource addressLayout := by
  intro name
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def addressEmbedding : Fin 3 ⊕ Fin 9 ↪ Fin 3 ⊕ (Bool ⊕ (Unit ⊕ Fin 9)) :=
  ⟨addressLayout, addressLayout_leftInverse.injective⟩

private noncomputable def addressScratch (name : Fin 9) : EncodedDomain (Fin 3) :=
  StandardMatrixAddress.domains (.inr name)

private theorem addressDomains (name : Fin 3 ⊕ Fin 9) :
    domains matrixAddress addressScratch (addressEmbedding name) = StandardMatrixAddress.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

end Realizable.Internal

open Realizable.Internal in
theorem matrixAddress_realizable : matrixAddress.Realizable := by
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (addressDomains name))
  refine ofLayout matrixAddress addressScratch StandardMatrixAddress.domains
    StandardMatrixAddress.readOnly StandardMatrixAddress.sizeTapes StandardMatrixAddress.outputTapes
    StandardMatrixAddress.machine StandardMatrixAddress.entry StandardMatrixAddress.exit _ _
    StandardMatrixAddress.contract addressEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (addressDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes)
  exact Fin.ext correct

end Polytime2.Computation
