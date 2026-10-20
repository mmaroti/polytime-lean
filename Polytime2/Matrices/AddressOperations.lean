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
import Polytime2.Matrices.AddressContract

/-! # Row-major addresses as a mathematical computation -/

namespace Polytime2.Computation.Realizable.Internal

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

private def addressPlacement : PublicTape (Fin 3) Bool ↪ Fin 3 ⊕ Fin 9 :=
  (Function.Embedding.refl (Fin 3)).sumMap
    ⟨(fun role => match role with | .inl false => 1 | .inl true => 6 | .inr _ => 7), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

theorem matrixAddress_realizable : matrixAddress.Realizable := by
  refine ofNamedLayout matrixAddress StandardMatrixAddress.domains StandardMatrixAddress.readOnly
    StandardMatrixAddress.sizeTapes StandardMatrixAddress.outputTapes StandardMatrixAddress.machine StandardMatrixAddress.entry StandardMatrixAddress.exit
    _ _ StandardMatrixAddress.contract addressPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes)
  exact Fin.ext correct

end Polytime2.Computation.Realizable.Internal
