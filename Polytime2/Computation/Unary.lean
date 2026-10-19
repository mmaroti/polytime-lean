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
import Polytime2.Arithmetic.BinaryScan

/-! # Packaging existing unary routines without exposing their tape names -/

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

-- carrierLevel: mathematical values represented by the existing unary routine.
universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

private def unaryPlacement : PublicTape Parameter Unit ↪ Parameter ⊕ Bool :=
  (Function.Embedding.refl Parameter).sumMap
    ⟨(fun role => match role with | .inl _ => false | .inr _ => true), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

/-- The existing size/input/output convention has no private scratch. -/
theorem ofUnaryRealizes (computation : Computation.{carrierLevel} Parameter Unit)
    {State : Type} [Fintype State]
    (machine : Machine (Alphabet (Parameter ⊕ Bool)) State) (entry exit : State)
    (certificate : CallingConvention.Realizes
      (StandardBinaryScan.domains (computation.inputDomains ()) computation.outputDomain)
      StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes machine entry exit
      (fun sizes input => computation.precondition sizes (fun _ => input ⟨.inr false, rfl⟩))
      (fun sizes input output => ∃ valid : computation.precondition sizes
          (fun _ => input ⟨.inr false, rfl⟩),
        output () = computation.compute sizes
          ⟨(fun _ => input ⟨.inr false, rfl⟩), valid⟩)) : computation.Realizable := by
  refine ofNamedLayout computation
    (StandardBinaryScan.domains (computation.inputDomains ()) computation.outputDomain)
    StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes
    machine entry exit _ _ certificate unaryPlacement
    (by rintro (parameter | argument | result) <;> rfl)
    (by rintro (parameter | argument | result) <;> rfl)
    (by intro name outside; cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr flag => cases flag with
        | false => exact False.elim (outside ⟨.inr (.inl ()), rfl⟩)
        | true => rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨good, result⟩ := correct
  exact congrArg (encoded computation.outputDomain sizes) result

end Polytime2.Computation.Realizable.Internal
