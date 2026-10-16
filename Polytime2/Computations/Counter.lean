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

import Polytime2.Computation.Unary
import Polytime2.StandardBinaryIncrement
import Polytime2.StandardBinaryDecrement
import Polytime2.StandardBinaryGuard

/-! # Public computations for copying and fixed-capacity increment -/

namespace Polytime2.Computation

-- carrierLevel: mathematical elements copied without changing their encoding.
universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

def copy (domain : EncodedDomain.{0, carrierLevel} Parameter) : Computation Parameter Unit where
  inputDomains _ := domain
  outputDomain := domain
  precondition _ _ := True
  compute _ arguments := arguments.val ()

/-- The public certificate mentions no controller or scratch layout. -/
theorem copy_realizable (domain : EncodedDomain.{0, carrierLevel} Parameter) :
    (copy domain).Realizable := by
  refine Realizable.Internal.ofUnaryRealizes (copy domain)
    StandardTerminatedCopy.algorithm 0 2 ?_
  let equivalence : ∀ name sizes,
      (StandardBinaryScan.domains domain domain name).Carrier sizes ≃
        (StandardTerminatedCopy.domains domain name).Carrier sizes := by
    intro name sizes
    cases name with
    | inl parameter => exact Equiv.refl _
    | inr flag => cases flag <;> exact Equiv.refl _
  refine CallingConvention.realizes_reindex equivalence
    (by intro name sizes; cases name with | inl _ => rfl | inr flag => cases flag <;> rfl)
    (by intro name sizes value; cases name with | inl _ => rfl | inr flag => cases flag <;> rfl)
    StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes StandardTerminatedCopy.outputTapes
    StandardTerminatedCopy.algorithm 0 2 _ _ _ _
    (by intro sizes input valid; trivial) ?_ (StandardTerminatedCopy.contract domain)
  intro sizes input output equal
  exact ⟨True.intro, equal⟩

noncomputable def counterIncrement (capacity : Parameter) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.binaryNaturals capacity
  outputDomain := EncodedDomain.binaryNaturals capacity
  precondition _ _ := True
  compute sizes arguments := StandardBinaryIncrement.next capacity sizes (arguments.val ())

/-- Increment realizes modular addition at the assigned capacity. -/
theorem counterIncrement_realizable (capacity : Parameter) :
    (counterIncrement capacity).Realizable := by
  refine Realizable.Internal.ofUnaryRealizes (counterIncrement capacity)
    (StandardBinaryScan.algorithm BinaryScan.increment) (.inl (.inl true)) (.inr ()) ?_
  apply (StandardBinaryIncrement.contract capacity).postcondition
  intro sizes input output equal
  exact ⟨True.intro, equal⟩

/-- The predecessor is specified only for positive inputs. -/
noncomputable def counterDecrement (capacity : Parameter) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.binaryNaturals capacity
  outputDomain := EncodedDomain.binaryNaturals capacity
  precondition _ arguments := 0 < (arguments ()).val
  compute sizes arguments := StandardBinaryDecrement.compute capacity sizes (arguments.val ())

theorem counterDecrement_realizable (capacity : Parameter) :
    (counterDecrement capacity).Realizable := by
  refine Realizable.Internal.ofUnaryRealizes (counterDecrement capacity)
    (StandardBinaryScan.algorithm StandardBinaryDecrement.update)
    StandardBinaryDecrement.entry StandardBinaryDecrement.exit ?_
  apply (StandardBinaryDecrement.contract capacity).postconditionWithHypothesis
  intro sizes input output valid equal
  exact ⟨valid, equal⟩

noncomputable def counterNonzero : Computation Unit Unit where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.booleans
  precondition _ _ := True
  compute _ arguments := decide (0 < (arguments.val ()).val)

theorem counterNonzero_realizable : counterNonzero.Realizable := by
  refine Realizable.Internal.ofUnaryRealizes counterNonzero
    StandardBinaryGuard.algorithm (false, 0) (false, 2) ?_
  apply StandardBinaryGuard.contract.postcondition
  intro sizes input output equal
  exact ⟨True.intro, equal⟩

end Polytime2.Computation
