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
import Polytime2.StandardGcd

/-! # Gcd as a mathematical computation with an existential certificate -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

/-- Gcd fits the operands' binary capacity, including when either operand is zero. -/
def gcdValue (bits : ℕ) (left right : Fin (2 ^ bits)) : Fin (2 ^ bits) :=
  ⟨Nat.gcd left.val right.val, by
    by_cases zero : left.val = 0
    · simpa only [zero, Nat.gcd_zero_left] using right.isLt
    · exact lt_of_le_of_lt (Nat.gcd_le_left right.val (Nat.pos_of_ne_zero zero)) left.isLt⟩

/-- False names the first operand and true the second; capacity is an immutable size. -/
noncomputable def gcd : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition sizes arguments := 2 * (arguments true).val ≤ 2 ^ sizes ()
  compute sizes arguments := gcdValue (sizes ()) (arguments.val false) (arguments.val true)

namespace Realizable.Internal

private def gcdPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 12 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 9 | .inl true => 10 | .inr _ => 11), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
/-- The physical certificate is consumed only inside this foundational proof. -/
theorem gcd_realizable : gcd.Realizable := by
  refine ofNamedLayout gcd StandardGcd.domains StandardGcd.argumentReadOnly
    StandardGcd.sizeTapes StandardGcd.outputTapes StandardGcd.algorithm StandardGcd.entry StandardGcd.exit
    _ _ StandardGcd.contract gcdPlacement
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
  intro sizes input valid output result
  apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
  apply Fin.ext
  exact result

end Polytime2.Computation
