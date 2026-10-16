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

private noncomputable def gcdScratchDomains (name : Fin 9) : EncodedDomain Unit :=
  StandardGcd.domains (.inr ⟨name.val, by omega⟩)

private noncomputable def gcdLayout : Unit ⊕ Fin 12 ≃ TapeName gcd (Fin 9) where
  toFun
    | .inl parameter => .inl parameter
    | .inr name => if privateTape : name.val < 9 then scratchTape gcd ⟨name.val, privateTape⟩
        else if name.val = 9 then inputTape gcd false
        else if name.val = 10 then inputTape gcd true
        else outputTape gcd
  invFun
    | .inl parameter => .inl parameter
    | .inr (.inl false) => .inr 9
    | .inr (.inl true) => .inr 10
    | .inr (.inr (.inl _)) => .inr 11
    | .inr (.inr (.inr name)) => .inr ⟨name.val, by omega⟩
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · fin_cases scratch <;> rfl

private theorem gcdDomains (name : Unit ⊕ Fin 12) :
    domains gcd gcdScratchDomains (gcdLayout name) = StandardGcd.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def gcdValues (name : Unit ⊕ Fin 12) (sizes : Unit → ℕ) :
    (domains gcd gcdScratchDomains (gcdLayout name)).Carrier sizes ≃
      (StandardGcd.domains name).Carrier sizes :=
  Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (gcdDomains name))

private theorem gcdReadOnly (name : Unit ⊕ Fin 12) :
    StandardGcd.argumentReadOnly name = readOnly gcd (gcdLayout name) := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

end Realizable.Internal

open Realizable.Internal in
/-- The physical certificate is consumed only inside this foundational proof. -/
theorem gcd_realizable : gcd.Realizable := by
  refine ofLayout gcd gcdScratchDomains StandardGcd.domains StandardGcd.argumentReadOnly
    StandardGcd.sizeTapes StandardGcd.outputTapes StandardGcd.algorithm StandardGcd.entry StandardGcd.exit
    _ _ StandardGcd.contract gcdLayout.toEmbedding gcdValues ?_ ?_ gcdReadOnly
    (by intro parameter; rfl) () rfl ?_ ?_
  · intro name sizes
    exact congrArg (fun domain => domain.width sizes) (gcdDomains name)
  · intro name sizes value
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  · intro sizes input valid
    exact valid
  · intro sizes input valid output result
    apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
    apply Fin.ext
    exact result

end Polytime2.Computation
