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
import Polytime2.Computation.Conditional
import Polytime2.Arithmetic.WidthOperations
import Polytime2.Arithmetic.Gcd

/-! # Gcd as a mathematical computation with an existential certificate -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

/-- Gcd fits the operands' binary capacity, including when either operand is zero. -/
def gcdValue (bits : ℕ) (left right : Fin (2 ^ bits)) : Fin (2 ^ bits) :=
  ⟨Nat.gcd left.val right.val, by
    by_cases zero : left.val = 0
    · simpa only [zero, Nat.gcd_zero_left] using right.isLt
    · exact lt_of_le_of_lt (Nat.gcd_le_left right.val (Nat.pos_of_ne_zero zero)) left.isLt⟩

/-- Gcd has no capacity restriction on either operand. -/
noncomputable def gcd : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition _ _ := True
  compute sizes arguments := gcdValue (sizes ()) (arguments.val false) (arguments.val true)

namespace Realizable.Internal

/-- The Euclidean controller requires a spare bit for its divisor. -/
noncomputable def gcdWithCapacity : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition sizes arguments := 2 * (arguments true).val ≤ 2 ^ sizes ()
  compute sizes arguments := gcdValue (sizes ()) (arguments.val false) (arguments.val true)

private def gcdPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 12 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 9 | .inl true => 10 | .inr _ => 11), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

/-- The physical certificate is consumed only inside this foundational proof. -/
theorem gcdWithCapacity_realizable : gcdWithCapacity.Realizable := by
  refine ofNamedLayout gcdWithCapacity StandardGcd.domains StandardGcd.argumentReadOnly
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

end Realizable.Internal

open Realizable.Internal in
theorem gcd_realizable : gcd.Realizable := by
  have widened := (gcdWithCapacity_realizable.substitute extraBitSizes).onResults
    gcd.inputDomains gcd.precondition
    (fun name sizes arguments => extraBitWiden sizes (arguments.val name))
    (by
      intro sizes arguments
      change 2 * (arguments.val true).val ≤
        2 ^ SizeSubstitution.assignment extraBitSizes sizes ()
      rw [extraBitSizes_eval, pow_succ]
      have bound := (arguments.val true).isLt
      omega)
    (by
      intro name
      exact extraBitWiden_realizable.onArguments gcd.inputDomains gcd.precondition
        (fun _ => name) (by intro _; rfl) (by intros; trivial))
  have narrowed := widened.followedBy extraBitNarrow_realizable rfl (by intros; trivial)
  exact narrowed.withSpecification gcd.precondition gcd.compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Fin.ext
      simp only [followedBy, extraBitNarrow, encodingMap, unaryMap, onResults, substitute,
        gcdWithCapacity, extraBitWiden, gcd, gcdValue]
      change (BitVec.setWidth (sizes ()) _).toNat = _
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (gcdValue (sizes ()) (arguments false) (arguments true)).isLt)

end Polytime2.Computation
