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
import Polytime2.Computation.Substitution
import Polytime2.Primitives.BitOperations
import Polytime2.Arithmetic.BinaryRemainder

/-! # Remainder with private working capacity

At width b, inputs and output are binary naturals below 2^b. Only the divisor
must be positive. Operands are preserved, and one extra working bit is private.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

namespace Realizable.Internal

/-- The long-division controller needs room for a shifted partial remainder. -/
noncomputable def binaryRemainderWithCapacity : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition sizes arguments := 0 < (arguments true).val ∧ 2 * (arguments true).val ≤ 2 ^ sizes ()
  compute _ arguments := ⟨(arguments.val false).val % (arguments.val true).val,
    lt_trans (Nat.mod_lt _ arguments.property.1) (arguments.val true).isLt⟩

private def remainderPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 7 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 6 | .inl true => 1 | .inr _ => 0), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

theorem binaryRemainderWithCapacity_realizable : binaryRemainderWithCapacity.Realizable := by
  refine ofNamedLayout binaryRemainderWithCapacity StandardBinaryRemainder.domains StandardBinaryRemainder.argumentReadOnly
    StandardBinaryRemainder.sizeTapes StandardBinaryRemainder.outputTapes StandardBinaryRemainder.algorithm StandardBinaryRemainder.entry StandardBinaryRemainder.exit
    _ _ StandardBinaryRemainder.contract remainderPlacement
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
  apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
  apply Fin.ext
  exact correct

end Realizable.Internal

/-- Remainder at the operands' original width requires only a positive divisor. -/
noncomputable def binaryRemainder : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition _ arguments := 0 < (arguments true).val
  compute _ arguments := ⟨(arguments.val false).val % (arguments.val true).val,
    lt_trans (Nat.mod_lt _ arguments.property) (arguments.val true).isLt⟩

namespace Realizable.Internal

private noncomputable def remainderSizes : Unit → MvPolynomial Unit ℕ :=
  fun _ => MvPolynomial.X () + 1

private theorem remainderSizes_eval (sizes : Unit → ℕ) :
    SizeSubstitution.assignment remainderSizes sizes () = sizes () + 1 := by
  simp [SizeSubstitution.assignment, remainderSizes]

private noncomputable def remainderWide : EncodedDomain Unit :=
  (EncodedDomain.binaryNaturals ()).substitute remainderSizes

private def remainderWiden (sizes : Unit → ℕ) (value : Fin (2 ^ sizes ())) :
    remainderWide.Carrier sizes :=
  ⟨value.val, by
    rw [remainderSizes_eval]
    exact value.isLt.trans_le (pow_le_pow_right₀ (by decide) (by omega))⟩

private theorem remainderWiden_realizable :
    (encodingMap (EncodedDomain.binaryNaturals ()) remainderWide remainderWiden).Realizable := by
  refine zeroExtendEncoding_realizable (EncodedDomain.binaryNaturals ()) remainderWide 1 remainderWiden ?_ ?_
  · intro sizes
    simp only [remainderWide, EncodedDomain.width, EncodedDomain.substitute,
      EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      SizeSubstitution.polynomial_eval, MvPolynomial.eval_X, map_one]
    exact remainderSizes_eval sizes
  · intro sizes value
    simp only [remainderWide, EncodedDomain.substitute, EncodedDomain.binaryNaturals,
      EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast]
    have widened : BitVec.ofFin (remainderWiden sizes value) =
        (BitVec.ofFin value).setWidth (SizeSubstitution.assignment remainderSizes sizes ()) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofFin, BitVec.toNat_setWidth]
      exact (Nat.mod_eq_of_lt (remainderWiden sizes value).isLt).symm
    rw [widened, EncodedDomain.bits_setWidth _ (by rw [remainderSizes_eval]; omega)]
    simp [remainderSizes_eval]

private noncomputable def remainderNarrow : Computation Unit Unit :=
  encodingMap remainderWide (EncodedDomain.binaryNaturals ())
    (fun sizes value => ((BitVec.ofFin value).setWidth (sizes ())).toFin)

private theorem remainderNarrow_realizable : remainderNarrow.Realizable := by
  apply Realizable.Internal.fieldProjection remainderWide (EncodedDomain.binaryNaturals ()) 0
    (fun _ _ => True) (fun sizes value => ((BitVec.ofFin value.val).setWidth (sizes ())).toFin)
  intro sizes value
  refine ⟨[], (EncodedDomain.ArrayEncoding.bits (BitVec.ofFin value.val)).drop (sizes ()), ?_, by simp⟩
  simp only [remainderWide, EncodedDomain.substitute, EncodedDomain.binaryNaturals,
    EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast, BitVec.ofFin_toFin, List.nil_append]
  rw [EncodedDomain.bits_setWidth_take _ (by rw [remainderSizes_eval]; omega)]
  simpa only [EncodedDomain.ArrayEncoding.bits_cast] using
    (List.take_append_drop (sizes ()) (EncodedDomain.ArrayEncoding.bits (BitVec.ofFin value.val))).symm

end Realizable.Internal

open Realizable.Internal in
theorem binaryRemainder_realizable : binaryRemainder.Realizable := by
  have widened := (binaryRemainderWithCapacity_realizable.substitute remainderSizes).onResults
    binaryRemainder.inputDomains binaryRemainder.precondition
    (fun name sizes arguments => remainderWiden sizes (arguments.val name))
    (by
      intro sizes arguments
      change 0 < (arguments.val true).val ∧
        2 * (arguments.val true).val ≤ 2 ^ SizeSubstitution.assignment remainderSizes sizes ()
      rw [remainderSizes_eval, pow_succ]
      exact ⟨arguments.property, by have bound := (arguments.val true).isLt; omega⟩)
    (by
      intro name
      exact remainderWiden_realizable.onResults binaryRemainder.inputDomains binaryRemainder.precondition
        (fun _ _ arguments => arguments.val name) (by intros; trivial)
        (by intro _; exact Realizable.argument _ name _))
  have narrowed := widened.followedBy remainderNarrow_realizable rfl (by intros; trivial)
  exact narrowed.withSpecification binaryRemainder.precondition binaryRemainder.compute
    (by intro sizes arguments valid; exact valid) (by
      intro sizes arguments valid
      apply Fin.ext
      simp only [followedBy, remainderNarrow, encodingMap, unaryMap, onResults, substitute,
        binaryRemainderWithCapacity, remainderWiden, binaryRemainder]
      change (BitVec.setWidth (sizes ()) _).toNat = _
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt ((Nat.mod_lt _ valid).trans (arguments true).isLt))

end Polytime2.Computation
