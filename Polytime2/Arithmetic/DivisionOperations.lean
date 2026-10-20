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
import Polytime2.Computation.Records
import Polytime2.Computation.Conditional
import Polytime2.Arithmetic.WidthOperations
import Polytime2.Arithmetic.DivisionResult

/-! # Certified quotient and remainder at the operands' original width

For `a b : Fin (2^w)` with `0 < b`, return `(a / b, a % b)` in the ordinary
product `Fin (2^w) × Fin (2^w)`. Both results fit at width `w`. A private extra
bit makes the restoring-division shift exact; callers supply only `w`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

namespace Realizable.Internal

noncomputable def binaryDivisionWithCapacity : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := (EncodedDomain.binaryNaturals ()).prod (EncodedDomain.binaryNaturals ())
  precondition sizes arguments := 0 < (arguments true).val ∧ 2 * (arguments true).val ≤ 2 ^ sizes ()
  compute _ arguments :=
    (⟨(arguments.val false).val / (arguments.val true).val,
      lt_of_le_of_lt (Nat.div_le_self _ _) (arguments.val false).isLt⟩,
     ⟨(arguments.val false).val % (arguments.val true).val,
      (Nat.mod_lt _ arguments.property.1).trans (arguments.val true).isLt⟩)

private def divisionPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 9 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 6 | .inl true => 1 | .inr _ => 8), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

theorem binaryDivisionWithCapacity_realizable : binaryDivisionWithCapacity.Realizable := by
  refine ofNamedLayout binaryDivisionWithCapacity
    StandardBinaryDivision.Packed.domains StandardBinaryDivision.Packed.readOnly
    StandardBinaryDivision.Packed.sizeTapes StandardBinaryDivision.Packed.outputTapes
    StandardBinaryDivision.Packed.algorithm StandardBinaryDivision.Packed.entry StandardBinaryDivision.Packed.exit
    _ _ StandardBinaryDivision.Packed.contract divisionPlacement
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
  apply congrArg (encoded _ sizes)
  exact Prod.ext (Fin.ext correct.1) (Fin.ext correct.2)

noncomputable def narrowDivisionPair : Computation Unit Unit :=
  unaryMap (extraBitDomain.prod extraBitDomain)
    ((EncodedDomain.binaryNaturals ()).prod (EncodedDomain.binaryNaturals ()))
    (fun _ _ => True) (fun sizes value =>
      (((BitVec.ofFin value.val.1).setWidth (sizes ())).toFin,
       ((BitVec.ofFin value.val.2).setWidth (sizes ())).toFin))

theorem narrowDivisionPair_realizable : narrowDivisionPair.Realizable := by
  have first := (pairProjection_realizable extraBitDomain extraBitDomain false).followedBy
    extraBitNarrow_realizable rfl (by intros; trivial)
  have second := (pairProjection_realizable extraBitDomain extraBitDomain true).followedBy
    extraBitNarrow_realizable rfl (by intros; trivial)
  exact Realizable.pairOutputs (fun _ : Unit => extraBitDomain.prod extraBitDomain)
    (EncodedDomain.binaryNaturals ()) (EncodedDomain.binaryNaturals ()) (fun _ _ => True)
    _ _ first second

end Realizable.Internal

/-- Unsigned quotient and remainder require only a positive divisor. -/
noncomputable def binaryDivision : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := (EncodedDomain.binaryNaturals ()).prod (EncodedDomain.binaryNaturals ())
  precondition _ arguments := 0 < (arguments true).val
  compute _ arguments :=
    (⟨(arguments.val false).val / (arguments.val true).val,
      lt_of_le_of_lt (Nat.div_le_self _ _) (arguments.val false).isLt⟩,
     ⟨(arguments.val false).val % (arguments.val true).val,
      (Nat.mod_lt _ arguments.property).trans (arguments.val true).isLt⟩)

/-- The returned pair satisfies Euclidean division with a strict remainder bound. -/
theorem binaryDivision_correct (sizes : Unit → ℕ) (arguments : binaryDivision.Arguments sizes)
    (valid : binaryDivision.precondition sizes arguments) :
    let answer := binaryDivision.compute sizes ⟨arguments, valid⟩
    (arguments false).val = (arguments true).val * answer.1.val + answer.2.val ∧
      answer.2.val < (arguments true).val :=
  ⟨(Nat.div_add_mod _ _).symm, Nat.mod_lt _ valid⟩

open Realizable.Internal in
theorem binaryDivision_realizable : binaryDivision.Realizable := by
  have substituted := binaryDivisionWithCapacity_realizable.substitute extraBitSizes
  have transported := substituted.reindexDomains (fun _ => extraBitDomain)
    (extraBitDomain.prod extraBitDomain)
    (fun _ _ => Equiv.refl _) (fun _ => Equiv.refl _)
    (by intros; rfl)
    (by intros; simp [substitute, binaryDivisionWithCapacity, EncodedDomain.substitute_width,
      extraBitDomain, EncodedDomain.width])
    (by intros; rfl)
    (by intros; simp [substitute, binaryDivisionWithCapacity,
      EncodedDomain.substitute_encode_bits, extraBitDomain,
      EncodedDomain.ArrayEncoding.bits_append]; rfl)
  have widened := transported.onResults binaryDivision.inputDomains binaryDivision.precondition
    (fun name sizes arguments => extraBitWiden sizes (arguments.val name))
    (by
      intro sizes arguments
      change 0 < (arguments.val true).val ∧
        2 * (arguments.val true).val ≤ 2 ^ SizeSubstitution.assignment extraBitSizes sizes ()
      rw [extraBitSizes_eval, pow_succ]
      exact ⟨arguments.property, by have bound := (arguments.val true).isLt; omega⟩)
    (by
      intro name
      exact extraBitWiden_realizable.onResults binaryDivision.inputDomains binaryDivision.precondition
        (fun _ _ arguments => arguments.val name) (by intros; trivial)
        (by intro _; exact Realizable.argument _ name _))
  have narrowed := widened.followedBy narrowDivisionPair_realizable rfl (by intros; trivial)
  exact narrowed.withSpecification binaryDivision.precondition binaryDivision.compute
    (by intro sizes arguments valid; exact valid) (by
      intro sizes arguments valid
      apply Prod.ext <;> apply Fin.ext
      · simp only [followedBy, narrowDivisionPair, unaryMap, onResults, reindexDomains, substitute,
          binaryDivisionWithCapacity, extraBitWiden, binaryDivision]
        change (BitVec.setWidth _ _).toNat = _
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (arguments false).isLt)
      · simp only [followedBy, narrowDivisionPair, unaryMap, onResults, reindexDomains, substitute,
          binaryDivisionWithCapacity, extraBitWiden, binaryDivision]
        change (BitVec.setWidth _ _).toNat = _
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt ((Nat.mod_lt _ valid).trans (arguments true).isLt))

end Polytime2.Computation
