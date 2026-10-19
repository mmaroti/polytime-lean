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

import Polytime2.Computation.Width
import Polytime2.Computation.Layout
import Polytime2.Primitives.FieldCopy
import Polytime2.Encoding.Records

/-! # Certified access to consecutive encoded fields

A mathematical bit-splitting theorem supplies the field meaning. Unary offset
and length headers are evaluated privately and hidden from callers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention
open Binary (Symbol word)

universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

private def fieldPlacement : PublicTape Parameter ((Unit ⊕ Unit) ⊕ Unit) ↪ Parameter ⊕ Fin 4 :=
  (Function.Embedding.refl Parameter).sumMap
    ⟨(fun name => match name with
      | .inl (.inl (.inl _)) => 2
      | .inl (.inl (.inr _)) => 1
      | .inl (.inr _) => 0
      | .inr _ => 3), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> simp_all⟩

/-- Copy a field identified by an exact polynomial prefixPolynomial width. The source and
result carriers may differ and every component width may depend on sizes. -/
theorem fieldProjection
    (source target : EncodedDomain.{0, carrierLevel} Parameter)
    (prefixPolynomial : MvPolynomial Parameter ℕ)
    (precondition : ∀ sizes, source.Carrier sizes → Prop)
    (result : ∀ sizes, {value : source.Carrier sizes // precondition sizes value} → target.Carrier sizes)
    (split : ∀ sizes value,
      ∃ before after : List Bool,
        EncodedDomain.ArrayEncoding.bits (source.encode sizes value.val) =
          before ++ EncodedDomain.ArrayEncoding.bits (target.encode sizes (result sizes value)) ++ after ∧
        before.length = MvPolynomial.eval sizes prefixPolynomial) :
    (Computation.unaryMap source target precondition result).Realizable := by
  classical
  let computation := Computation.unaryMap source target precondition result
  apply Realizable.withComputedWidth computation target.widthPolynomial
  apply Realizable.withComputedWidth (computation.withUnaryWidth target.widthPolynomial) prefixPolynomial
  let extended := (computation.withUnaryWidth target.widthPolynomial).withUnaryWidth prefixPolynomial
  let domains : Parameter ⊕ Fin 4 → EncodedDomain.{0, carrierLevel} Parameter
    | .inl parameter => EncodedDomain.unary parameter
    | .inr name => if name = 0 then EncodedDomain.unaryOfLength prefixPolynomial
        else if name = 1 then EncodedDomain.unaryOfLength target.widthPolynomial
        else if name = 2 then source else target
  let readOnly : Parameter ⊕ Fin 4 → Bool := Sum.elim (fun _ => true) (FieldCopy.readOnly)
  let sizes : Parameter ↪ Parameter ⊕ Fin 4 := ⟨Sum.inl, Sum.inl_injective⟩
  let data : Fin 4 ↪ Parameter ⊕ Fin 4 := ⟨Sum.inr, Sum.inr_injective⟩
  let outputs : Unit ↪ Parameter ⊕ Fin 4 := oneTape (.inr 3)
  let algorithm := wire (Alphabet := Alphabet (Parameter ⊕ Fin 4)) data (FieldCopy.machine)
  have certificate : CallingConvention.Realizes domains readOnly sizes outputs algorithm
      FieldCopy.entry FieldCopy.exit
      (fun assignment input => precondition assignment (input ⟨.inr 2, rfl⟩))
      (fun assignment input output => ∃ valid : precondition assignment (input ⟨.inr 2, rfl⟩),
        output () = result assignment ⟨input ⟨.inr 2, rfl⟩, valid⟩) := by
    refine ⟨(by intro parameter; rfl), (by intro name; rfl),
      (by intro symbols; simp [algorithm, wire, FieldCopy.halt]),
      3 * prefixPolynomial + 3 * target.widthPolynomial + 13, ?_⟩
    intro assignment input initial valid represented headers
    let value := input ⟨.inr 2, rfl⟩
    let answer := result assignment ⟨value, valid⟩
    let bits := EncodedDomain.ArrayEncoding.bits (target.encode assignment answer)
    have bitsLength : bits.length = target.width assignment := List.length_ofFn
    obtain ⟨before, after, decomposition, prefixLength⟩ := split assignment ⟨value, valid⟩
    obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 3) rfl
    change old.length = target.width assignment at oldLength
    have offsetEq : initial (.inr 0) = unary before.length := by
      have represented := represented.1 (.inr 0) rfl
      change initial (.inr 0) = encoded (EncodedDomain.unaryOfLength prefixPolynomial) assignment _ at represented
      cases input ⟨.inr 0, rfl⟩
      simpa only [prefixLength] using represented.trans (EncodedDomain.encoded_unaryOfLength prefixPolynomial assignment)
    have lengthEq : initial (.inr 1) = unary bits.length := by
      have represented := represented.1 (.inr 1) rfl
      change initial (.inr 1) = encoded (EncodedDomain.unaryOfLength target.widthPolynomial) assignment _ at represented
      cases input ⟨.inr 1, rfl⟩
      simpa only [bitsLength] using represented.trans (EncodedDomain.encoded_unaryOfLength target.widthPolynomial assignment)
    have sourceEq : initial (.inr 2) = buffer (word (before ++ bits ++ after)) := by
      have represented := represented.1 (.inr 2) rfl
      change initial (.inr 2) = buffer (word (EncodedDomain.ArrayEncoding.bits (source.encode assignment value))) at represented
      rwa [decomposition] at represented
    have trace := FieldCopy.runs before bits (word after) old
      (oldLength.trans bitsLength.symm)
      (fun name => (domains (.inr name)).width assignment)
      (by change bits.length ≤ target.width assignment; exact le_of_eq bitsLength)
    have trace := trace.wire_at_of_eq data
      (fun name => (domains name).width assignment) readOnly
      (by intro name; rfl) (by intro name premise; exact premise)
      (fun _ => 0) (fun _ => 0) initial
      (install data (FieldCopy.frame before.length bits.length
        (buffer (word (before ++ bits ++ after))) (encoded target assignment answer)) initial)
      (by intro name; rfl) (by intro name; rfl) (by intros; rfl)
      (by intro name; fin_cases name <;> simp [FieldCopy.frame, offsetEq, lengthEq, sourceEq, oldEq, word, List.append_assoc, data])
      (by intro name; rw [install_at]; fin_cases name <;> simp [FieldCopy.frame, encoded, word, List.append_assoc, data, bits, CallingConvention.tape, EncodedDomain.ArrayEncoding.bits, buffer])
      (by intro name outside; exact install_outside _ _ _ _ outside)
    refine ⟨3 * before.length + 3 * bits.length + 13, (fun _ => answer), _, ?_, trace, ⟨valid, rfl⟩, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, ← prefixLength]
      simp [bitsLength, EncodedDomain.width]
    · intro name; cases name; exact install_at data _ initial 3
  refine ofNamedLayout extended domains readOnly sizes outputs algorithm
    FieldCopy.entry FieldCopy.exit _ _ certificate fieldPlacement
    (by rintro (parameter | ((original | lengthName) | offsetName) | resultName) <;> rfl)
    (by rintro (parameter | ((original | lengthName) | offsetName) | resultName) <;> rfl)
    (by intro name outside; cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name =>
        fin_cases name
        · exact False.elim (outside ⟨.inr (.inl (.inr ())), rfl⟩)
        · exact False.elim (outside ⟨.inr (.inl (.inl (.inr ()))), rfl⟩)
        · exact False.elim (outside ⟨.inr (.inl (.inl (.inl ()))), rfl⟩)
        · rfl)
    (by intro parameter; rfl) () rfl (by intro assignment input valid; exact valid) ?_
  intro assignment input valid output correct
  obtain ⟨good, equal⟩ := correct
  exact congrArg (encoded target assignment) equal

end Polytime2.Computation.Realizable.Internal
