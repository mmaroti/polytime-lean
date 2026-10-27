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

import Polytime2.Encoding.Records
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Renaming size parameters without changing mathematical payloads -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

universe carrierLevel

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Interpret a domain using selected size names in a larger parameter family.
The carrier uses the direct projection, while the exact width is renamed. -/
noncomputable def renameParameters (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) : EncodedDomain NewParameter :=
  ofCodec (fun sizes => domain.Carrier (sizes ∘ names)) (MvPolynomial.rename names domain.widthPolynomial)
    (fun sizes => domain.width (sizes ∘ names))
    (fun sizes => (MvPolynomial.eval_rename names sizes domain.widthPolynomial).symm)
    (fun sizes => domain.encode (sizes ∘ names)) (fun sizes => domain.decode (sizes ∘ names))
    (fun sizes => domain.decode_encode (sizes ∘ names)) (fun sizes => domain.encode_decode (sizes ∘ names))

@[simp] theorem renameParameters_widthPolynomial (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) :
    (domain.renameParameters names).widthPolynomial = MvPolynomial.rename names domain.widthPolynomial := rfl

@[simp] theorem renameParameters_width (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) (sizes : NewParameter → ℕ) :
    (domain.renameParameters names).width sizes = domain.width (sizes ∘ names) := by
  change MvPolynomial.eval sizes (MvPolynomial.rename names domain.widthPolynomial) = _
  exact MvPolynomial.eval_rename names sizes domain.widthPolynomial

@[simp] theorem renameParameters_bits (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) (sizes : NewParameter → ℕ) (value : domain.Carrier (sizes ∘ names)) :
    ArrayEncoding.bits ((domain.renameParameters names).encode sizes value) =
      ArrayEncoding.bits (domain.encode (sizes ∘ names) value) := by
  simp only [renameParameters, ofCodec, ArrayEncoding.bits_cast]

/-- Identity renaming retains the entire canonical codec. -/
@[simp] theorem renameParameters_id (domain : EncodedDomain.{0, carrierLevel} Parameter) :
    domain.renameParameters id = domain := by
  refine ext_of_encode_bits (domain.renameParameters id) domain rfl ?_ ?_
  · exact MvPolynomial.rename_id_apply _
  · intros; exact renameParameters_bits _ _ _ _

/-- Successive size renamings compose without a carrier or encoding adapter. -/
@[simp] theorem renameParameters_comp {ThirdParameter : Type} [Fintype ThirdParameter]
    (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (first : Parameter → NewParameter) (second : NewParameter → ThirdParameter) :
    (domain.renameParameters first).renameParameters second =
      domain.renameParameters (second ∘ first) := by
  refine ext_of_encode_bits ((domain.renameParameters first).renameParameters second)
    (domain.renameParameters (second ∘ first)) rfl ?_ ?_
  · exact MvPolynomial.rename_rename _ _ _
  · intros; simp only [renameParameters_bits]; rfl

/-- Observe composed renamings without rewriting the dependent value's codec. -/
theorem renameParameters_comp_bits {ThirdParameter : Type} [Fintype ThirdParameter]
    (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (first : Parameter → NewParameter) (second : NewParameter → ThirdParameter)
    (sizes : ThirdParameter → ℕ) (value : domain.Carrier ((sizes ∘ second) ∘ first)) :
    ArrayEncoding.bits (((domain.renameParameters first).renameParameters second).encode sizes value) =
      ArrayEncoding.bits ((domain.renameParameters (second ∘ first)).encode sizes value) := by
  simp only [renameParameters_bits]
  rfl

/-- Fixed finite codecs are independent of runtime size names. -/
@[simp] theorem fixed_renameParameters {Carrier : Type carrierLevel} {cardinality : ℕ}
    (enumeration : Carrier ≃ Fin cardinality) (names : Parameter → NewParameter) :
    (fixed (Parameter := Parameter) enumeration).renameParameters names = fixed enumeration := by
  refine ext_of_encode_bits ((fixed (Parameter := Parameter) enumeration).renameParameters names)
    (fixed enumeration) rfl ?_ ?_
  · simp only [renameParameters_widthPolynomial, fixed_widthPolynomial, MvPolynomial.rename_C]
  · intros; simp only [renameParameters_bits, fixed_encode_bits]; rfl

/-- Parameter renaming commutes with products, preserving field order. -/
@[simp] theorem prod_renameParameters (left right : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) :
    (left.prod right).renameParameters names =
      (left.renameParameters names).prod (right.renameParameters names) := by
  refine ext_of_encode_bits ((left.prod right).renameParameters names)
    ((left.renameParameters names).prod (right.renameParameters names)) rfl ?_ ?_
  · simp only [renameParameters_widthPolynomial, map_add]
  · intros; simp only [renameParameters_bits, bits_prod_encode]; rfl

/-- Specialization-fixed codecs are independent of the names of runtime sizes. -/
@[simp] theorem constant_renameParameters (domain : EncodedDomain.{0, carrierLevel} Empty)
    (names : Parameter → NewParameter) :
    (domain.constant : EncodedDomain Parameter).renameParameters names = domain.constant := by
  refine ext_of_encode_bits ((domain.constant : EncodedDomain Parameter).renameParameters names)
    domain.constant rfl ?_ ?_
  · simp only [renameParameters_widthPolynomial, constant_widthPolynomial, MvPolynomial.rename_C]
  · intros; simp only [renameParameters_bits, constant_encode_bits]; rfl

/-- Parameter renaming commutes with records, including the empty record. -/
@[simp] theorem record_renameParameters (count : ℕ)
    (fields : Fin count → EncodedDomain.{0, carrierLevel} Parameter) (names : Parameter → NewParameter) :
    (record count fields).renameParameters names = record count (fun index => (fields index).renameParameters names) := by
  refine ext_of_encode_bits ((record count fields).renameParameters names)
    (record count (fun index => (fields index).renameParameters names)) rfl ?_ ?_
  · simp only [renameParameters_widthPolynomial, record_widthPolynomial, map_sum]
  · intro sizes value
    rw [renameParameters_bits]
    apply record_encode_bits_congr
    intro index
    rw [renameParameters_bits]
    rfl

/-- Named-coordinate arrays commute with parameter renaming. -/
@[simp] theorem array_renameParameters (element : EncodedDomain.{0, carrierLevel} Parameter)
    (parameter : Parameter) (names : Parameter → NewParameter) :
    (element.array parameter).renameParameters names = (element.renameParameters names).array (names parameter) := by
  refine ext_of_encode_bits ((element.array parameter).renameParameters names)
    ((element.renameParameters names).array (names parameter)) rfl ?_ ?_
  · simp only [renameParameters_widthPolynomial, array_widthPolynomial, map_mul, MvPolynomial.rename_X]
  · intros; simp only [renameParameters_bits, array_encode_bits, ArrayEncoding.bits_encode]; rfl

/-- Renaming runtime sizes preserves totality of a full canonical codec. -/
theorem renameParameters_encode_surjective (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (full : ∀ sizes, Function.Surjective (domain.encode sizes))
    (names : Parameter → NewParameter) (sizes : NewParameter → ℕ) :
    Function.Surjective ((domain.renameParameters names).encode sizes) := by
  intro bits
  let source := bits.cast (renameParameters_width domain names sizes)
  obtain ⟨value, encoded⟩ := full (sizes ∘ names) source
  refine ⟨value, ?_⟩
  change (domain.encode (sizes ∘ names) value).cast (renameParameters_width domain names sizes).symm = bits
  rw [encoded]
  apply BitVec.eq_of_toNat_eq
  rfl

end Polytime2.EncodedDomain
