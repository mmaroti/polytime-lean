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

import Polytime2.Encoding.EncodedArray
import Mathlib.Algebra.BigOperators.Fin

/-! # Products and tagged variants with consecutive bit fields

Fields are ordered by their finite index. Variants store one discriminator,
then every alternative's field, with zero bits in all inactive fields.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

universe parameterLevel carrierLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- Every bit pattern is a value; the exact width is a fixed polynomial. -/
noncomputable abbrev bitVectors (polynomial : MvPolynomial Parameter ℕ) : EncodedDomain Parameter where
  Carrier sizes := BitVec (MvPolynomial.eval sizes polynomial)
  widthPolynomial := polynomial
  encode _ value := value
  decode _ bits := some bits
  decode_encode _ _ := rfl
  encode_decode _ _ _ accepted := (Option.some.inj accepted).symm

/-- A pair stores the left field first in little-endian tape order. -/
noncomputable abbrev prod (left right : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    EncodedDomain Parameter :=
  ofCodec (fun sizes => left.Carrier sizes × right.Carrier sizes)
    (left.widthPolynomial + right.widthPolynomial)
    (fun sizes => right.width sizes + left.width sizes) (by intros; simp [Nat.add_comm])
    (fun sizes value => right.encode sizes value.2 ++ left.encode sizes value.1)
    (fun sizes bits => do
      let first ← left.decode sizes (bits.extractLsb' 0 (left.width sizes))
      let second ← right.decode sizes (bits.extractLsb' (left.width sizes) (right.width sizes))
      pure (first, second))
    (by intros; simp [BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right, decode_encode])
    (by
      intro sizes bits value accepted
      simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at accepted
      obtain ⟨first, firstAccepted, second, secondAccepted, equal⟩ := accepted
      cases equal
      rw [left.encode_decode _ _ _ firstAccepted, right.encode_decode _ _ _ secondAccepted]
      exact BitVec.extractLsb'_append_extractLsb')

@[simp] theorem prod_widthPolynomial
    (left right : EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    (left.prod right).widthPolynomial = left.widthPolynomial + right.widthPolynomial := rfl

@[simp] theorem bits_prod_encode
    (left right : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : left.Carrier sizes × right.Carrier sizes) :
    ArrayEncoding.bits ((left.prod right).encode sizes value) =
      ArrayEncoding.bits (left.encode sizes value.1) ++ ArrayEncoding.bits (right.encode sizes value.2) := by
  simp only [prod, ofCodec, ArrayEncoding.bits_cast, ArrayEncoding.bits_append]

namespace RecordEncoding

/-- The recursive codec is private to the record construction. -/
noncomputable def domain : (count : ℕ) →
    (Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) → EncodedDomain Parameter
  | 0, _ => {
      Carrier := fun _ => PUnit.{carrierLevel + 1}
      widthPolynomial := 0
      encode := fun _ _ => 0
      decode := fun _ _ => some PUnit.unit
      decode_encode := fun _ _ => rfl
      encode_decode := by intros; apply BitVec.eq_of_getLsbD_eq; intro index bounded; simp at bounded }
  | count + 1, fields => (fields 0).prod (domain count (Fin.tail fields))

noncomputable def equivalence : (count : ℕ) →
    (fields : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) →
    (sizes : Parameter → ℕ) →
    ((index : Fin count) → (fields index).Carrier sizes) ≃ (domain count fields).Carrier sizes
  | 0, _, _ => {
      toFun := fun _ => PUnit.unit
      invFun := fun _ index => Fin.elim0 index
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => rfl }
  | count + 1, fields, sizes => {
      toFun := fun value => (value 0, equivalence count (Fin.tail fields) sizes (Fin.tail value))
      invFun := fun value => Fin.cons value.1 ((equivalence count (Fin.tail fields) sizes).symm value.2)
      left_inv := by
        intro value
        have inverse := (equivalence count (Fin.tail fields) sizes).symm_apply_apply (Fin.tail value)
        funext index
        refine Fin.cases rfl (fun smaller => ?_) index
        exact congrFun inverse smaller
      right_inv := by
        intro value
        change (fields 0).Carrier sizes × (domain count (Fin.tail fields)).Carrier sizes at value
        rcases value with ⟨first, rest⟩
        exact congrArg (Prod.mk first) ((equivalence count (Fin.tail fields) sizes).apply_symm_apply rest) }


end RecordEncoding

/-- A finite heterogeneous record uses the ordinary dependent function carrier. -/
noncomputable abbrev record (count : ℕ)
    (fields : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) : EncodedDomain Parameter :=
  (RecordEncoding.domain count fields).reindex
    (fun sizes => (index : Fin count) → (fields index).Carrier sizes)
    (RecordEncoding.equivalence count fields)

@[simp] theorem record_widthPolynomial (count : ℕ)
    (fields : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    (record count fields).widthPolynomial = ∑ index, (fields index).widthPolynomial := by
  induction count with
  | zero => simp [record, RecordEncoding.domain, reindex]
  | succ count hypothesis =>
    change (fields 0).widthPolynomial + (record count (Fin.tail fields)).widthPolynomial = _
    rw [hypothesis, Fin.sum_univ_succ]
    rfl

/-- Records concatenate their component words, without delimiters or padding. -/
theorem bits_record_encode (count : ℕ)
    (fields : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (values : (index : Fin count) → (fields index).Carrier sizes) :
    ArrayEncoding.bits ((record count fields).encode sizes values) =
      (List.ofFn (fun index => ArrayEncoding.bits ((fields index).encode sizes (values index)))).flatten := by
  induction count with
  | zero => simp [record, RecordEncoding.domain, reindex, ArrayEncoding.bits]
  | succ count hypothesis =>
    change ArrayEncoding.bits
      (((RecordEncoding.domain count (Fin.tail fields)).encode sizes
        (RecordEncoding.equivalence count (Fin.tail fields) sizes (Fin.tail values)) ++
        (fields 0).encode sizes (values 0)).cast (by
          simp [record, RecordEncoding.domain, reindex, prod, Nat.add_comm])) = _
    rw [ArrayEncoding.bits_cast, ArrayEncoding.bits_append]
    change ArrayEncoding.bits ((fields 0).encode sizes (values 0)) ++
      ArrayEncoding.bits ((record count (Fin.tail fields)).encode sizes (Fin.tail values)) = _
    rw [hypothesis, List.ofFn_succ]
    rfl

/-- The exact polynomial number of bits preceding a record coordinate. -/
noncomputable def recordOffset : (count : ℕ) →
    (Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) → Fin count →
    MvPolynomial Parameter ℕ
  | 0, _, index => Fin.elim0 index
  | count + 1, fields, index => Fin.cases 0
      (fun smaller => (fields 0).widthPolynomial + recordOffset count (Fin.tail fields) smaller) index

/-- The selected field is preceded by its polynomial offset. -/
theorem split_record_encode (count : ℕ)
    (fields : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (values : (index : Fin count) → (fields index).Carrier sizes)
    (index : Fin count) :
    ∃ before after : List Bool,
      ArrayEncoding.bits ((record count fields).encode sizes values) =
        before ++ ArrayEncoding.bits ((fields index).encode sizes (values index)) ++ after ∧
      before.length = MvPolynomial.eval sizes (recordOffset count fields index) := by
  rw [bits_record_encode]
  induction count with
  | zero => exact Fin.elim0 index
  | succ count hypothesis =>
    refine Fin.cases ?_ (fun smaller => ?_) index
    · refine ⟨[], (List.ofFn (fun index =>
        ArrayEncoding.bits ((fields index.succ).encode sizes (values index.succ)))).flatten, ?_, ?_⟩
      · simp [List.ofFn_succ]
      · simp [recordOffset]
    · obtain ⟨before, after, split, length⟩ := hypothesis (Fin.tail fields) (Fin.tail values) smaller
      refine ⟨ArrayEncoding.bits ((fields 0).encode sizes (values 0)) ++ before, after, ?_, ?_⟩
      · rw [List.ofFn_succ, List.flatten_cons]
        simp only [List.append_assoc]
        congr 1
        simpa only [Fin.tail, List.append_assoc] using split
      · simp only [List.length_append, List.length_ofFn, length, recordOffset, Fin.cases_succ,
          map_add]

namespace VariantEncoding

noncomputable abbrev storage (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) : EncodedDomain Parameter :=
  (fixed (Equiv.refl (Fin count))).prod
    (record count (fun index => bitVectors (alternatives index).widthPolynomial))

noncomputable def fields (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : (index : Fin count) × (alternatives index).Carrier sizes) :
    (index : Fin count) → BitVec ((alternatives index).width sizes) := by
  classical
  exact fun index => if equal : index = value.1 then
    (alternatives index).encode sizes (equal.symm ▸ value.2) else 0

end VariantEncoding

/-- A discriminator followed by one zero-padded field per alternative.
Invalid tags, invalid selected values, and nonzero inactive fields are rejected. -/
noncomputable def variant (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    EncodedDomain Parameter := by
  classical
  let raw := VariantEncoding.storage count alternatives
  let pack := fun sizes (value : (index : Fin count) × (alternatives index).Carrier sizes) =>
    raw.encode sizes (value.1, VariantEncoding.fields count alternatives sizes value)
  exact ofCodec (fun sizes => (index : Fin count) × (alternatives index).Carrier sizes)
    raw.widthPolynomial raw.width (fun _ => rfl) pack
    (fun (sizes : Parameter → ℕ) (bits : BitVec (raw.width sizes)) =>
      match raw.decode sizes bits with
      | none => none
      | some payload => do
        let value ← (alternatives payload.1).decode sizes (payload.2 payload.1)
        let result := Sigma.mk payload.1 value
        if pack sizes result = bits then some result else none)
    (by
      intro sizes value
      simp only [pack, raw.decode_encode]
      simp only [VariantEncoding.fields, ↓reduceDIte,
        (alternatives value.1).decode_encode]
      simp)
    (by
      intro sizes bits value accepted
      cases decoded : raw.decode sizes bits with
      | none => simp [decoded] at accepted
      | some payload =>
        simp only [decoded, Bind.bind, Option.bind_eq_some_iff] at accepted
        obtain ⟨selected, _, accepted⟩ := accepted
        split at accepted
        next equal => cases Option.some.inj accepted; exact equal
        next different => contradiction)

@[simp] theorem variant_widthPolynomial (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter) :
    (variant count alternatives).widthPolynomial = MvPolynomial.C (Nat.clog 2 count) +
      ∑ index, (alternatives index).widthPolynomial := by
  change MvPolynomial.C (Nat.clog 2 count) +
    (record count (fun index => bitVectors (alternatives index).widthPolynomial)).widthPolynomial = _
  simp only [record_widthPolynomial]

/-- The tag is followed by every alternative's field in index order. -/
theorem bits_variant_encode (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (value : (index : Fin count) × (alternatives index).Carrier sizes) :
    ArrayEncoding.bits ((variant count alternatives).encode sizes value) =
      ArrayEncoding.bits ((fixed (Parameter := Parameter) (Equiv.refl (Fin count))).encode sizes value.1) ++
      (List.ofFn (fun index => ArrayEncoding.bits (VariantEncoding.fields count alternatives sizes value index))).flatten := by
  change ArrayEncoding.bits (((VariantEncoding.storage count alternatives).encode sizes
    (value.1, VariantEncoding.fields count alternatives sizes value)).cast (by rfl)) = _
  rw [ArrayEncoding.bits_cast]
  change ArrayEncoding.bits (((record count (fun index => bitVectors (alternatives index).widthPolynomial)).encode sizes
    (VariantEncoding.fields count alternatives sizes value) ++
    (fixed (Parameter := Parameter) (Equiv.refl (Fin count))).encode sizes value.1).cast (by
      simp [Nat.add_comm])) = _
  rw [ArrayEncoding.bits_cast, ArrayEncoding.bits_append, bits_record_encode]

/-- A nonzero inactive field is not a canonical variant encoding. -/
theorem variant_rejects_inactive (count : ℕ)
    (alternatives : Fin count → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (sizes : Parameter → ℕ) (tag inactive : Fin count)
    (slots : (index : Fin count) → BitVec ((alternatives index).width sizes))
    (different : inactive ≠ tag) (nonzero : slots inactive ≠ 0) :
    (variant count alternatives).decode sizes
      ((VariantEncoding.storage count alternatives).encode sizes (tag, slots)) = none := by
  classical
  cases accepted : (variant count alternatives).decode sizes
      ((VariantEncoding.storage count alternatives).encode sizes (tag, slots)) with
  | none => rfl
  | some value =>
    have equal := (variant count alternatives).encode_decode sizes _ value accepted
    change (VariantEncoding.storage count alternatives).encode sizes
      (value.1, VariantEncoding.fields count alternatives sizes value) =
        (VariantEncoding.storage count alternatives).encode sizes (tag, slots) at equal
    let raw := VariantEncoding.storage count alternatives
    have decoded := (raw.decode_encode sizes
      (value.1, VariantEncoding.fields count alternatives sizes value)).symm.trans
        ((congrArg (raw.decode sizes) equal).trans (raw.decode_encode sizes (tag, slots)))
    have packed := Option.some.inj decoded
    have tagEqual := congrArg Prod.fst packed
    change value.1 = tag at tagEqual
    have fieldEqual := congrFun (congrArg Prod.snd packed) inactive
    have empty : VariantEncoding.fields count alternatives sizes value inactive = 0 := by
      simp [VariantEncoding.fields, tagEqual, different]
    exact False.elim (nonzero (fieldEqual.symm.trans empty))

end Polytime2.EncodedDomain
