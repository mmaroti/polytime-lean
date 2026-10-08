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

import Polytime.EncodedDomain

/-! # Boolean tuples and bounded natural counters

Bits are stored least significant first. Counters below a polynomial capacity
use that many binary bits; this deliberately avoids logarithmic size expressions.
-/

namespace Polytime

namespace FixedPresentation

def boolean : FixedPresentation where
  Carrier := Bool
  cardinality := 2
  enumeration := finTwoEquiv.symm

@[simp] theorem boolean_width : boolean.bitWidth = 1 := by decide

end FixedPresentation

namespace BoolTuple

def toBits {length : ℕ} (tuple : Fin length → Bool) : BitVec length :=
  (BitVec.ofBoolListLE (List.ofFn tuple)).cast (List.length_ofFn ..)

def fromBits {length : ℕ} (bits : BitVec length) : Fin length → Bool :=
  fun index => bits[index.val]

@[simp] theorem fromBits_toBits {length : ℕ} (tuple : Fin length → Bool) :
    fromBits (toBits tuple) = tuple := by
  funext index
  simp [fromBits, toBits, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, index.isLt]

@[simp] theorem toBits_fromBits {length : ℕ} (bits : BitVec length) :
    toBits (fromBits bits) = bits := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index valid
  have equality := congrFun (fromBits_toBits (fromBits bits)) ⟨index, valid⟩
  simpa [fromBits, BitVec.getLsbD_eq_getElem valid] using equality

def lookup {length : ℕ} (tuple : Fin length → Bool) (index : Fin length) : Bool :=
  tuple index

def update {length : ℕ} (tuple : Fin length → Bool) (index : Fin length)
    (value : Bool) : Fin length → Bool :=
  fun position => if position = index then value else tuple position

@[simp] theorem lookup_update {length : ℕ} (tuple : Fin length → Bool)
    (index : Fin length) (value : Bool) : lookup (update tuple index value) index = value := by
  simp [lookup, update]

theorem update_preserves {length : ℕ} (tuple : Fin length → Bool)
    (index position : Fin length) (value : Bool) (distinct : position ≠ index) :
    lookup (update tuple index value) position = lookup tuple position := by
  simp [lookup, update, distinct]

noncomputable section TupleDomains

def domain {ctx : SizeContext} (length : SizeExpression ctx) : DomainExpression ctx :=
  .power (.fixed FixedPresentation.boolean) length

def valueEquiv {ctx : SizeContext} (length : SizeExpression ctx)
    (assignment : SizeAssignment ctx) :
    (domain length).Value assignment ≃ (Fin (length.eval assignment) → Bool) :=
  Equiv.cast (by simp only [domain, DomainExpression.value_power, DomainExpression.value_fixed,
    FixedPresentation.boolean])

/-- Complete Boolean tuples are equivalent to their exact-width bit vectors. -/
def bitsEquiv {ctx : SizeContext} (length : SizeExpression ctx) (assignment : SizeAssignment ctx) :
    BitVec (length.eval assignment) ≃ (domain length).Value assignment :=
  ({ toFun := fromBits, invFun := toBits,
     left_inv := toBits_fromBits, right_inv := fromBits_toBits } :
    BitVec (length.eval assignment) ≃ (Fin (length.eval assignment) → Bool)).trans
      (valueEquiv length assignment).symm

@[simp] theorem domain_width {ctx : SizeContext} (length : SizeExpression ctx)
    (assignment : SizeAssignment ctx) : (domain length).bitWidth assignment = length.eval assignment := by
  simp [domain]

theorem encode_bit {ctx : SizeContext} (length : SizeExpression ctx) (assignment : SizeAssignment ctx)
    (tuple : Fin (length.eval assignment) → Bool) (index : Fin (length.eval assignment)) :
    ((BoolTuple.domain length).encode assignment ((BoolTuple.valueEquiv length assignment).symm tuple)).getLsbD index.val = tuple index := by
  have represented : (BoolTuple.valueEquiv length assignment).symm tuple =
      DomainExpression.powerFixedValue FixedPresentation.boolean length assignment tuple := by
    exact (DomainExpression.powerFixedValue_eq_cast FixedPresentation.boolean length assignment tuple).symm
  rw [represented]
  have encoding := DomainExpression.encode_power_fixed_bit
    FixedPresentation.boolean length assignment tuple index.val
  have bit := BitCodec.power_encode_bit FixedPresentation.boolean.codec (length.eval assignment) tuple index
  exact encoding.trans (bit.trans (by cases tuple index <;> rfl))

end TupleDomains
end BoolTuple

namespace BoundedNat

noncomputable section CounterPresentation

/-- Naturals strictly below the capacity, with a fixed padded binary encoding. -/
def domain {ctx : SizeContext} (capacity : SizeExpression ctx) : EncodedDomain ctx where
  Carrier assignment := Fin (capacity.eval assignment)
  expression := BoolTuple.domain capacity
  represent assignment value := (BoolTuple.valueEquiv capacity assignment).symm
    (BoolTuple.fromBits (BitVec.ofNatLT value.val (value.isLt.trans Nat.lt_two_pow_self)))
  interpret assignment tuple :=
    let value := (BoolTuple.toBits (BoolTuple.valueEquiv capacity assignment tuple)).toNat
    if valid : value < capacity.eval assignment then some ⟨value, valid⟩ else none
  interpret_represent assignment value := by
    simp [value.isLt]
  represent_interpret assignment tuple value hypothesis := by
    dsimp at hypothesis ⊢
    split at hypothesis
    · have equality := Option.some.inj hypothesis
      subst value
      simp
    · contradiction

@[simp] theorem domain_width {ctx : SizeContext} (capacity : SizeExpression ctx)
    (assignment : SizeAssignment ctx) :
    (domain capacity).expression.bitWidth assignment = capacity.eval assignment := by
  simp [domain]

/-- The domain uses the ordinary padded binary numeral, without truncation. -/
theorem encode_bits {ctx : SizeContext} (capacity : SizeExpression ctx) (assignment : SizeAssignment ctx)
    (value : Fin (capacity.eval assignment)) :
    (((BoundedNat.domain capacity).codec assignment).encode value).cast (BoundedNat.domain_width capacity assignment) =
      BitVec.ofNat (capacity.eval assignment) value.val := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index valid
  simp only [BitVec.getLsbD_cast]
  change ((BoolTuple.domain capacity).encode assignment
    ((BoolTuple.valueEquiv capacity assignment).symm
      (BoolTuple.fromBits (BitVec.ofNatLT value.val (value.isLt.trans Nat.lt_two_pow_self))))).getLsbD index = _
  have equality := BoolTuple.encode_bit capacity assignment
    (BoolTuple.fromBits (BitVec.ofNatLT value.val (value.isLt.trans Nat.lt_two_pow_self))) ⟨index, valid⟩
  exact equality.trans (by simp [BoolTuple.fromBits, BitVec.ofNatLT_eq_ofNat, BitVec.getLsbD_eq_getElem valid])

end CounterPresentation
end BoundedNat
end Polytime
