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

import Polytime.Tuple
import Mathlib.Data.Int.GCD

/-! # Integers bounded by bit length

These presentations reserve bits, rather than storage proportional to numeric
magnitude. Signed integers use canonical two's complement with one sign bit.
Arithmetic returns bounded mathematical integers without truncation. These
executable refinements do not yet have tape-runtime certificates and are not
registered as certified program primitives.
-/

namespace Polytime

namespace BinaryNat

noncomputable section NaturalPresentation

/-- An unsigned b-bit integer may be as large as 2^b - 1. -/
def domain {ctx : SizeContext} (bits : SizeExpression ctx) : EncodedDomain ctx where
  Carrier assignment := Fin (2 ^ bits.eval assignment)
  expression := BoolTuple.domain bits
  represent assignment value := (BoolTuple.valueEquiv bits assignment).symm
    (BoolTuple.fromBits (BitVec.ofFin value))
  interpret assignment tuple := some
    ⟨(BoolTuple.toBits (BoolTuple.valueEquiv bits assignment tuple)).toNat, BitVec.isLt _⟩
  interpret_represent assignment value := by simp
  represent_interpret assignment tuple value hypothesis := by
    dsimp at hypothesis
    have equality := Option.some.inj hypothesis
    subst value
    simp

@[simp] theorem domain_width {ctx : SizeContext} (bits : SizeExpression ctx)
    (assignment : SizeAssignment ctx) : (domain bits).expression.bitWidth assignment = bits.eval assignment := by
  simp [domain]

end NaturalPresentation
end BinaryNat

namespace BinaryInt

/-- b magnitude bits and one sign bit represent [-2^b, 2^b). -/
abbrev Value (bits : ℕ) := {value : ℤ // -(2 : ℤ) ^ bits ≤ value ∧ value < (2 : ℤ) ^ bits}

def toBits {bits : ℕ} (value : Value bits) : BitVec (bits + 1) := BitVec.ofInt (bits + 1) value.val

def fromBits {bits : ℕ} (value : BitVec (bits + 1)) : Value bits :=
  ⟨value.toInt, by simpa using BitVec.le_toInt value, by simpa using BitVec.toInt_lt (x := value)⟩

@[simp] theorem fromBits_toBits {bits : ℕ} (value : Value bits) : fromBits (toBits value) = value := by
  apply Subtype.ext
  exact BitVec.toInt_ofInt_eq_self (by omega) (by simpa using value.property.1)
    (by simpa using value.property.2)

@[simp] theorem toBits_fromBits {bits : ℕ} (value : BitVec (bits + 1)) : toBits (fromBits value) = value := by
  simp [toBits, fromBits]

/-- Numeric magnitude is bounded exponentially in the declared bit count. -/
theorem abs_le (value : Value bits) : |value.val| ≤ (2 : ℤ) ^ bits :=
  _root_.abs_le.mpr ⟨value.property.1, value.property.2.le⟩

/-- Addition reserves one extra magnitude bit, so it cannot silently overflow. -/
def add (left right : Value bits) : Value (bits + 1) :=
  ⟨left.val + right.val, by
    have positive : 0 < (2 : ℤ) ^ bits := pow_pos (by decide) _
    obtain ⟨lowerLeft, upperLeft⟩ := left.property
    obtain ⟨lowerRight, upperRight⟩ := right.property
    constructor <;> simp only [pow_succ] <;> omega⟩

def sub (left right : Value bits) : Value (bits + 1) :=
  ⟨left.val - right.val, by
    obtain ⟨lowerLeft, upperLeft⟩ := left.property
    obtain ⟨lowerRight, upperRight⟩ := right.property
    constructor <;> simp only [pow_succ] <;> omega⟩

/-- Multiplication reserves a linear number of bits in the operand bit count. -/
def mul (left right : Value bits) : Value (2 * bits + 1) :=
  ⟨left.val * right.val, by
    have bound : |left.val * right.val| ≤ (2 : ℤ) ^ bits * (2 : ℤ) ^ bits := by
      rw [abs_mul]
      exact mul_le_mul (abs_le left) (abs_le right) (abs_nonneg _) (by positivity)
    have capacity : (2 : ℤ) ^ (2 * bits + 1) = 2 * ((2 : ℤ) ^ bits * (2 : ℤ) ^ bits) := by
      rw [show 2 * bits + 1 = bits + bits + 1 by omega, pow_succ, pow_add]
      ring
    have positive : 0 < (2 : ℤ) ^ bits * (2 : ℤ) ^ bits := by positivity
    obtain ⟨lower, upper⟩ := _root_.abs_le.mp bound
    rw [capacity]
    constructor <;> omega⟩

/-- The quotient stays bounded by the dividend magnitude, including signed extremes. -/
def div (left right : Value bits) (_nonzero : right.val ≠ 0) : Value (bits + 1) :=
  ⟨left.val / right.val, by
    have naturalBound := Int.natAbs_ediv_le_natAbs left.val right.val
    have bound : |left.val / right.val| ≤ (2 : ℤ) ^ bits := by
      have castBound : ((left.val / right.val).natAbs : ℤ) ≤ (left.val.natAbs : ℤ) := by exact_mod_cast naturalBound
      simp only [Int.natCast_natAbs] at castBound
      exact castBound.trans (abs_le left)
    have positive : 0 < (2 : ℤ) ^ bits := by positivity
    obtain ⟨lower, upper⟩ := _root_.abs_le.mp bound
    constructor <;> simp only [pow_succ] <;> omega⟩

/-- Euclidean remainder is nonnegative even for a negative divisor. -/
def rem (left right : Value bits) (nonzero : right.val ≠ 0) : Value (bits + 1) :=
  ⟨left.val % right.val, by
    have lower := Int.emod_nonneg left.val nonzero
    have upper := (Int.emod_lt_abs left.val nonzero).trans_le (abs_le right)
    have positive : 0 < (2 : ℤ) ^ bits := by positivity
    constructor <;> simp only [pow_succ] <;> omega⟩

theorem div_rem (left right : Value bits) (nonzero : right.val ≠ 0) :
    left.val = right.val * (div left right nonzero).val + (rem left right nonzero).val ∧
      0 ≤ (rem left right nonzero).val ∧ (rem left right nonzero).val < |right.val| :=
  ⟨(Int.mul_ediv_add_emod _ _).symm, Int.emod_nonneg _ nonzero, Int.emod_lt_abs _ nonzero⟩

/-- Nonnegative gcd, including gcd(0,0) = 0, with sufficient output capacity. -/
def gcd (left right : Value bits) : Value (bits + 1) :=
  ⟨(left.val.gcd right.val : ℤ), by
    have bound : (left.val.gcd right.val : ℤ) ≤ (2 : ℤ) ^ bits := by
      by_cases zero : left.val = 0
      · simp only [zero, Int.gcd_zero_left, Int.natCast_natAbs]
        exact abs_le right
      · have naturalBound := Int.gcd_le_natAbs_left right.val zero
        have castBound : (left.val.gcd right.val : ℤ) ≤ (left.val.natAbs : ℤ) := by exact_mod_cast naturalBound
        simp only [Int.natCast_natAbs] at castBound
        exact castBound.trans (abs_le left)
    have positive : 0 < (2 : ℤ) ^ bits := by positivity
    constructor <;> simp only [pow_succ] <;> omega⟩

noncomputable section IntegerPresentation

/-- Ordinary integer values correspond bijectively to two's-complement bits. -/
def bitsEquiv (bits : ℕ) : Value bits ≃ BitVec (bits + 1) where
  toFun := toBits
  invFun := fromBits
  left_inv := fromBits_toBits
  right_inv := toBits_fromBits

/-- Exact signed-binary storage, even when represented magnitudes are exponential. -/
def domain {ctx : SizeContext} (bits : SizeExpression ctx) : EncodedDomain ctx :=
  EncodedDomain.ofEquiv (BoolTuple.domain (bits + SizeExpression.constant 1))
    (fun assignment => Value (bits.eval assignment))
    (fun assignment =>
      ((bitsEquiv (bits.eval assignment)).trans
        (Equiv.cast (congrArg BitVec (by simp : bits.eval assignment + 1 =
          (bits + SizeExpression.constant 1).eval assignment)))).trans
        (BoolTuple.bitsEquiv (bits + SizeExpression.constant 1) assignment))

@[simp] theorem domain_width {ctx : SizeContext} (bits : SizeExpression ctx)
    (assignment : SizeAssignment ctx) :
    (domain bits).expression.bitWidth assignment = bits.eval assignment + 1 := by simp [domain, EncodedDomain.ofEquiv]

end IntegerPresentation
end BinaryInt
end Polytime
