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
import Polytime2.Encoding.BinaryEncoding
import Mathlib.Data.Int.Basic

/-! # Canonical sign-and-magnitude integer domains

At magnitude width `w`, the mathematical carrier is `{z : ℤ // z.natAbs < 2^w}`.
One sign bit precedes the `w` little-endian magnitude bits. Zero is positive;
negative-zero words are rejected. At width zero, zero is the only value.

Arithmetic uses derived result widths, without truncation: negation preserves
`w`, addition/subtraction use `w+1`, and multiplication uses `2*w`. Division
requires only a nonzero divisor and satisfies `a = b*q+r`, `0 ≤ r < |b|`.
Gcd is nonnegative, including `gcd(0,0)=0`; extended gcd returns bounded
Bézout coefficients with a polynomial bit-cost certificate. Left shift
multiplies by a power of two; arithmetic right shift uses floor division.
Magnitude bit length is `Nat.size z.natAbs`.
-/

namespace Polytime2.EncodedDomain

universe parameterLevel carrierLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

namespace SignedEncoding

/-- The storage sign is true exactly for a strictly negative value. -/
def negative (value : ℤ) : Bool := decide (value < 0)

/-- Sign and magnitude reconstruct the original ordinary integer. -/
theorem restore (value : ℤ) :
    (if negative value then -(value.natAbs : ℤ) else (value.natAbs : ℤ)) = value := by
  by_cases sign : value < 0
  · have magnitude := Int.natAbs_of_nonneg (show 0 ≤ -value by omega)
    simp only [Int.natAbs_neg] at magnitude
    simp only [negative, sign, decide_true, ↓reduceIte]
    omega
  · simpa [negative, sign] using Int.natAbs_of_nonneg (by omega : 0 ≤ value)

/-- The ordinary magnitude cast is positive on either side of zero. -/
theorem magnitude_value (value : ℤ) :
    (value.natAbs : ℤ) = if value < 0 then -value else value := by
  have restored := restore value
  by_cases sign : value < 0 <;> simp only [negative, sign, decide_true, decide_false, ↓reduceIte] at restored ⊢ <;> omega

/-- The sign/magnitude pair is private to the codec; negative zero is excluded. -/
def representationEquiv (width : ℕ) :
    {value : ℤ // value.natAbs < 2 ^ width} ≃
      {parts : Bool × Fin (2 ^ width) // parts.1 = true → parts.2.val ≠ 0} where
  toFun value := ⟨(negative value.val, ⟨value.val.natAbs, value.property⟩), by
    intro isNegative zero
    have nonzero : value.val ≠ 0 := by
      have sign : value.val < 0 := of_decide_eq_true isNegative
      omega
    exact nonzero (Int.natAbs_eq_zero.mp zero)⟩
  invFun parts := ⟨if parts.val.1 then -(parts.val.2.val : ℤ) else (parts.val.2.val : ℤ), by
    split <;> simp⟩
  left_inv value := by
    apply Subtype.ext
    exact restore value.val
  right_inv parts := by
    apply Subtype.ext
    rcases parts with ⟨⟨sign, magnitude⟩, valid⟩
    cases sign
    · simp [negative]
    · have positive : 0 < magnitude.val := Nat.pos_of_ne_zero (valid rfl)
      simp [negative, positive]

end SignedEncoding

/-- Ordinary bounded integers with a sign bit and an exact polynomial magnitude width. -/
noncomputable def binaryIntegers (width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter := by
  classical
  let magnitude := binaryNaturalsOfWidth width
  let storage := (booleans.prod magnitude).restrict
    (fun _ parts => parts.1 = true → parts.2.val ≠ 0)
  exact storage.reindex (fun sizes => {value : ℤ // value.natAbs < 2 ^ MvPolynomial.eval sizes width})
    (fun sizes => SignedEncoding.representationEquiv (MvPolynomial.eval sizes width))

@[simp] theorem binaryIntegers_width (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (binaryIntegers width).width sizes = 1 + MvPolynomial.eval sizes width := by
  simp [binaryIntegers, restrict, reindex, EncodedDomain.width, booleans, fixed, binaryNaturalsOfWidth, boundedIndexOfWidth, ofCodec]
  decide

/-- The integer codec reuses the Boolean and natural product bits unchanged. -/
theorem binaryIntegers_encode_bits (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (binaryIntegers width).Carrier sizes) :
    ArrayEncoding.bits ((binaryIntegers width).encode sizes value) =
      ArrayEncoding.bits (booleans.encode sizes (SignedEncoding.negative value.val)) ++
      ArrayEncoding.bits ((binaryNaturalsOfWidth width).encode sizes
        ⟨value.val.natAbs, value.property⟩) := by
  change ArrayEncoding.bits ((booleans.prod (binaryNaturalsOfWidth width)).encode sizes
    (SignedEncoding.negative value.val, ⟨value.val.natAbs, value.property⟩)) = _
  exact bits_prod_encode _ _ _ _

/-- Canonical sign/magnitude construction does not change the product word. -/
theorem binaryIntegers_encode_parts (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (parts : {parts : Bool × Fin (2 ^ MvPolynomial.eval sizes width) //
      parts.1 = true → parts.2.val ≠ 0}) :
    (binaryIntegers width).encode sizes
        ((SignedEncoding.representationEquiv (MvPolynomial.eval sizes width)).symm parts) =
      (booleans.prod (binaryNaturalsOfWidth width)).encode sizes parts.val := by
  change (booleans.prod (binaryNaturalsOfWidth width)).encode sizes
    ((SignedEncoding.representationEquiv (MvPolynomial.eval sizes width))
      ((SignedEncoding.representationEquiv (MvPolynomial.eval sizes width)).symm parts)).val = _
  rw [Equiv.apply_symm_apply]

/-- Equal magnitude widths and integer values have identical canonical words. -/
theorem binaryIntegers_encode_congr (firstWidth secondWidth : MvPolynomial Parameter ℕ)
    (sameWidth : firstWidth = secondWidth) (sizes : Parameter → ℕ)
    (first : (binaryIntegers firstWidth).Carrier sizes)
    (second : (binaryIntegers secondWidth).Carrier sizes) (sameValue : first.val = second.val) :
    ArrayEncoding.bits ((binaryIntegers firstWidth).encode sizes first) =
      ArrayEncoding.bits ((binaryIntegers secondWidth).encode sizes second) := by
  subst secondWidth
  have equal : first = second := Subtype.ext sameValue
  rw [equal]

/-- Constant-width integer words are independent of the runtime size context. -/
theorem binaryIntegers_fixed_encode_bits (width : ℕ) (sizes : Parameter → ℕ)
    (value : (binaryIntegers (MvPolynomial.C width)).Carrier sizes) :
    ArrayEncoding.bits ((binaryIntegers (MvPolynomial.C width)).encode sizes value) =
      [SignedEncoding.negative value.val] ++ ArrayEncoding.bits (BitVec.ofNat width value.val.natAbs) := by
  erw [binaryIntegers_encode_bits (MvPolynomial.C width) sizes value]
  erw [binaryNaturalsOfWidth_encode_bits (MvPolynomial.C width) sizes _]
  have signBits (sign : Bool) : ArrayEncoding.bits ((booleans : EncodedDomain Parameter).encode sizes sign) = [sign] := by
    change ArrayEncoding.bits ((fixed finTwoEquiv.symm).encode sizes sign) = [sign]
    erw [fixed_encode_bits finTwoEquiv.symm sizes sign]
    rw [show Nat.clog 2 2 = 1 by decide]
    cases sign <;> rfl
  rw [signBits]
  apply congrArg (fun payload => [SignedEncoding.negative value.val] ++ payload)
  simp only [BitVec.ofFin_eq_ofNat]
  exact congrArg (fun digits : ℕ => ArrayEncoding.bits (BitVec.ofNat digits value.val.natAbs))
    (show MvPolynomial.eval sizes (MvPolynomial.C width) = width by simp)

end Polytime2.EncodedDomain
