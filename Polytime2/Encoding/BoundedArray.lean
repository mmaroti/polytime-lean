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

import Polytime2.Encoding.Dependent
import Polytime2.Encoding.BoundedUnary

/-! # Exact-length arrays with polynomial-capacity encodings

The mathematical payload contains only the chosen number of elements. Its
canonical encoding stores the unary count followed by zero-padded element bits.
-/

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- A bounded array exposes its count and precisely that many mathematical
values. No default element is needed for capacity padding. -/
noncomputable def boundedArray (element : EncodedDomain Parameter)
    (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ofBoundedCodec (boundedUnary length)
    (fun sizes count => Fin count.val → element.Carrier sizes)
    (fun sizes count => count.val * element.width sizes)
    (fun sizes count => ArrayEncoding.encode (element.encode sizes) count.val)
    (fun sizes count => ArrayEncoding.decode (element.decode sizes) count.val)
    (fun sizes count => ArrayEncoding.decode_encode _ _ (element.decode_encode sizes) count.val)
    (length * element.widthPolynomial) (by
      intro sizes count
      simp only [map_mul]
      exact Nat.mul_le_mul_right (element.width sizes) (Nat.le_of_lt_succ count.isLt))

/-- Convert stored elements between equally wide codecs at equal capacities.
The actual count is retained, including for empty element carriers. -/
noncomputable def boundedArrayConvert {TargetParameter : Type} [Fintype TargetParameter]
    (source : EncodedDomain Parameter) (target : EncodedDomain TargetParameter)
    (sourceCapacity : MvPolynomial Parameter ℕ) (targetCapacity : MvPolynomial TargetParameter ℕ)
    (sourceSizes : Parameter → ℕ) (targetSizes : TargetParameter → ℕ)
    (sameCapacity : MvPolynomial.eval sourceSizes sourceCapacity = MvPolynomial.eval targetSizes targetCapacity)
    (convert : source.Carrier sourceSizes → target.Carrier targetSizes)
    (field : (boundedArray source sourceCapacity).Carrier sourceSizes) :
    (boundedArray target targetCapacity).Carrier targetSizes :=
  ⟨⟨field.1.val, by rw [← sameCapacity]; exact field.1.isLt⟩, fun index => convert (field.2 index)⟩

/-- Encoding-preserving element conversion also preserves the complete stored
array encoding, including count bits and inactive capacity padding. -/
theorem boundedArrayConvert_bits {TargetParameter : Type} [Fintype TargetParameter]
    (source : EncodedDomain Parameter) (target : EncodedDomain TargetParameter)
    (sourceCapacity : MvPolynomial Parameter ℕ) (targetCapacity : MvPolynomial TargetParameter ℕ)
    (sourceSizes : Parameter → ℕ) (targetSizes : TargetParameter → ℕ)
    (sameCapacity : MvPolynomial.eval sourceSizes sourceCapacity = MvPolynomial.eval targetSizes targetCapacity)
    (convert : source.Carrier sourceSizes → target.Carrier targetSizes)
    (sameWidth : source.width sourceSizes = target.width targetSizes)
    (sameBits : ∀ value, ArrayEncoding.bits (source.encode sourceSizes value) =
      ArrayEncoding.bits (target.encode targetSizes (convert value)))
    (field : (boundedArray source sourceCapacity).Carrier sourceSizes) :
    ArrayEncoding.bits ((boundedArray source sourceCapacity).encode sourceSizes field) =
      ArrayEncoding.bits ((boundedArray target targetCapacity).encode targetSizes
        (boundedArrayConvert source target sourceCapacity targetCapacity sourceSizes targetSizes
          sameCapacity convert field)) := by
  change ArrayEncoding.bits (((boundedUnary sourceCapacity).prod
      (bitVectors (sourceCapacity * source.widthPolynomial))).encode sourceSizes
      (field.1, (ArrayEncoding.encode (source.encode sourceSizes) field.1.val field.2).setWidth _)) =
    ArrayEncoding.bits (((boundedUnary targetCapacity).prod
      (bitVectors (targetCapacity * target.widthPolynomial))).encode targetSizes
      (_, (ArrayEncoding.encode (target.encode targetSizes) field.1.val
        (fun index => convert (field.2 index))).setWidth _))
  rw [bits_prod_encode, bits_prod_encode]
  congr 1
  · simp only [boundedUnary, BoundedUnary.encode_bits]
    exact congrArg (fun capacity => BoundedUnary.bits capacity field.1.val) sameCapacity
  · apply ArrayEncoding.bits_setWidth_congr_of_eq
    · simp only [ArrayEncoding.bits_encode, sameBits]
    · simp only [map_mul]
      exact congrArg₂ (· * ·) sameCapacity sameWidth

end Polytime2.EncodedDomain
