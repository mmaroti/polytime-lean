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

import Polytime2.Arrays.PackingResult
import Polytime2.Encoding.ParameterRename

/-! # Reading packed arrays at their exact runtime size

Several packed arrays can share a computed-size call. Each field is read at its
own count from the immutable size tapes; capacity padding stays private.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type}
variable [Fintype HostParameter] [Fintype Parameter]

/-- Extract the stored elements at their exact named length, converting each
element at admissible runtime sizes. Realization requires identical element
encodings, so conversion needs no elementwise machine work. -/
noncomputable def boundedArrayAtSize (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (countName : Parameter) (target : EncodedDomain Parameter)
    (allowed : (Parameter → ℕ) → Prop)
    (convert : ∀ sizes, allowed sizes → element.Carrier (sizes ∘ hostNames) → target.Carrier sizes) :
    Computation Parameter Unit :=
  unaryMap ((boundedArray element capacity).renameParameters hostNames)
    (target.array countName)
    (fun sizes packed => packed.1.val = sizes countName ∧ allowed sizes)
    (fun sizes packed position => convert sizes packed.property.2
      (packed.val.2 (Fin.cast packed.property.1.symm position)))

theorem boundedArrayAtSize_realizable (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (countName : Parameter) (target : EncodedDomain Parameter)
    (allowed : (Parameter → ℕ) → Prop)
    (convert : ∀ sizes, allowed sizes → element.Carrier (sizes ∘ hostNames) → target.Carrier sizes)
    (sameBits : ∀ sizes (valid : allowed sizes) value,
      ArrayEncoding.bits (target.encode sizes (convert sizes valid value)) =
        ArrayEncoding.bits (element.encode (sizes ∘ hostNames) value)) :
    (boundedArrayAtSize element capacity hostNames countName target allowed convert).Realizable := by
  apply Realizable.Internal.fieldProjection _ _
    (MvPolynomial.rename hostNames (boundedUnary capacity).widthPolynomial)
  intro sizes packed
  let original := sizes ∘ hostNames
  let count := packed.val.1
  let values := packed.val.2
  have targetBits : ArrayEncoding.bits
      ((target.array countName).encode sizes
        (fun position => convert sizes packed.property.2
          (values (Fin.cast packed.property.1.symm position)))) =
      ArrayEncoding.bits (ArrayEncoding.encode (element.encode original) count.val values) := by
    simp only [array_encode_bits, ArrayEncoding.bits_encode, sameBits]
    exact congrArg List.flatten (List.ofFn_congr packed.property.1
      (fun position => ArrayEncoding.bits (element.encode original (values position)))).symm
  refine ⟨ArrayEncoding.bits ((boundedUnary capacity).encode original count),
    List.replicate (MvPolynomial.eval original (capacity * element.widthPolynomial) -
      count.val * element.width original) false, ?_, ?_⟩
  · rw [targetBits, renameParameters_bits]
    change ArrayEncoding.bits (((boundedUnary capacity).prod
      (bitVectors (capacity * element.widthPolynomial))).encode original
        (count, (ArrayEncoding.encode (element.encode original) count.val values).setWidth _)) = _
    rw [bits_prod_encode, bits_setWidth _ (by
      simp only [map_mul]
      exact Nat.mul_le_mul_right (element.width original) (Nat.le_of_lt_succ count.isLt))]
    exact (List.append_assoc _ _ _).symm
  · simp only [ArrayEncoding.bits, List.length_ofFn, MvPolynomial.eval_rename]
    rfl

end Polytime2.Computation
