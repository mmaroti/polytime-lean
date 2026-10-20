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

/-- Expose a bounded array as an ordinary exact array once its retained length
has been supplied as a size parameter. Elements may depend on original sizes. -/
noncomputable def boundedArrayAtSize (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (countName : Parameter) : Computation Parameter Unit :=
  unaryMap ((boundedArray element capacity).renameParameters hostNames)
    ((element.renameParameters hostNames).array countName)
    (fun sizes packed => packed.1.val = sizes countName)
    (fun _ packed position => packed.val.2 (Fin.cast packed.property.symm position))

theorem boundedArrayAtSize_realizable (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (hostNames : HostParameter → Parameter)
    (countName : Parameter) :
    (boundedArrayAtSize element capacity hostNames countName).Realizable := by
  apply Realizable.Internal.fieldProjection _ _
    (MvPolynomial.rename hostNames (boundedUnary capacity).widthPolynomial)
  intro sizes packed
  let original := sizes ∘ hostNames
  let count := packed.val.1
  let values := packed.val.2
  have targetBits : ArrayEncoding.bits
      (((element.renameParameters hostNames).array countName).encode sizes
        (fun position => values (Fin.cast packed.property.symm position))) =
      ArrayEncoding.bits (ArrayEncoding.encode (element.encode original) count.val values) := by
    simp only [EncodedDomain.array, ofCodec, ArrayEncoding.bits_cast,
      ArrayEncoding.bits_encode, renameParameters_bits]
    exact congrArg List.flatten (List.ofFn_congr packed.property
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
