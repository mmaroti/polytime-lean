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

import Polytime2.Encoding.BoundedArray
import Polytime2.Primitives.BitOperations

/-! # Empty bounded arrays without default elements

Initialize the shared bounded-array codec at count zero. The payload is empty
and its storage padding is all zero, even when the element carrier is empty.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Initialize a bounded array with no mathematical elements. -/
noncomputable def boundedArrayEmpty (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := boundedArray element capacity
  precondition _ _ := True
  compute _ _ := ⟨⟨0, by omega⟩, Fin.elim0⟩

/-- Zero allocation initializes the exact canonical empty-array encoding. -/
theorem boundedArrayEmpty_realizable (element : EncodedDomain Parameter) (capacity : MvPolynomial Parameter ℕ) :
    (boundedArrayEmpty element capacity).Realizable := by
  have ready := zeroBits_realizable (capacity + capacity * element.widthPolynomial)
  apply ready.withEncodedOutput (boundedArray element capacity) (boundedArrayEmpty element capacity).compute (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  change ArrayEncoding.bits (((boundedUnary capacity).prod (bitVectors (capacity * element.widthPolynomial))).encode sizes
    (⟨0, by omega⟩, (ArrayEncoding.encode (element.encode sizes) 0 Fin.elim0).setWidth _)) =
    ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes (capacity + capacity * element.widthPolynomial)))
  rw [bits_prod_encode]
  have empty : ArrayEncoding.encode (element.encode sizes) 0 Fin.elim0 = 0 := by rfl
  have header : ArrayEncoding.bits ((boundedUnary capacity).encode sizes ⟨0, by omega⟩) =
      List.replicate (MvPolynomial.eval sizes capacity) false := by
    change ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes capacity) ⟨0, by omega⟩) = _
    rw [BoundedUnary.encode_bits]
    simp [BoundedUnary.bits]
  rw [header]
  simp [empty, bitVectors, ArrayEncoding.bits, map_add]

end Polytime2.Computation
