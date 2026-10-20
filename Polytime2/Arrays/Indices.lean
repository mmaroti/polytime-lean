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

import Polytime2.Arrays.PrefixCount
import Polytime2.Computation.ComputedSizes

/-! # Certified source-coordinate arrays for shared stable packing -/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Original positions, encoded with enough bits for every source coordinate.
Packing this array records the inverse of the shared source-to-dense table. -/
noncomputable def arrayIndices (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := (EncodedDomain.bitVectors (length + 1)).arrayOfLength length
  precondition _ _ := True
  compute sizes _ := fun index => BitVec.ofNat (MvPolynomial.eval sizes (length + 1)) index.val

theorem arrayIndices_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayIndices length).Realizable := by
  have flags := (polynomialUnarySize_realizable length).withEncodedOutput
    (EncodedDomain.booleans.arrayOfLength length) (fun _ _ => fun _ => true) (by
      intro sizes
      simp [polynomialUnarySize, EncodedDomain.boundedUnary, EncodedDomain.arrayOfLength, EncodedDomain.booleans,
        EncodedDomain.fixed, EncodedDomain.ofCodec, show Nat.clog 2 2 = 1 by decide]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      change EncodedDomain.ArrayEncoding.bits
        ((EncodedDomain.booleans.arrayOfLength length).encode sizes (fun _ => true)) =
          EncodedDomain.ArrayEncoding.bits (BoundedUnary.encode _ (Fin.last _))
      rw [FirstFalse.boolean_bits, BoundedUnary.encode_bits]
      simp [BoundedUnary.bits, polynomialUnarySize, EncodedDomain.boundedUnary])
  have counted := flags.followedBy (prefixCounts_realizable length) rfl (by intros; trivial)
  exact counted.withSpecification (fun _ _ => True) (arrayIndices length).compute (by intros; trivial) (by
    intro sizes arguments valid
    funext index
    change BitVec.ofNat _ (((List.ofFn (fun _ : Fin (MvPolynomial.eval sizes length) => true)).take index.val).count true) =
      BitVec.ofNat _ index.val
    congr 1
    simp)

end Polytime2.Computation
