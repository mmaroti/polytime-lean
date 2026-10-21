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

import Polytime2.Encoding.Integers
import Polytime2.Computation.Fields

/-! # Certified sign and magnitude of ordinary bounded integers

Both operations accept every integer at the given magnitude width. Sign means
strict negativity, so zero has false sign; magnitude is the ordinary natural
absolute value at the original word width. Neither operation needs scratch
capacity from callers.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Test strict negativity, with zero treated as nonnegative. -/
noncomputable def integerNegative (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryIntegers width) booleans (fun _ _ => True)
    (fun _ value => SignedEncoding.negative value.val.val)

theorem integerNegative_realizable (width : MvPolynomial Parameter ℕ) :
    (integerNegative width).Realizable := by
  apply Realizable.Internal.fieldProjection (binaryIntegers width) booleans 0
  intro sizes value
  exact ⟨[], ArrayEncoding.bits ((binaryNaturalsOfWidth width).encode sizes
    ⟨value.val.val.natAbs, value.val.property⟩),
    by simpa using binaryIntegers_encode_bits width sizes value.val, by simp⟩

/-- Extract the ordinary natural magnitude without changing its bit width. -/
noncomputable def integerMagnitude (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryIntegers width) (binaryNaturalsOfWidth width) (fun _ _ => True)
    (fun _ value => ⟨value.val.val.natAbs, value.val.property⟩)

theorem integerMagnitude_realizable (width : MvPolynomial Parameter ℕ) :
    (integerMagnitude width).Realizable := by
  apply Realizable.Internal.fieldProjection (binaryIntegers width) (binaryNaturalsOfWidth width) 1
  intro sizes value
  refine ⟨ArrayEncoding.bits (booleans.encode sizes (SignedEncoding.negative value.val.val)), [],
    ?_, ?_⟩
  · simpa using binaryIntegers_encode_bits width sizes value.val
  · simp [booleans, fixed, ofCodec]
    decide

end Polytime2.Computation
