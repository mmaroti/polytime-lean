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

end Polytime2.EncodedDomain
