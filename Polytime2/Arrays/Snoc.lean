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

import Polytime2.Arrays.Queue
import Polytime2.Computation.Conditional

/-! # Appending one mathematical array element

Record construction and the existing snoc encoding identity realize appending
one element. Neither an element default nor a storage-specific carrier is
needed, and the old array may be empty.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Append the true input element to the false input array. -/
noncomputable def arraySnoc (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains | false => element.arrayOfLength length | true => element
  outputDomain := element.arrayOfLength (length + 1)
  precondition _ _ := True
  compute sizes arguments := snocValues length sizes (arguments.val false) (arguments.val true)

/-- The array's canonical bits are exactly the old array bits followed by the new element bits. -/
theorem arraySnoc_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arraySnoc element length).Realizable := by
  let computation := arraySnoc element length
  have pair := (Realizable.argument computation.inputDomains false computation.precondition).prodMk (Realizable.argument computation.inputDomains true computation.precondition)
  apply pair.withEncodedOutput computation.outputDomain computation.compute
  · intro sizes
    change MvPolynomial.eval sizes ((length + 1) * element.widthPolynomial) =
      MvPolynomial.eval sizes (length * element.widthPolynomial + element.widthPolynomial)
    congr 1
    ring
  · intro sizes arguments
    exact congrArg CallingConvention.tape (arraySnoc_encode_bits element length sizes (arguments.val false) (arguments.val true))

end Polytime2.Computation
