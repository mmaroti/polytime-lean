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

import Polytime2.Matrices.IntegerOperations

/-! # Transposing paired integer matrices

Transpose both ordinary matrices in a coupled result without changing their
magnitude bounds. Row/column dual algorithms share this realization.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Transpose both matrices of a coupled result. -/
noncomputable def integerMatrixPairTranspose
    (firstRows firstColumns secondRows secondColumns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (integerMatrices firstRows firstColumns width).prod (integerMatrices secondRows secondColumns width)
  outputDomain := (integerMatrices firstColumns firstRows width).prod (integerMatrices secondColumns secondRows width)
  precondition _ _ := True
  compute _ arguments :=
    (⟨(arguments.val ()).1.val.transpose, fun column row => (arguments.val ()).1.property row column⟩,
      ⟨(arguments.val ()).2.val.transpose, fun column row => (arguments.val ()).2.property row column⟩)

theorem integerMatrixPairTranspose_realizable
    (firstRows firstColumns secondRows secondColumns width : MvPolynomial Parameter ℕ) :
    (integerMatrixPairTranspose firstRows firstColumns secondRows secondColumns width).Realizable := by
  have mapped := (integerMatrixTranspose_realizable firstRows firstColumns width).prodMap
    (integerMatrixTranspose_realizable secondRows secondColumns width)
  exact mapped.withSpecification (fun _ _ => True)
    (integerMatrixPairTranspose firstRows firstColumns secondRows secondColumns width).compute
    (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
