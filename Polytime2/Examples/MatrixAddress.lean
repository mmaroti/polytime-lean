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

import Polytime2.Matrices.AddressOperations

/-! # Matrix addresses computed from unary dimensions -/

namespace Polytime2.Examples.MatrixAddress

open Polytime2.Computation.Realizable.Internal

example : matrixAddress.Realizable := matrixAddress_realizable

-- Row one, column two of a three-column matrix has row-major address five.
example : (matrixAddress.compute ![3, 2, 3]
    ⟨(fun | false => (1 : Fin 8) | true => (2 : Fin 8)),
      by change 3 < 8 ∧ 1 * 3 + 2 < 8; decide⟩ : Fin 8) = (5 : Fin 8) := rfl

-- No data bits are needed when both operands and the column count are zero.
example : (matrixAddress.compute ![0, 0, 0]
    ⟨(fun _ => (0 : Fin 1)), by change 0 < 1 ∧ 0 * 0 + 0 < 1; decide⟩ : Fin 1) =
    (0 : Fin 1) := rfl

end Polytime2.Examples.MatrixAddress
