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

import Polytime2.Matrices.EntryOperations

/-! # Mathematical matrix lookup by row and column -/

namespace Polytime2.Examples.MatrixEntry

open Polytime2.Computation

noncomputable section CoordinateExamples

private def scalar : EncodedDomain Empty := EncodedDomain.booleans
private def sizes : Fin 3 → ℕ := ![3, 2, 3]
private def original : Matrix (Fin 2) (Fin 3) Bool :=
  ![![false, false, false], ![false, false, true]]
private def lookup := matrixEntry scalar
private def arguments : lookup.Arguments sizes
  | 0 => (1 : Fin 8)
  | 1 => (2 : Fin 8)
  | 2 => original
private theorem admissible : lookup.precondition sizes arguments := by
  change 3 < 2 ^ 3 ∧ 1 < 2 ∧ 2 < 3 ∧ 2 * 3 ≤ 2 ^ 3
  decide

example : lookup.Realizable := matrixEntry_realizable scalar
example : lookup.compute sizes ⟨arguments, admissible⟩ = true := rfl

-- Singleton scalars and the complete matrix occupy zero bits.
example : (matrixEntry (EncodedDomain.fixed (Equiv.refl (Fin 1)))).Realizable :=
  matrixEntry_realizable _

end CoordinateExamples
end Polytime2.Examples.MatrixEntry
