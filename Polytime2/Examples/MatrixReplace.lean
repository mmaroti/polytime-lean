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

import Polytime2.Computation.Composition
import Polytime2.Matrices.EntryOperations

/-! # Matrix replacement followed by lookup through public composition rules -/

namespace Polytime2.Examples.MatrixReplace

open Polytime2.Computation

noncomputable section CoordinateExamples

private def scalar : EncodedDomain Empty := EncodedDomain.booleans
private def sizes : Fin 2 → ℕ := ![2, 3]
private def replacement := matrixReplace scalar
private def arguments : replacement.Arguments sizes
  | 0 => (1 : Fin 2)
  | 1 => (2 : Fin 3)
  | 2 => fun _ _ => false
  | 3 => true
private theorem admissible : replacement.precondition sizes arguments := by
  trivial

example : replacement.Realizable := matrixReplace_realizable scalar
example : replacement.compute sizes ⟨arguments, admissible⟩ (1 : Fin 2) (2 : Fin 3) = true := rfl
example : replacement.compute sizes ⟨arguments, admissible⟩ (0 : Fin 2) (0 : Fin 3) = false := rfl

private def contextDomains : Fin 4 ⊕ Unit → EncodedDomain (Fin 2) :=
  Sum.elim replacement.inputDomains (fun _ => replacement.outputDomain)
private def lookupSelection : Fin 3 ↪ Fin 4 ⊕ Unit :=
  ⟨(fun | 0 => .inl 0 | 1 => .inl 1 | 2 => .inr ()), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
private def continuation := (matrixEntry scalar).withArguments contextDomains lookupSelection
  (by intro name; fin_cases name <;> rfl)
private def readBack := replacement.letThen continuation (fun _ => rfl) rfl
  (by intro sizes arguments valid; exact valid)

example : readBack.Realizable := by
  apply Computation.Realizable.letThen (matrixReplace_realizable scalar)
  exact (matrixEntry_realizable scalar).withArguments _ _ _

example : readBack.compute sizes ⟨arguments, admissible⟩ = true := rfl

example : (matrixReplace (EncodedDomain.fixed (Equiv.refl (Fin 1)))).Realizable :=
  matrixReplace_realizable _

end CoordinateExamples
end Polytime2.Examples.MatrixReplace
