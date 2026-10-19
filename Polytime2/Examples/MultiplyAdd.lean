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

import Polytime2.Arithmetic.Operations

/-! # Compound arithmetic through existential computation certificates -/

namespace Polytime2.Examples.MultiplyAdd

open Polytime2.Computation

example : binaryMultiplyAdd.Realizable := binaryMultiplyAdd_realizable
example : binaryAddMultiply.Realizable := binaryAddMultiply_realizable

-- Row 2, width 3, and column 1 give row-major address 7.
private def sizes (parameter : Bool) : ℕ := if parameter then 2 else 3
private def arguments : binaryMultiplyAdd.Arguments sizes :=
  fun name => ⟨![2, 3, 1] name, by fin_cases name <;> decide⟩
private theorem admissible : binaryMultiplyAdd.precondition sizes arguments := by
  change 2 * 3 + 1 < 2 ^ 3
  decide

example : (binaryMultiplyAdd.compute sizes ⟨arguments, admissible⟩).val = 7 := rfl

-- The intermediate sum and final product fit a three-bit result.
private def sumArguments : binaryAddMultiply.Arguments sizes :=
  fun name => ⟨![1, 2, 2] name, by fin_cases name <;> decide⟩
private theorem sumAdmissible : binaryAddMultiply.precondition sizes sumArguments := by
  change 1 + 2 < 2 ^ 3 ∧ (1 + 2) * 2 < 2 ^ 3
  decide

example : (binaryAddMultiply.compute sizes ⟨sumArguments, sumAdmissible⟩).val = 6 := rfl

-- Zero-bit operands still admit a valid zero result.
example : binaryMultiplyAdd.precondition (fun _ => 0) (fun _ => ⟨0, by decide +revert⟩) := by
  change 0 * 0 + 0 < 2 ^ 0
  decide
example : binaryAddMultiply.precondition (fun _ => 0) (fun _ => ⟨0, by decide +revert⟩) := by
  change 0 + 0 < 2 ^ 0 ∧ (0 + 0) * 0 < 2 ^ 0
  decide

end Polytime2.Examples.MultiplyAdd
