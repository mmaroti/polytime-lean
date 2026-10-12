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

import Polytime2.AddMultiplyExternal
import Polytime2.BinarySubtraction

/-! # External arithmetic boundary cases

The public input contains widths and operands only; empty widths are valid.
The complete realization theorem covers these inputs with the same controller.
-/

namespace Polytime2.Examples.Arithmetic

open AddMultiplyInput (Input inputWord preparedAt blank)
open AddMultiplyExternal (compute)

#guard inputWord ([], [], []) = [3, 3, 0]
#guard compute ([], [], []) = 0
#guard compute ([true, true, true], [true, false, false], [true, false, true, true]) = 104
#guard (inputWord ([true, true, true], [true, false, false], [true, false, true, true])).length = 20
#guard compute ([true], [true], []) = 0

-- The final subtraction bit is the borrow; lower bits retain their capacity.
#guard BinarySubtraction.subtract [true, true, false] [true, false, true] =
  [false, true, true, true]
#guard BinarySubtraction.subtract [true, false, true] [true, true, false] =
  [false, true, false, false]
#guard BinarySubtraction.subtract [true, false, true] [true, false, true] =
  [false, false, false, false]
#guard BinarySubtraction.subtract [] [] = [false]

-- Only the external input tape contains data at entry.
example (input : Input) (name : Fin 10) (working : name ≠ 7) :
    preparedAt input 0 name = blank := by
  fin_cases name <;> simp_all [preparedAt]

-- The encoded width fields agree with both size parameters.
example : AddMultiplyExternal.hypothesis (fun name => if name then 4 else 3)
    ([true, true, true], [true, false, false], [true, false, true, true]) := by
  unfold AddMultiplyExternal.hypothesis
  decide

-- The preparer also handles all widths zero.
example : ∃ ticks, ticks ≤ 108 ∧ MultiTape.Steps AddMultiplyInput.machine ticks
    (AddMultiplyInput.entry, preparedAt ([], [], []) 0)
    (none, preparedAt ([], [], []) 9) := by
  simpa using AddMultiplyInput.steps ([], [], []) rfl

-- Runtime widths do not enter the controller type.
example : Fintype AddMultiplyExternal.State := inferInstance

end Polytime2.Examples.Arithmetic
