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

import Polytime2.StandardMatrixEntryContract

/-! # Matrix lookup with arbitrary initial output and scratch contents -/

namespace Polytime2.Examples.MatrixEntry

open Polytime2.StandardMatrixEntry CallingConvention

-- Row 1, column 2 in a two-by-three Boolean matrix selects its last entry.
-- Output, counters, and flags start with arbitrary contents.
example : ∃ ticks final, Runs (fun name => (domains EncodedDomain.booleans name).width ![3, 2, 3])
    readOnly (machine 1) ticks (entry 1) (fun _ => 0)
    (frame ![3, 2, 3] [true, false, false] [false, true, false]
      (encoded (EncodedDomain.booleans.arrayOfLength length) ![3, 2, 3]
        (fun index => decide (index.val = 5)))
      [2] [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2] 2 2)
    (exit 1) (fun _ => 0) final ∧ final (.inr true) = tape [true] := by
  obtain ⟨ticks, addressBits, addressLength, addressValue, cost, trace⟩ :=
    runs EncodedDomain.booleans ![3, 2, 3] [true, false, false] [false, true, false] rfl rfl
      (fun index => decide (index.val = 5))
      [2] [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2] rfl rfl rfl rfl rfl rfl 2 2
      (by decide) (by decide) (by norm_num [length, Binary.value])
  exact ⟨ticks, _, trace, rfl⟩

-- A singleton scalar has zero-bit width. The same routine still restores
-- every head and writes a valid element into its empty output region.
example : ∃ ticks final, Runs
    (fun name => (domains (EncodedDomain.fixed (Equiv.refl (Fin 1))) name).width ![1, 1, 1])
    readOnly (machine 0) ticks (entry 0) (fun _ => 0)
    (frame ![1, 1, 1] [false] [false]
      (encoded ((EncodedDomain.fixed (Equiv.refl (Fin 1))).arrayOfLength length) ![1, 1, 1]
        (fun _ => (0 : Fin 1))) [] [2] [0] [2] [0] [2] 2 2)
    (exit 0) (fun _ => 0) final ∧ final (.inr true) = tape [] := by
  obtain ⟨ticks, addressBits, addressLength, addressValue, cost, trace⟩ :=
    runs (EncodedDomain.fixed (Equiv.refl (Fin 1))) ![1, 1, 1] [false] [false] rfl rfl
      (fun _ => (0 : Fin 1)) [] [2] [0] [2] [0] [2] rfl rfl rfl rfl rfl rfl 2 2
      (by decide) (by decide) (by norm_num [length, Binary.value])
  exact ⟨ticks, _, trace, rfl⟩

end Polytime2.Examples.MatrixEntry
