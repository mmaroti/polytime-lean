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

import Polytime2.StandardMatrixReplaceContract

/-! # Matrix replacement with a separate, arbitrary initial output -/

namespace Polytime2.Examples.MatrixReplace

open Polytime2.StandardMatrixReplace CallingConvention

-- Replace row 1, column 2 by true. The six output cells and all arithmetic
-- scratch may initially contain blanks or unrelated bits.
example : ∃ ticks final, Runs
    (fun name => (domains EncodedDomain.booleans name).width ![3, 2, 3])
    readOnly (machine 1) ticks (entry 1) (fun _ => 0)
    (frame ![3, 2, 3] [true, false, false] [false, true, false]
      (encoded (EncodedDomain.booleans.arrayOfLength StandardMatrixEntry.length) ![3, 2, 3] (fun _ => false))
      (buffer [0, 2, 0, 2, 0, 2]) (Binary.word [true])
      [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2] 2 2)
    (exit 1) (fun _ => 0) final ∧
    final (.inr 2) = encoded (EncodedDomain.booleans.arrayOfLength StandardMatrixEntry.length)
      ![3, 2, 3] (Function.update (fun _ => false) ⟨5, by norm_num [StandardMatrixEntry.length]⟩ true) := by
  obtain ⟨ticks, addressBits, addressLength, addressValue, cost, trace⟩ :=
    runs EncodedDomain.booleans ![3, 2, 3] [true, false, false] [false, true, false] rfl rfl
      (fun _ => false) true [0, 2, 0, 2, 0, 2]
      [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2]
      (by norm_num [EncodedDomain.arrayOfLength, StandardMatrixEntry.length,
        EncodedDomain.booleans, EncodedDomain.fixed]) rfl rfl rfl rfl rfl 2 2
      (by decide) (by decide) (by norm_num [StandardMatrixEntry.length, Binary.value])
  exact ⟨ticks, _, trace, rfl⟩

end Polytime2.Examples.MatrixReplace
