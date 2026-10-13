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

import Polytime2.StandardMatrixAddressContract

/-! # Matrix addresses computed from unary dimensions -/

namespace Polytime2.Examples.MatrixAddress

open Polytime2.StandardMatrixAddress CallingConvention

-- Two rows, three columns, and three-bit indices; every writable region
-- starts blank or contains unrelated bits. Row 1, column 2 has row-major address 5.
example : ∃ scratch : List Bool, scratch.length = 3 ∧
    Runs (fun name => (domains name).width (![3, 2, 3])) readOnly machine 221
      entry (fun _ => 0)
      (frame ![3, 2, 3] [true, false, false] [false, true, false]
        [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2] 2 2)
      exit (fun _ => 0)
      (frame ![3, 2, 3] [true, false, false] [false, true, false]
        (Binary.word (MultiplyAdd.product [true, false, false] (columnBits ![3, 2, 3])
          (Binary.word scratch) [0, 0, 2] 2))
        (Binary.word [false, false, false]) (Binary.word [false, false, false])
        (Binary.word (columnBits ![3, 2, 3]))
        (Binary.word (MultiplyAdd.result [true, false, false] (columnBits ![3, 2, 3])
          [false, true, false] (Binary.word scratch) [0, 0, 2] 2))
        (Binary.data false) (Binary.data false)) := by
  exact runs ![3, 2, 3] [true, false, false] [false, true, false] rfl rfl
    [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] [0, 2, 2] rfl rfl rfl rfl rfl 2 2
    (by decide) (by decide)

example : Binary.value (columnBits ![3, 2, 3]) = 3 :=
  columnBits_value ![3, 2, 3] (by decide)

end Polytime2.Examples.MatrixAddress
