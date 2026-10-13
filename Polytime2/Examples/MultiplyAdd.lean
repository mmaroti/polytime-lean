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

import Polytime2.MultiplyAddContract

/-! # Binary row-major address arithmetic -/

namespace Polytime2.Examples.MultiplyAdd

open CallingConvention
open Polytime2.MultiplyAdd

-- Row 2, width 3, column 1 give address 7. Every writable cell starts
-- blank or contains old bits; both arithmetic flags hold arbitrary values.
example : Runs (widths 3 2) readOnly machine 105 entry (fun _ => 0)
    (frame [false, true, false] [true, true] [true, false, false]
      [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] 2 2)
    exit (fun _ => 0)
    (frame [false, true, false] [true, true] [true, false, false]
      (Binary.word [false, true, true]) (Binary.word [false, false, false])
      (Binary.word [false, false, false]) (Binary.word [true, true, true])
      (Binary.data false) (Binary.data false)) := by
  exact runs [false, true, false] [true, true] [true, false, false] rfl
    [0, 2, 0] [2, 0, 0] [0, 0, 2] [2, 2, 0] rfl rfl rfl rfl 2 2 (by decide)

-- Zero-bit words still initialize both flags and restore all heads.
example : Runs (widths 0 0) readOnly machine 17 entry (fun _ => 0)
    (frame [] [] [] [] [] [] [] 2 2) exit (fun _ => 0)
    (frame [] [] [] [] [] [] [] (Binary.data false) (Binary.data false)) :=
  runs [] [] [] rfl [] [] [] [] rfl rfl rfl rfl 2 2 (by decide)

end Polytime2.Examples.MultiplyAdd
