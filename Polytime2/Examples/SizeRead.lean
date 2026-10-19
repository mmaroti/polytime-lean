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

import Polytime2.Primitives.SizeOperations

/-! # Unary sizes read through arbitrary fixed-width output regions -/

namespace Polytime2.Examples.SizeRead

open CallingConvention StandardSizeRead

example : Computation.readSize.Realizable := Computation.readSize_realizable

-- The public computation exposes only the mathematical count.
example : (Computation.readSize.compute (fun name => if name then 2 else 3)
    ⟨(fun name => nomatch name), by change 3 < 2 ^ 2; decide⟩).val = 3 := rfl

-- Read size three into a two-bit counter, overwriting arbitrary old counter contents.
example : ∃ scratch : List Bool, scratch.length = 2 ∧
    Runs (widths 3 2) readOnly machine 67 entry (fun _ => 0)
      (entryFrame 3 2 [0, 2] [2, 0]) exit (fun _ => 0)
      (entryFrame 3 2 (Binary.word [true, true]) (Binary.word scratch)) := by
  simpa [advanceBits, BinaryScan.run, BinaryScan.increment] using runs 3 2 [0, 2] [2, 0] rfl rfl

-- Zero size and zero-bit capacity still clear scratch and restore every head.
example : Runs (widths 0 0) readOnly machine 11 entry (fun _ => 0)
    (entryFrame 0 0 [] []) exit (fun _ => 0) (entryFrame 0 0 [] []) := by
  obtain ⟨scratch, scratchLength, trace⟩ := runs 0 0 [] [] rfl rfl
  have empty : scratch = [] := List.eq_nil_of_length_eq_zero scratchLength
  subst scratch
  simpa [advanceBits, Binary.word] using trace

end Polytime2.Examples.SizeRead
