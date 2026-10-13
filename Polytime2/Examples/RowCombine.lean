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

import Polytime2.StandardRowCombineContract

/-! # Separate-entry row combination, including zero-bit scalars -/

namespace Polytime2.Examples.RowCombine

open Polytime2.StandardRowCombine CallingConvention

-- Binary row addition: 1 + 1 * 1 = 0. Both result tapes start with arbitrary contents.
example : Runs (fun _ => 1) readOnly
    (machine (fun coefficient source target =>
      (if source 0 then 1#1 else 0#1,
        if target 0 != (coefficient 0 && source 0) then 1#1 else 0#1)))
    20 entry (fun _ => 0) (frame [true] [true] [true] [2] [0])
    exit (fun _ => 0) (frame [true] [true] [true] (Binary.word [true]) (Binary.word [false])) := by
  exact runs (fun coefficient source target =>
    (if source 0 then 1#1 else 0#1,
      if target 0 != (coefficient 0 && source 0) then 1#1 else 0#1))
    [true] [true] [true] rfl rfl rfl [2] [0] rfl rfl

example : Runs (fun _ => 0) readOnly (machine (fun _ _ _ => (0#0, 0#0)))
    10 entry (fun _ => 0) (frame [] [] [] [] []) exit (fun _ => 0) (frame [] [] [] [] []) := by
  exact runs (fun _ _ _ => (0#0, 0#0)) [] [] [] rfl rfl rfl [] [] rfl rfl

-- Three-element scalar presentations have an unused binary label. Decoding
-- valid inputs and encoding both outputs go through the domain certificate.
example : encodedTable (EncodedDomain.fixed (Equiv.refl (Fin 3)))
    (fun _ (coefficient source target : Fin 3) =>
      (source, (⟨(target.val + coefficient.val * source.val) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3)))
    (fun index => decide (index.val = 1)) (fun index => decide (index.val = 0)) (fun _ => false) =
      (1#2, 2#2) := by rfl

end Polytime2.Examples.RowCombine
