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

import Polytime2.StandardFiniteTable

/-! # Finite tables overwrite arbitrary fixed regions -/

namespace Polytime2.Examples.FiniteTables

open CallingConvention StandardFiniteTable

-- The output contains blanks and old binary data before the call.
example : Runs (widths 1 1 2) readOnly
    (machine (firstWidth := 1) (secondWidth := 1) (fun first second => if first 0 && second 0 then 2#2 else 1#2))
    14 entry (fun _ => 0) (frame [true] [true] [0, 2])
    exit (fun _ => 0) (frame [true] [true] (Binary.word [false, true])) := by
  simpa [Binary.word] using runs (firstWidth := 1) (secondWidth := 1) (fun first second => if first 0 && second 0 then 2#2 else 1#2)
    [true] [true] rfl rfl [0, 2] rfl

-- An internal scalar block can have other array elements on both sides.
example (left right : Fin 3 → List Binary.Symbol) :
    Runs (widths 1 1 2) readOnly
      (machine (firstWidth := 1) (secondWidth := 1)
        (fun first second => if first 0 && second 0 then 2#2 else 1#2))
      14 entry (fun _ => 0) (frameWithContext [true] [true] [0, 2] left right)
      exit (fun _ => 0)
      (frameWithContext [true] [true] (Binary.word [false, true]) left right) := by
  simpa [Binary.word] using runsWithContext (firstWidth := 1) (secondWidth := 1)
    (fun first second => if first 0 && second 0 then 2#2 else 1#2)
    [true] [true] rfl rfl [0, 2] rfl left right

-- Empty arguments and result still preserve both inputs and restore every head.
example : Runs (widths 0 0 0) readOnly (machine (firstWidth := 0) (secondWidth := 0) (fun _ _ => 0#0))
    6 entry (fun _ => 0) (frame [] [] [])
    exit (fun _ => 0) (frame [] [] []) := by
  simpa [Binary.word] using runs (firstWidth := 0) (secondWidth := 0) (fun _ _ => 0#0) [] [] rfl rfl [] rfl

-- The mathematical contract works with a non-power-of-two scalar carrier.
example :
    let domain : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 3))
    CallingConvention.Realizes (domains domain domain domain) readOnly sizeTapes
      (algorithm domain domain domain (fun _ (first : Fin 3) (second : Fin 3) => first + second))
      entry exit (fun _ _ => True)
      (fun _ input output => output ⟨2, rfl⟩ = ((fun (a b : Fin 3) => a + b) (input ⟨0, rfl⟩) (input ⟨1, rfl⟩))) :=
  StandardFiniteTable.contract (EncodedDomain.fixed (Equiv.refl (Fin 3)))
    (EncodedDomain.fixed (Equiv.refl (Fin 3))) (EncodedDomain.fixed (Equiv.refl (Fin 3)))
    (fun _ (first : Fin 3) (second : Fin 3) => first + second)

end Polytime2.Examples.FiniteTables
