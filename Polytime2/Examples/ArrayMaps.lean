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

import Polytime2.StandardArrayMapContract
import Polytime2.FieldRow

/-! # Binary array maps and finite-field row scaling -/

namespace Polytime2.Examples.ArrayMaps

open CallingConvention StandardArrayMap

-- A Boolean parameter flips two one-bit entries. The old output is blank
-- or contains old bits, so this also checks that traversal ignores old output symbols.
example : ∃ ticks, ticks ≤ 45 ∧
    Runs (widths 1 2) readOnly
      (machine (parameterWidth := 1) (elementWidth := 1)
        (fun parameter value => if parameter 0 != value 0 then 1#1 else 0#1))
      ticks entry (fun _ => 0)
      (frame (parameterWidth := 1) (fun _ => true) [] [true, false] [] [0, 2])
      exit (fun _ => 0)
      (StandardFiniteTable.frame [true] [true, false] (Binary.word [false, true])) := by
  simpa [bits, mapped, List.ofFn_succ, List.ofFn_zero] using
    runs (parameterWidth := 1) (elementWidth := 1)
      (fun parameter value => if parameter 0 != value 0 then 1#1 else 0#1)
      (fun _ => true) [fun _ => true, fun _ => false] [0, 2] rfl

-- A nonempty array of zero-bit elements has no data cells to initialize.
example : ∃ ticks, ticks ≤ 36 ∧
    Runs (widths 0 0) readOnly
      (machine (parameterWidth := 0) (elementWidth := 0) (fun _ _ => 0#0))
      ticks entry (fun _ => 0) (frame Fin.elim0 [] [] [] [])
      exit (fun _ => 0) (StandardFiniteTable.frame [] [] []) := by
  simpa [bits, mapped, Binary.word] using
    runs (parameterWidth := 0) (elementWidth := 0) (fun _ _ => 0#0)
      Fin.elim0 [Fin.elim0, Fin.elim0, Fin.elim0] [] rfl

-- Scalar: a specialization-fixed finite field; Parameter: unary size names.
-- The array can be a matrix row whose length is any size polynomial.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {Scalar : Type} [Field Scalar] [Fintype Scalar]

example (length : MvPolynomial Parameter ℕ) :
    let domain := FieldRow.scalarDomain (Fintype.equivFin Scalar)
    CallingConvention.Realizes (domains domain domain length)
      argumentReadOnly sizeTapes
      (algorithm domain domain (fun _ (coefficient value : Scalar) => coefficient * value))
      entry exit (fun _ _ => True)
      (fun _ input output => output ⟨.inr 2, rfl⟩ = fun index =>
        (fun (coefficient value : Scalar) => coefficient * value)
          (input ⟨.inr 0, rfl⟩) (input ⟨.inr 1, rfl⟩ index)) :=
  FieldRow.scale_contract (Fintype.equivFin Scalar) length

end Polytime2.Examples.ArrayMaps
