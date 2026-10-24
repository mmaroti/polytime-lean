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

import Polytime2.Arithmetic.SignedDivides
import Polytime2.Arrays.ZipWith
import Polytime2.Arrays.AllTrue

/-! # Pointwise divisibility of integer arrays

Input two signed integer arrays of the same mathematical length, with
independent magnitude widths. Return whether each entry of the first divides
the corresponding entry of the second. The test is total, including zero
divisors and empty arrays, and supports Smith feasibility.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def flags (length divisorWidth valueWidth : MvPolynomial Parameter ℕ) :=
  arrayZipWith (Empty.elim : Empty → EncodedDomain Parameter)
    (binaryIntegers divisorWidth) (binaryIntegers valueWidth) booleans length
    (fun sizes _ divisor value => (integerDividesAtWidths divisorWidth valueWidth).compute sizes
      ⟨(fun choice => match choice with | false => divisor | true => value), trivial⟩)

private theorem flags_realizable (length divisorWidth valueWidth : MvPolynomial Parameter ℕ) :
    (flags length divisorWidth valueWidth).Realizable := by
  apply arrayZipWith_realizable
  exact (integerDividesAtWidths_realizable divisorWidth valueWidth).withArguments _
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro choice; cases choice <;> rfl)

/-- Test every pointwise divisibility condition, including zero divisors. -/
noncomputable def integerArrayDivides (length divisorWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  ((flags length divisorWidth valueWidth).followedBy (arrayAllTrue length) rfl (by intros; trivial)).onResults
    (fun choice => (if choice then binaryIntegers valueWidth else binaryIntegers divisorWidth).arrayOfLength length)
    (fun _ _ => True)
    (fun name _ arguments => match name with | .inl impossible => nomatch impossible | .inr choice => arguments.val choice)
    (by intros; trivial)

/-- Certified scalar divisibility, pointwise traversal, and Boolean conjunction suffice. -/
theorem integerArrayDivides_realizable (length divisorWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerArrayDivides length divisorWidth valueWidth).Realizable := by
  apply ((flags_realizable length divisorWidth valueWidth).followedBy (arrayAllTrue_realizable length) rfl
    (by intros; trivial)).onResults _ _ _ (by intros; trivial)
  intro name
  rcases name with impossible | choice
  · exact impossible.elim
  · exact Realizable.argument _ choice _

/-- The returned Boolean is exactly universal mathematical divisibility. -/
theorem integerArrayDivides_correct (length divisorWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerArrayDivides length divisorWidth valueWidth).Arguments sizes) :
    (integerArrayDivides length divisorWidth valueWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∀ index, (arguments false index).val ∣ (arguments true index).val := by
  change (List.ofFn (fun index => decide ((arguments false index).val ∣ (arguments true index).val))).all id = true ↔ _
  simp

end Polytime2.Computation
