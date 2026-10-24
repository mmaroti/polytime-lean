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

import Polytime2.Arrays.Indices
import Polytime2.Arrays.Transform

/-! # Tabulating arrays from certified mathematical functions

The input is a fixed finite family of mathematical context values. For every
position in a size-dependent finite interval, a certified operation produces one
output element. The result is the ordinary array of those values, including
empty arrays and element domains without default values. Position storage is
prepared internally using the existing prefix-count enumeration.
-/

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- Tabulate an array by its mathematical coordinates and immutable context. -/
noncomputable def arrayTabulate (context : Context → EncodedDomain.{0, 0} Parameter)
    (target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      Fin (MvPolynomial.eval sizes length) → target.Carrier sizes) : Computation Parameter Context where
  inputDomains := context
  outputDomain := target.arrayOfLength length
  precondition _ _ := True
  compute sizes arguments := operation sizes arguments.val

theorem arrayTabulate_realizable (context : Context → EncodedDomain.{0, 0} Parameter)
    (target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      Fin (MvPolynomial.eval sizes length) → target.Carrier sizes)
    (step : (arrayTransformStep context (EncodedDomain.arrayPosition length) target operation).Realizable) :
    (arrayTabulate context target length operation).Realizable := by
  have positions := (arrayPositions_realizable length).withArguments context
    ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)
  have transformed := arrayTransform_realizable context (EncodedDomain.arrayPosition length) target
    length operation step
  exact positions.letThen transformed (by intros; rfl) rfl (by intros; trivial)

end Polytime2.Computation
