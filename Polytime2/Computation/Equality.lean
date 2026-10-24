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

import Polytime2.Arithmetic.BitComparison

/-! # Equality of canonically encoded mathematical elements

Equality is decided by the existing word comparison. Canonical encoding is
injective, so the Boolean result is exactly mathematical equality, for every
size-dependent domain, including domains with zero-width encodings.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Compare two mathematical elements without exposing their representation. -/
noncomputable def elementsEqual (domain : EncodedDomain.{0, 0} Parameter) : Computation Parameter Bool := by
  classical
  exact {
    inputDomains := fun _ => domain
    outputDomain := EncodedDomain.booleans
    precondition := fun _ _ => True
    compute := fun _ arguments => decide (arguments.val false = arguments.val true) }

theorem elementsEqual_realizable (domain : EncodedDomain.{0, 0} Parameter) :
    (elementsEqual domain).Realizable := by
  classical
  have compared := (bitsEqual_realizable domain.widthPolynomial).reinterpretInputs
    (elementsEqual domain).inputDomains (fun _ => domain.encode)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  apply compared.withSpecification (fun _ _ => True) (elementsEqual domain).compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [Computation.reinterpretInputs, bitsEqual, elementsEqual, decide_eq_true_eq]
  exact (domain.encode_injective sizes).eq_iff

end Polytime2.Computation
