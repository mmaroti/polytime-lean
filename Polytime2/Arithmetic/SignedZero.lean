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

import Polytime2.Arithmetic.SignedWidth

/-! # Canonical signed zero at a derived width

Construct zero at any magnitude width, including zero width. Callers reuse
this certificate when zero-filling mathematical vectors and diagonals.
-/

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Construct the canonical signed zero without any input. -/
noncomputable def integerZero (width : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := binaryIntegers width
  precondition _ _ := True
  compute _ _ := ⟨0, by simp⟩

/-- Fixed zero construction and exact narrowing work even at zero magnitude width. -/
theorem integerZero_realizable (width : MvPolynomial Parameter ℕ) :
    (integerZero width).Realizable := by
  have zero := integerBooleanOperationWiden_realizable width (Argument := Empty) (fun _ => ⟨0, by decide⟩)
  have narrowed := zero.followedBy (integerNarrowAtWidths_realizable (width + 1) width
    (by intro sizes; simp only [map_add, map_one]; omega)) rfl (by
      intro sizes arguments valid
      change (0 : ℤ).natAbs < 2 ^ MvPolynomial.eval sizes width
      simp)
  have ready := narrowed.withArguments (Empty.elim : Empty → EncodedDomain Parameter)
    (Function.Embedding.refl Empty) (by intro impossible; exact impossible.elim)
  exact ready.withSpecification (fun _ _ => True) (integerZero width).compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
