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

import Polytime2.Matrices.IntegerNarrow
import Polytime2.Matrices.IntegerOperations

/-! # Resizing integer matrices without ordering the two widths

Use the existing target-bound computation for either narrowing or widening.
A common intermediate width is the sum of the source and target widths. Thus
all resizing is composed from existing widening and narrowing certificates.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Resize to any target width when every entry fits, with no width-order premise. -/
theorem integerMatrixResize_realizable (rows columns sourceWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixNarrow rows columns sourceWidth targetWidth).Realizable := by
  let computation := integerMatrixNarrow rows columns sourceWidth targetWidth
  have padded := (integerMatrixWiden_realizable rows columns sourceWidth targetWidth
    (sourceWidth + targetWidth) rfl).withPrecondition computation.precondition (by intros; trivial)
  have resized := padded.followedBy
    (integerMatrixNarrow_realizable rows columns (sourceWidth + targetWidth) targetWidth
      (by intro sizes; simp only [map_add]; omega)) rfl (by
        intro sizes arguments valid
        exact valid)
  apply resized.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Subtype.ext
  rfl

end Polytime2.Computation
