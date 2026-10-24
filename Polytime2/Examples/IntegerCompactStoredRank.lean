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

import Polytime2.Matrices.IntegerCompactHermiteInitial
import Polytime2.TM0.Computation

/-! # Standalone machine certification for compact Hermite passes

The caller supplies pivot metadata and three matrices. No rank parameter or
additional precondition is required, including when the stored rank is zero.
-/

namespace Polytime2.Examples.IntegerCompactStoredRank

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerCompactHost rows columns matrixWidth leftWidth rightWidth).TM0Realizable :=
  (integerCompactHost_realizable rows columns matrixWidth leftWidth rightWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerCompactHost rows columns matrixWidth leftWidth rightWidth).Arguments sizes) :
    (integerCompactHost rows columns matrixWidth leftWidth rightWidth).precondition sizes arguments := trivial

example {Parameter : Type} [Fintype Parameter]
    (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteRows rows columns width).TM0Realizable :=
  (integerCompactHermiteRows_realizable rows columns width).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteColumns rows columns width).TM0Realizable :=
  (integerCompactHermiteColumns_realizable rows columns width).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteInitial rows columns width).TM0Realizable :=
  (integerCompactHermiteInitial_realizable rows columns width).tm0

end Polytime2.Examples.IntegerCompactStoredRank
