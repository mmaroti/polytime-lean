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

import Polytime2.Matrices.IntegerRectangularCleanupStoredRank
import Polytime2.TM0.Computation

/-! # Full-matrix divisibility cleanup

The cleanup reads its active entries from an ordinary rectangular diagonal.
Both width interfaces have standalone machine certificates. Rank zero accepts
the zero matrix for arbitrary outer dimensions, including empty dimensions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerRectangularCleanup

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanup rows columns rank width).TM0Realizable :=
  (integerRectangularCleanup_realizable rows columns rank width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanupAtRank rows columns rank width).TM0Realizable :=
  (integerRectangularCleanupAtRank_realizable rows columns rank width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerRectangularCleanup rows columns 0 width).Arguments sizes)
    (zeroMatrix : (arguments ()).val = 0) :
    (integerRectangularCleanup rows columns 0 width).precondition sizes arguments := by
  apply integerRectangularCleanup_permitted rows columns 0 width sizes arguments
    (by simp) (by simp) (fun _ => 0)
  · intro index
    have impossible := index.isLt
    simp at impossible
  · rw [zeroMatrix]
    ext row column
    simp [Polytime2.IntegerMatrix.rectangularDiagonal]

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerRectangularCleanupAtSize rows columns width names rankName).TM0Realizable :=
  (integerRectangularCleanupAtSize_realizable rows columns width names rankName).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (rankZero : sizes rankName = 0)
    (arguments : (integerRectangularCleanupAtSize rows columns width names rankName).Arguments sizes)
    (zeroMatrix : (arguments ()).val = 0) :
    (integerRectangularCleanupAtSize rows columns width names rankName).precondition sizes arguments := by
  apply integerRectangularCleanupAtSize_permitted rows columns width names rankName sizes arguments
    (by omega) (by omega) (fun _ => 0)
  · intro index
    have impossible := index.isLt
    omega
  · rw [zeroMatrix]
    ext row column
    simp [Polytime2.IntegerMatrix.rectangularDiagonal, rankZero]

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanupHost rows columns width).TM0Realizable :=
  (integerRectangularCleanupHost_realizable rows columns width).tm0

end Polytime2.Examples.IntegerRectangularCleanup
