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

import Polytime2.Matrices.IntegerRectangularHermiteStoredRank
import Polytime2.TM0.Computation

/-! # Full rectangular Hermite runtime

The active square result is lifted with two full identity-extended bases.
Both diagonal reading and the complete rectangular operation have standalone
machine certificates. Rank zero is admitted for arbitrary outer dimensions.
-/

namespace Polytime2.Examples.IntegerRectangularHermite

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rank width : MvPolynomial Parameter ℕ) :
    (integerMatrixDiagonalMagnitudes rank width).TM0Realizable :=
  (integerMatrixDiagonalMagnitudes_realizable rank width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermite rows columns rank width).TM0Realizable :=
  (integerRectangularHermite_realizable rows columns rank width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerRectangularHermite rows columns 0 width).Arguments sizes) :
    (integerRectangularHermite rows columns 0 width).precondition sizes arguments := by
  refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
  · intro row column before
    have impossible := row.isLt
    simp at impossible
  · intro index
    have impossible := index.isLt
    simp at impossible

example {Parameter : Type} [Fintype Parameter] (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermiteAtRank rows columns rank width).TM0Realizable :=
  (integerRectangularHermiteAtRank_realizable rows columns rank width).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerRectangularHermiteAtSize rows columns width names rankName).TM0Realizable :=
  (integerRectangularHermiteAtSize_realizable rows columns width names rankName).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) (rankName : Parameter)
    (sizes : Parameter → ℕ) (zeroRank : sizes rankName = 0)
    (arguments : (integerRectangularHermiteAtSize rows columns width names rankName).Arguments sizes) :
    (integerRectangularHermiteAtSize rows columns width names rankName).precondition sizes arguments := by
  apply integerRectangularHermiteAtSize_permitted rows columns width names rankName sizes arguments
    (by simp [zeroRank]) (by simp [zeroRank])
  · intro row column before
    have impossible := row.isLt
    simp [zeroRank] at impossible
  · intro index
    have impossible := index.isLt
    simp [zeroRank] at impossible

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermiteHost rows columns width).TM0Realizable :=
  (integerRectangularHermiteHost_realizable rows columns width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerRectangularHermiteHost rows columns width).Arguments sizes)
    (zeroRank : (arguments ()).1.val = 0) :
    (integerRectangularHermiteHost rows columns width).precondition sizes arguments := by
  apply integerRectangularHermiteHost_permitted rows columns width sizes arguments
    (by simp [zeroRank]) (by simp [zeroRank])
  · intro row column before
    have impossible := row.isLt
    simp [zeroRank] at impossible
  · intro index
    have impossible := index.isLt
    simp [zeroRank] at impossible

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteHost rows columns width).Arguments sizes //
      (integerRectangularHermiteHost rows columns width).precondition sizes arguments})
    (zeroMatrix : (arguments.val ()).2.val = 0) :
    ((integerRectangularHermiteHost rows columns width).compute sizes arguments).1.val = 0 := by
  have preserved := integerRectangularHermiteHost_preserves rows columns width sizes arguments
    (by intro row after; funext column; rw [zeroMatrix]; rfl)
    (by intro column after; funext row; change (arguments.val ()).2.val row column = 0; rw [zeroMatrix]; rfl)
  have equation := preserved.1
  rw [zeroMatrix, Matrix.mul_zero, Matrix.zero_mul] at equation
  exact equation.symm

end Polytime2.Examples.IntegerRectangularHermite
