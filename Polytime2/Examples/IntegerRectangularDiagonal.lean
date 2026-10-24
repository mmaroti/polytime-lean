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

import Polytime2.Matrices.IntegerRectangularDiagonal
import Polytime2.TM0.Computation

/-! # Certified rectangular diagonal construction

Independent full dimensions include inactive zero rows and columns. Rank zero
and empty dimensions use the same constructor. Coordinate guards and derived
size words have standalone machine certificates.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerRectangularDiagonal

open Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

example (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularDiagonal rows columns rank width).TM0Realizable :=
  (integerRectangularDiagonal_realizable rows columns rank width).tm0

example (length : MvPolynomial Parameter ℕ) : (polynomialIntegerSize length).TM0Realizable :=
  (polynomialIntegerSize_realizable length).tm0

example (length bound : MvPolynomial Parameter ℕ) : (positionWithin length bound).TM0Realizable :=
  (positionWithin_realizable length bound).tm0

example (first second : MvPolynomial Parameter ℕ) : (positionsEqual first second).TM0Realizable :=
  (positionsEqual_realizable first second).tm0

private noncomputable def arguments : (integerRectangularDiagonal (Parameter := Empty) 4 5 3 5).Arguments Empty.elim :=
  fun _ index => if index.val = 0 then ⟨1, by norm_num⟩ else ⟨30, by norm_num⟩

example :
    let result := (integerRectangularDiagonal (Parameter := Empty) 4 5 3 5).compute Empty.elim ⟨arguments, trivial⟩
    result.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1 ∧
      result.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = 30 ∧
      result.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 30 ∧
      result.val ⟨3, by norm_num⟩ ⟨3, by norm_num⟩ = 0 ∧
      result.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 0 ∧
      result.val ⟨0, by norm_num⟩ ⟨4, by norm_num⟩ = 0 := by
  dsimp only
  rw [integerRectangularDiagonal_correct]
  norm_num [Polytime2.IntegerMatrix.rectangularDiagonal, arguments]

example :
    ((integerRectangularDiagonal (Parameter := Empty) 3 2 0 0).compute Empty.elim
      ⟨(fun _ index => by have bound := index.isLt; norm_num at bound), trivial⟩).val = 0 := by
  rw [integerRectangularDiagonal_correct]
  ext row column
  simp [Polytime2.IntegerMatrix.rectangularDiagonal]

example (columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularDiagonal 0 columns 0 width).Arguments sizes) :
    ((integerRectangularDiagonal 0 columns 0 width).compute sizes ⟨arguments, trivial⟩).val = 0 := by
  ext row column
  have bound := row.isLt
  norm_num at bound

example : ((polynomialIntegerSize (Parameter := Empty) 0).compute Empty.elim
    ⟨(fun impossible => impossible.elim), trivial⟩).val = 0 := by
  change ((MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ) : ℕ) : ℤ) = 0
  norm_num

example : (positionWithin (Parameter := Empty) 4 3).compute Empty.elim
    ⟨(fun _ => ⟨3, by norm_num⟩), trivial⟩ = false := by
  change @Eq Bool (decide ((3 : ℕ) < MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))) false
  norm_num

example : (positionsEqual (Parameter := Empty) 4 5).compute Empty.elim
    ⟨(fun choice => match choice with
      | false => ⟨2, by norm_num⟩
      | true => ⟨2, by norm_num⟩), trivial⟩ = true := by
  change @Eq Bool (decide ((2 : ℕ) = 2)) true
  decide

end Polytime2.Examples.IntegerRectangularDiagonal
