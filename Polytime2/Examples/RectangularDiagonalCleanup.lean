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

import Polytime2.Matrices.RectangularDiagonalCleanup
import Polytime2.TM0.Computation

/-! # Full rectangular Smith cleanup with actual output matrices

The 4-by-5 case retains all active transformations and both complementary
identities. Rank-zero cases include either empty full dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.RectangularDiagonalCleanup

open Polytime2.Computation
open Polytime2.IntegerMatrix

variable {Parameter : Type} [Fintype Parameter]

example (rows columns rank width : MvPolynomial Parameter ℕ) :
    (rectangularPositiveDiagonalCleanup rows columns rank width).TM0Realizable :=
  (rectangularPositiveDiagonalCleanup_realizable rows columns rank width).tm0

private def diagonalValue (index : ℕ) : ℕ := if index = 0 then 6 else if index = 1 then 10 else 15

private noncomputable def arguments :
    (rectangularPositiveDiagonalCleanup (Parameter := Empty) 4 5 3 4).Arguments Empty.elim :=
  fun _ index => ⟨diagonalValue index.val, by dsimp only [diagonalValue]; split_ifs <;> norm_num⟩

private theorem arguments_valid :
    (rectangularPositiveDiagonalCleanup (Parameter := Empty) 4 5 3 4).precondition Empty.elim arguments := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro index
  dsimp only [arguments, diagonalValue]
  split_ifs <;> norm_num

private theorem matrixEntries (rows columns rank : ℕ) (sameRows : rows = 4) (sameColumns : columns = 5) (sameRank : rank = 3) :
    let result := rectangularDiagonalCleanup rows columns (by omega) (by omega) 4
      (fun index : Fin rank => diagonalValue index.val)
    (result.1 ⟨0, by omega⟩ ⟨0, by omega⟩, result.1 ⟨1, by omega⟩ ⟨1, by omega⟩,
      result.1 ⟨2, by omega⟩ ⟨2, by omega⟩, result.1 ⟨3, by omega⟩ ⟨3, by omega⟩,
      result.2.1 ⟨3, by omega⟩ ⟨3, by omega⟩, result.2.2 ⟨4, by omega⟩ ⟨4, by omega⟩,
      result.2.1 ⟨0, by omega⟩ ⟨0, by omega⟩, result.2.2 ⟨0, by omega⟩ ⟨1, by omega⟩) =
      (1, 30, 30, 0, 1, 1, 16, 95) := by
  subst rows columns rank
  change @Eq (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) _ (1, 30, 30, 0, 1, 1, 16, 95)
  simp only [Prod.mk.injEq]
  repeat' constructor
  all_goals decide +kernel

example :
    let result := (rectangularPositiveDiagonalCleanup (Parameter := Empty) 4 5 3 4).compute Empty.elim
      ⟨arguments, arguments_valid⟩
    (result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩, result.1.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩,
      result.1.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩, result.1.val ⟨3, by norm_num⟩ ⟨3, by norm_num⟩,
      result.2.1.val ⟨3, by norm_num⟩ ⟨3, by norm_num⟩, result.2.2.val ⟨4, by norm_num⟩ ⟨4, by norm_num⟩,
      result.2.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩, result.2.2.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) =
      (1, 30, 30, 0, 1, 1, 16, 95) := by
  have correct := rectangularPositiveDiagonalCleanup_correct (Parameter := Empty) 4 5 3 4 Empty.elim ⟨arguments, arguments_valid⟩
  have entries := congrArg (fun result =>
    (result.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩, result.1 ⟨1, by norm_num⟩ ⟨1, by norm_num⟩,
      result.1 ⟨2, by norm_num⟩ ⟨2, by norm_num⟩, result.1 ⟨3, by norm_num⟩ ⟨3, by norm_num⟩,
      result.2.1 ⟨3, by norm_num⟩ ⟨3, by norm_num⟩, result.2.2 ⟨4, by norm_num⟩ ⟨4, by norm_num⟩,
      result.2.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩, result.2.2 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)) correct
  apply entries.trans
  simpa only [arguments, map_ofNat] using matrixEntries
    (MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ))
    (MvPolynomial.eval Empty.elim (5 : MvPolynomial Empty ℕ))
    (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)) (by norm_num) (by norm_num) (by norm_num)

example :
    let result := (rectangularPositiveDiagonalCleanup (Parameter := Empty) 4 5 3 4).compute Empty.elim
      ⟨arguments, arguments_valid⟩
    IsSmithForm (rectangularDiagonal (MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ))
      (MvPolynomial.eval Empty.elim (5 : MvPolynomial Empty ℕ)) (fun index : Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)) => diagonalValue index.val))
      result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)) :=
  rectangularPositiveDiagonalCleanup_isSmithForm 4 5 3 4 Empty.elim ⟨arguments, arguments_valid⟩

private noncomputable def emptyArguments :
    (rectangularPositiveDiagonalCleanup (Parameter := Empty) 0 4 0 0).Arguments Empty.elim :=
  fun _ index => by have bound := index.isLt; norm_num at bound

private theorem empty_valid (rows columns : MvPolynomial Empty ℕ) :
    (rectangularPositiveDiagonalCleanup rows columns 0 0).precondition Empty.elim emptyArguments := by
  refine ⟨?_, by simp, by simp⟩
  intro index
  have bound := index.isLt
  norm_num at bound

example :
    let result := (rectangularPositiveDiagonalCleanup (Parameter := Empty) 0 4 0 0).compute Empty.elim
      ⟨emptyArguments, empty_valid 0 4⟩
    IsSmithForm (rectangularDiagonal (MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ))
      (MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ)) (fun index => (emptyArguments () index).val))
      result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ)) :=
  rectangularPositiveDiagonalCleanup_isSmithForm 0 4 0 0 Empty.elim ⟨emptyArguments, empty_valid 0 4⟩

example :
    let result := (rectangularPositiveDiagonalCleanup (Parameter := Empty) 4 0 0 0).compute Empty.elim
      ⟨emptyArguments, empty_valid 4 0⟩
    IsSmithForm (rectangularDiagonal (MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ))
      (MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ)) (fun index => (emptyArguments () index).val))
      result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ)) :=
  rectangularPositiveDiagonalCleanup_isSmithForm 4 0 0 0 Empty.elim ⟨emptyArguments, empty_valid 4 0⟩

end Polytime2.Examples.RectangularDiagonalCleanup
