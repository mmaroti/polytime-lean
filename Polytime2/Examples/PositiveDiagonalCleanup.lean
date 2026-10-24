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

import Polytime2.Matrices.PositiveDiagonalCleanup
import Polytime2.TM0.Computation

/-! # Positive diagonal cleanup without controller capacities

Only the diagonal and its mathematical bit width are supplied. Preparation
constructs both identities and all workspace. Repeated repairs retain the
expected diagonal and actual bases; empty and zero-width inputs are covered.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.PositiveDiagonalCleanup

open Polytime2.Computation
open Polytime2.IntegerMatrix

variable {Parameter : Type} [Fintype Parameter]

example (length width : MvPolynomial Parameter ℕ) : (positiveDiagonalCleanup length width).TM0Realizable :=
  (positiveDiagonalCleanup_realizable length width).tm0

private def diagonalValue (index : ℕ) : ℕ := if index = 0 then 6 else if index = 1 then 10 else 15

private noncomputable def arguments : (positiveDiagonalCleanup (Parameter := Empty) 3 4).Arguments Empty.elim :=
  fun _ index => ⟨diagonalValue index.val, by dsimp only [diagonalValue]; split_ifs <;> norm_num⟩

private theorem arguments_valid :
    (positiveDiagonalCleanup (Parameter := Empty) 3 4).precondition Empty.elim arguments := by
  intro index
  dsimp only [arguments, diagonalValue]
  split_ifs <;> norm_num

private theorem normalizedDiagonal (dimension : ℕ) (same : dimension = 3) :
    diagonalCleanup 37 (fun index : Fin dimension => diagonalValue index.val) =
      (fun index => if index.val = 0 then 1 else 30) := by
  subst dimension
  funext index
  fin_cases index <;> decide +kernel

example :
    let result := (positiveDiagonalCleanup (Parameter := Empty) 3 4).compute Empty.elim ⟨arguments, arguments_valid⟩
    (fun index => (result.1 index).val) = (fun index => if index.val = 0 then 1 else 30) := by
  have computed := positiveDiagonalCleanup_correct (Parameter := Empty) 3 4 Empty.elim ⟨arguments, arguments_valid⟩
  norm_num only [map_ofNat] at computed
  have diagonal := congrArg Prod.fst computed
  exact diagonal.trans ((diagonalCleanupWithBases_diagonal _ _ _ _).trans
    (by simpa only [arguments, map_ofNat] using
      normalizedDiagonal (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)) (by norm_num)))

private theorem normalizedBasisEntries (dimension : ℕ) (same : dimension = 3) :
    let result := diagonalCleanupWithBases 37 (fun index : Fin dimension => diagonalValue index.val) 1 1
    result.2.1 ⟨0, by omega⟩ ⟨0, by omega⟩ = 16 ∧
      result.2.2 ⟨0, by omega⟩ ⟨1, by omega⟩ = 95 := by
  subst dimension
  decide +kernel

example :
    let result := (positiveDiagonalCleanup (Parameter := Empty) 3 4).compute Empty.elim ⟨arguments, arguments_valid⟩
    (result.2.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩,
      result.2.2.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩) = (16, 95) := by
  have computed := positiveDiagonalCleanup_correct (Parameter := Empty) 3 4 Empty.elim ⟨arguments, arguments_valid⟩
  norm_num only [map_ofNat] at computed
  have bases := congrArg Prod.snd computed
  have entries := congrArg (fun bases => (bases.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩,
    bases.2 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)) bases
  have expected := normalizedBasisEntries _ (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)
  apply entries.trans
  simpa only [arguments, map_ofNat] using Prod.ext expected.1 expected.2

example :
    let result := (positiveDiagonalCleanup (Parameter := Empty) 3 4).compute Empty.elim ⟨arguments, arguments_valid⟩
    IsSmithForm (Matrix.diagonal (fun index => ((diagonalValue index.val : ℕ) : ℤ)))
      (Matrix.diagonal (fun index => ((result.1 index).val : ℤ))) result.2.1.val result.2.2.val
      (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)) :=
  positiveDiagonalCleanup_isSmithForm 3 4 Empty.elim ⟨arguments, arguments_valid⟩

example (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (positiveDiagonalCleanup 0 width).Arguments sizes) :
    (positiveDiagonalCleanup 0 width).precondition sizes arguments := by
  intro index
  have bound := index.isLt
  norm_num at bound

example (arguments : (positiveDiagonalCleanup (Parameter := Empty) 1 0).Arguments Empty.elim) :
    ¬(positiveDiagonalCleanup (Parameter := Empty) 1 0).precondition Empty.elim arguments := by
  intro valid
  have positive := valid ⟨0, by norm_num⟩
  have bound := (arguments () ⟨0, by norm_num⟩).isLt
  change (arguments () ⟨0, by norm_num⟩).val < 2 ^ MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ) at bound
  have tooSmall : (arguments () ⟨0, by norm_num⟩).val < 1 := by simpa only [map_zero, pow_zero] using bound
  exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt positive)) tooSmall

end Polytime2.Examples.PositiveDiagonalCleanup
