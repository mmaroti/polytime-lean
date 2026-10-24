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

import Polytime2.Matrices.IntegerHermiteIncoming
import Polytime2.TM0.Computation

/-! # Original-width incoming-row reduction

The caller supplies width-three matrices for the gcd example. The traversal
prepares its larger workspace internally and returns the same mathematical
result as the incoming prefix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteIncoming

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (integerHermiteIncoming rows columns width pivots).TM0Realizable :=
  (integerHermiteIncoming_realizable rows columns width pivots).tm0

private noncomputable def arguments :
    (integerHermiteIncoming (Parameter := Empty) 2 1 3 1).Arguments Empty.elim
  | 0 => fun index => ⟨index.val, by simpa using index.isLt⟩
  | 1 => id
  | 2 => ⟨fun row _ => if row.val = 0 then 6 else 2, by
      intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 3 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem valid : (integerHermiteIncoming (Parameter := Empty) 2 1 3 1).precondition
    Empty.elim arguments := by
  refine ⟨?_, Function.injective_id, ?_, ?_⟩
  · intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values
  · intro index
    have zero : index.val = 0 := by have bounded := index.isLt; norm_num at bounded; omega
    norm_num [arguments, successorValues, zero]
  · intro row column before
    have rowBound := row.isLt
    have columnBound := column.isLt
    norm_num at rowBound columnBound
    exact False.elim (by omega)

private noncomputable def result :=
  (integerHermiteIncoming (Parameter := Empty) 2 1 3 1).compute Empty.elim ⟨arguments, valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  have correct := integerHermiteIncoming_correct 2 1 3 1 Empty.elim ⟨arguments, valid⟩
  let selectedRows : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ) + 1) ↪
      Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)) :=
    ⟨successorValues 1 Empty.elim (arguments 0), valid.1⟩
  have first := congrArg Prod.fst correct
  change result.1.val = _ at first
  have advanced := IntegerMatrix.hermiteIncomingPrefix_succ_forward
    (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    (Column := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ))) selectedRows (arguments 1)
    (⟨0, by norm_num⟩ : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
    (arguments 2).val (arguments 3).val
  norm_num at first
  have final := first.trans (congrArg Prod.fst advanced)
  rw [final]
  dsimp only [selectedRows, successorValues]
  norm_num only [arguments, map_one, map_ofNat, Fin.last, Fin.val_cast]
  decide +kernel

example : 0 < result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  have entries := integerHermiteIncoming_entries 2 1 3 1 Empty.elim ⟨arguments, valid⟩ ⟨0, by norm_num⟩
  dsimp only [successorValues] at entries
  norm_num only [arguments, map_one, Fin.last, Fin.val_cast] at entries
  exact entries

end Polytime2.Examples.IntegerHermiteIncoming
