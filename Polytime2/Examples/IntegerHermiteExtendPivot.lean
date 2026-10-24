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

import Polytime2.Matrices.IntegerHermiteExtendPivot
import Polytime2.TM0.Computation

/-! # Extending a Hermite block with a negative pivot

Normalize the new pivot -3 to 3, then reduce the old entries 7 and -4 to 1 and 2.
The returned basis retains both the sign change and the quotient updates.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteExtendPivot

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteExtendPivot rows columns width length).TM0Realizable :=
  (integerHermiteExtendPivot_realizable rows columns width length).tm0

private noncomputable def arguments :
    (integerHermiteExtendPivot (Parameter := Empty) 3 1 3 2).Arguments Empty.elim
  | 0 => ⟨2, by norm_num⟩
  | 1 => ⟨0, by norm_num⟩
  | 2 => ⟨fun row _ => if row.val = 0 then 7 else if row.val = 1 then -4 else -3, by
      intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 3 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩
  | 4 => fun index => ⟨index.val, by
      have bounded := index.isLt
      norm_num at bounded ⊢
      omega⟩

private theorem targetList : List.ofFn (arguments 4) = [⟨0, by norm_num⟩, ⟨1, by norm_num⟩] := by
  rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ) = 2 by norm_num)]
  norm_num [arguments, List.ofFn]
  rfl

private theorem valid : (integerHermiteExtendPivot (Parameter := Empty) 3 1 3 2).precondition
    Empty.elim arguments := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values
  · intro member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    have values := congrArg Fin.val same
    have bounded := index.isLt
    norm_num [arguments] at values bounded
    omega
  · norm_num [arguments]

private noncomputable def result :=
  (integerHermiteExtendPivot (Parameter := Empty) 3 1 3 2).compute Empty.elim ⟨arguments, valid⟩

private theorem correct : (result.1.val, result.2.val) = IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
    (arguments 0) (arguments 1) [⟨0, by norm_num⟩, ⟨1, by norm_num⟩]
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
      (arguments 0) (arguments 1) (arguments 2).val (arguments 3).val).1
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
      (arguments 0) (arguments 1) (arguments 2).val (arguments 3).val).2 := by
  have actual := integerHermiteExtendPivot_correct 3 1 3 2 Empty.elim ⟨arguments, valid⟩
  dsimp only at actual
  exact actual.trans (congrArg (fun targets => IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))) (arguments 0) (arguments 1) targets
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
      (arguments 0) (arguments 1) (arguments 2).val (arguments 3).val).1
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
      (Column := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
      (arguments 0) (arguments 1) (arguments 2).val (arguments 3).val).2) targetList)

example : result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 3 := by
  have equation := congrArg Prod.fst correct
  change result.1.val = _ at equation
  rw [equation]
  norm_num [arguments, IntegerMatrix.rowRemainderSweep, IntegerMatrix.rowRemainderWithLeft,
    IntegerMatrix.rowRemainder, IntegerMatrix.rowAdd, IntegerMatrix.positivePivotWithLeft,
    IntegerMatrix.rowNegate_apply, Matrix.updateRow_apply, Fin.ext_iff]

example : result.2.val ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ = 2 ∧
    result.2.val ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ = -2 ∧
    result.2.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = -1 := by
  have equation := congrArg Prod.snd correct
  change result.2.val = _ at equation
  rw [equation]
  norm_num [arguments, IntegerMatrix.rowRemainderSweep, IntegerMatrix.rowRemainderWithLeft,
    IntegerMatrix.rowRemainder, IntegerMatrix.rowAdd, IntegerMatrix.positivePivotWithLeft,
    IntegerMatrix.rowNegate_apply, Matrix.updateRow_apply, Matrix.one_apply, Fin.ext_iff]

end Polytime2.Examples.IntegerHermiteExtendPivot
