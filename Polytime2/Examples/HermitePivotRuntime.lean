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

import Polytime2.Matrices.IntegerResidualPivot
import Polytime2.Matrices.IntegerPositivePivot
import Polytime2.TM0.Computation

/-! # Runtime residual selection and pivot sign normalization

Search skips leading zeros and accepts a negative nonzero entry. A zero row
and an empty column dimension return none. Sign normalization tracks a
nonidentity basis and retains positive and zero entries unchanged.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.HermitePivotRuntime

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerResidualPivot rows columns width).TM0Realizable :=
  (integerResidualPivot_realizable rows columns width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerPositivePivotWithLeft rows columns width).TM0Realizable :=
  (integerPositivePivotWithLeft_realizable rows columns width).tm0

private noncomputable def residualArguments (source : ℕ) (bounded : source < 2) :
    (integerResidualPivot (Parameter := Empty) 2 3 3).Arguments Empty.elim
  | false => ⟨source, by simpa using bounded⟩
  | true => ⟨fun row column => if row.val = 0 then 0 else if column.val = 0 then 0
      else if column.val = 1 then -5 else 7, by
        intro row column; dsimp only; split_ifs <;> norm_num⟩

example : (integerResidualPivot (Parameter := Empty) 2 3 3).compute Empty.elim
    ⟨residualArguments 1 (by decide), trivial⟩ = some ⟨1, by norm_num⟩ := by
  rw [integerResidualPivot_correct]
  apply (ArraySearch.firstFalse_some_iff _ _).mpr
  norm_num [residualArguments, List.ofFn]
  decide +kernel

example : (integerResidualPivot (Parameter := Empty) 2 3 3).compute Empty.elim
    ⟨residualArguments 0 (by decide), trivial⟩ = none := by
  apply (integerResidualPivot_none _ _ _ _ _).mpr
  funext column
  rfl

private noncomputable def emptyArguments : (integerResidualPivot (Parameter := Empty) 1 0 0).Arguments Empty.elim
  | false => ⟨0, by norm_num⟩
  | true => ⟨0, by intros; simp⟩

example : (integerResidualPivot (Parameter := Empty) 1 0 0).compute Empty.elim ⟨emptyArguments, trivial⟩ = none := by
  apply (integerResidualPivot_none _ _ _ _ _).mpr
  rfl

private noncomputable def signArguments (entry : ℤ) (bounded : entry.natAbs < 8) :
    (integerPositivePivotWithLeft (Parameter := Empty) 2 2 3).Arguments Empty.elim
  | 0 => ⟨1, by norm_num⟩
  | 1 => ⟨0, by norm_num⟩
  | 2 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 1 else 2)
      else (if column.val = 0 then entry else 4), by
        intro row column
        dsimp only
        split_ifs <;> norm_num
        exact bounded⟩
  | 3 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 1 else 0)
      else (if column.val = 0 then 2 else 1), by
        intro row column; dsimp only; split_ifs <;> norm_num⟩

example :
    let result := (integerPositivePivotWithLeft (Parameter := Empty) 2 2 3).compute Empty.elim
      ⟨signArguments (-6) (by norm_num), trivial⟩
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 6 ∧
      result.2.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = -2 := by
  have entry := integerPositivePivotWithLeft_entry (Parameter := Empty) 2 2 3 Empty.elim
    ⟨signArguments (-6) (by norm_num), trivial⟩
  have raw := integerPositivePivotWithLeft_correct (Parameter := Empty) 2 2 3 Empty.elim
    ⟨signArguments (-6) (by norm_num), trivial⟩
  constructor
  · convert entry using 1 <;> norm_num [signArguments]
  · have basis := congrArg Prod.snd raw
    change ((integerPositivePivotWithLeft (Parameter := Empty) 2 2 3).compute Empty.elim
      ⟨signArguments (-6) (by norm_num), trivial⟩).2.val _ _ = -2
    dsimp only at basis
    have selected := congrFun (congrFun basis ⟨1, by norm_num⟩) ⟨0, by norm_num⟩
    refine selected.trans ?_
    norm_num [signArguments, Polytime2.IntegerMatrix.positivePivotWithLeft, Polytime2.IntegerMatrix.rowNegate_apply]

example : ((integerPositivePivotWithLeft (Parameter := Empty) 2 2 3).compute Empty.elim
    ⟨signArguments 6 (by norm_num), trivial⟩).2.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 := by decide +kernel

example : ((integerPositivePivotWithLeft (Parameter := Empty) 2 2 3).compute Empty.elim
    ⟨signArguments 0 (by norm_num), trivial⟩).2.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 := by decide +kernel

example {Parameter : Type} [Fintype Parameter] (length : MvPolynomial Parameter ℕ) :
    (arraySearchIsNone length).TM0Realizable := (arraySearchIsNone_realizable length).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerResidualRowIsZero rows columns width).TM0Realizable :=
  (integerResidualRowIsZero_realizable rows columns width).tm0

example : (arraySearchIsNone (Parameter := Empty) 0).compute Empty.elim
    ⟨(fun _ => none), trivial⟩ = true := rfl

example : (arraySearchIsNone (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun _ => some ⟨1, by norm_num⟩), trivial⟩ = false := rfl

example : (integerResidualRowIsZero (Parameter := Empty) 2 3 3).compute Empty.elim
    ⟨residualArguments 0 (by decide), trivial⟩ = true := by
  apply (integerResidualRowIsZero_correct 2 3 3 Empty.elim ⟨residualArguments 0 (by decide), trivial⟩).mpr
  funext column
  rfl

example : (integerResidualRowIsZero (Parameter := Empty) 2 3 3).compute Empty.elim
    ⟨residualArguments 1 (by decide), trivial⟩ = false := by
  cases tested : (integerResidualRowIsZero (Parameter := Empty) 2 3 3).compute Empty.elim
      ⟨residualArguments 1 (by decide), trivial⟩ with
  | false => rfl
  | true =>
    have zero := (integerResidualRowIsZero_correct 2 3 3 Empty.elim
      ⟨residualArguments 1 (by decide), trivial⟩).mp tested
    have entry := congrFun zero ⟨1, by norm_num⟩
    norm_num [residualArguments] at entry

end Polytime2.Examples.HermitePivotRuntime
