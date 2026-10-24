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

import Polytime2.Matrices.RemainderSweepController
import Polytime2.TM0.Computation

/-! # Distinct-target Euclidean normalization

Reducing 7 and -4 against the fixed pivot 3 returns remainders 1 and 2.
The same quotient updates are retained in the actual accumulated basis.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.RemainderSweepController

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width length : MvPolynomial Parameter ℕ) :
    (remainderSweepController rows columns width length).TM0Realizable :=
  (remainderSweepController_realizable rows columns width length).tm0

private noncomputable def arguments :
    (remainderSweepController (Parameter := Empty) 3 1 3 2).Arguments Empty.elim
  | .inl false => ⟨2, by norm_num⟩
  | .inl true => ⟨0, by norm_num⟩
  | .inr false =>
    (⟨fun row _ => if row.val = 0 then 7 else if row.val = 1 then -4 else 3, by
      intro row column; dsimp only; split_ifs <;> norm_num⟩,
      ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩)
  | .inr true => fun index => ⟨index.val, by
      have bounded := index.isLt
      norm_num at bounded ⊢
      omega⟩

private theorem targetList : List.ofFn (arguments (.inr true)) =
    [⟨0, by norm_num⟩, ⟨1, by norm_num⟩] := by
  rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ) = 2 by norm_num)]
  norm_num [arguments, List.ofFn]
  rfl

private theorem valid : (remainderSweepController (Parameter := Empty) 3 1 3 2).precondition
    Empty.elim arguments := by
  rw [remainderSweepController_precondition, targetList]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.nodup_nil, List.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true]
    intro same
    have values := congrArg Fin.val same
    norm_num at values
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro same
      have values := congrArg Fin.val same
      norm_num [arguments] at values
    · intro same
      have values := congrArg Fin.val same
      norm_num [arguments] at values
  · norm_num [arguments]
  · intro row column
    dsimp only [arguments]
    split_ifs <;> norm_num
  · intro row column
    simp only [arguments, Matrix.one_apply]
    split_ifs <;> norm_num

private noncomputable def result :=
  (remainderSweepController (Parameter := Empty) 3 1 3 2).compute Empty.elim ⟨arguments, valid⟩

private theorem correct : (result.1.val, result.2.val) = IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
    ⟨2, by norm_num⟩ (⟨0, by norm_num⟩ : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
    [⟨0, by norm_num⟩, ⟨1, by norm_num⟩] (arguments (.inr false)).1.val (arguments (.inr false)).2.val := by
  have computed := remainderSweepController_correct 3 1 3 2 Empty.elim ⟨arguments, valid⟩
  dsimp only at computed
  change (result.1.val, result.2.val) = _ at computed
  exact computed.trans (congrArg (fun targets => IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
    (arguments (.inl false)) (arguments (.inl true)) targets (arguments (.inr false)).1.val
    (arguments (.inr false)).2.val) targetList)

example : result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 3 := by
  have equation := congrArg Prod.fst correct
  change result.1.val = _ at equation
  rw [equation]
  norm_num only [arguments]
  decide +kernel

example : result.2.val ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ = -2 ∧
    result.2.val ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ = 2 := by
  have equation := congrArg Prod.snd correct
  change result.2.val = _ at equation
  rw [equation]
  norm_num [arguments, IntegerMatrix.rowRemainderSweep, IntegerMatrix.rowRemainderWithLeft,
    IntegerMatrix.rowRemainder, IntegerMatrix.rowAdd, Matrix.updateRow_apply, Matrix.one_apply, Fin.ext_iff]

end Polytime2.Examples.RemainderSweepController
