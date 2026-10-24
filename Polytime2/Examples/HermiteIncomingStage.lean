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

import Polytime2.Matrices.HermiteIncomingWorkspace
import Polytime2.TM0.Computation

/-! # Runtime incoming-row stages

The first pivot has an empty normalization prefix. It still clears the incoming
entry by a gcd update and retains the actual unimodular basis.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.HermiteIncomingStage

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingStage rows columns width pivots).TM0Realizable :=
  (hermiteIncomingStage_realizable rows columns width pivots).tm0

private noncomputable def arguments :
    (hermiteIncomingStage (Parameter := Empty) 2 1 3 1).Arguments Empty.elim
  | 0 => fun index => ⟨index.val, by simpa using index.isLt⟩
  | 1 => fun _ => ⟨0, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨fun row _ => if row.val = 0 then 6 else 2, by
      intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 4 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private noncomputable def selectedRows : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ) + 1) ↪
    Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)) where
  toFun index := ⟨index.val, by
    have bounded := index.isLt
    norm_num at bounded ⊢
    exact bounded⟩
  inj' := by
    intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values

private theorem selected : successorValues 1 Empty.elim (arguments 0) = selectedRows := by
  funext index
  rfl

private theorem valid : (hermiteIncomingStage (Parameter := Empty) 2 1 3 1).precondition
    Empty.elim arguments := by
  apply hermiteIncomingStage_permitted 2 1 3 1 Empty.elim arguments selectedRows selected
  norm_num [arguments, selectedRows]

private noncomputable def result :=
  (hermiteIncomingStage (Parameter := Empty) 2 1 3 1).compute Empty.elim ⟨arguments, valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  have correct := hermiteIncomingStage_correct 2 1 3 1 Empty.elim ⟨arguments, valid⟩
  have first := congrArg Prod.fst correct
  change result.1.val = _ at first
  rw [first]
  dsimp only [hermiteIncomingCoordinates]
  norm_num only [arguments, successorValues, Fin.last, map_ofNat, map_one, Fin.val_cast]
  decide +kernel

example : (result.1.val, result.2.val) = IntegerMatrix.hermiteIncomingPrefix selectedRows
    (arguments 1) 1 (arguments 3).val (arguments 4).val :=
  hermiteIncomingStage_prefix 2 1 3 1 Empty.elim ⟨arguments, valid⟩ selectedRows selected
    (arguments 3).val (arguments 4).val rfl

private theorem withinValid : (hermiteIncomingStageWithin (Parameter := Empty) 2 1 3 1).precondition
    Empty.elim arguments := by
  refine ⟨valid, ?_⟩
  change (∀ row column, (result.1.val row column).natAbs < 2 ^ MvPolynomial.eval Empty.elim 3) ∧
    (∀ row column, (result.2.val row column).natAbs < 2 ^ MvPolynomial.eval Empty.elim 3)
  have correct := hermiteIncomingStage_correct 2 1 3 1 Empty.elim ⟨arguments, valid⟩
  have first := congrArg Prod.fst correct
  have second := congrArg Prod.snd correct
  change result.1.val = _ at first
  change result.2.val = _ at second
  rw [first, second]
  dsimp only [hermiteIncomingCoordinates]
  norm_num only [arguments, successorValues, Fin.last, map_ofNat, map_one, Fin.val_cast]
  constructor <;> rintro ⟨row, rowBound⟩ ⟨column, columnBound⟩
  all_goals
    have rowSmall : row < 2 := by simpa only [map_ofNat] using rowBound
    have columnSmall : column < 2 := by
      have normalized := columnBound
      norm_num only [map_ofNat, map_one] at normalized
      omega
    interval_cases row <;> interval_cases column
  all_goals
    simp only [List.take_zero, IntegerMatrix.hermiteRowStage, IntegerMatrix.rowRemainderSweep,
      IntegerMatrix.hermiteRowStep]
    norm_num [IntegerMatrix.bezoutRowsWithLeft, IntegerMatrix.rowPair, Matrix.one_apply,
      Matrix.updateRow_apply, IntegerMatrix.bezoutMatrix]
  all_goals decide +kernel

example : (hermiteIncomingStageWithin (Parameter := Empty) 2 1 3 1).TM0Realizable :=
  (hermiteIncomingStageWithin_realizable 2 1 3 1).tm0

example :
    let narrowed := (hermiteIncomingStageWithin (Parameter := Empty) 2 1 3 1).compute
      Empty.elim ⟨arguments, withinValid⟩
    narrowed.1.val = result.1.val ∧ narrowed.2.val = result.2.val := ⟨rfl, rfl⟩

end Polytime2.Examples.HermiteIncomingStage
