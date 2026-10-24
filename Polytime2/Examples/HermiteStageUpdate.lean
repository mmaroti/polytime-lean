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

import Polytime2.Matrices.HermiteStageController
import Polytime2.TM0.Computation

/-! # Runtime interleaved stage update

The incoming entry causes a genuine gcd change, then an earlier row is reduced
against the new pivot. The actual left basis records both operations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.HermiteStageUpdate

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStageUpdate rows columns width).TM0Realizable :=
  (integerHermiteRowStageUpdate_realizable rows columns width).tm0

private noncomputable def arguments :
    (integerHermiteRowStageUpdate (Parameter := Empty) 3 2 3).Arguments Empty.elim
  | 0 => ⟨1, by norm_num⟩
  | 1 => ⟨2, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨0, by norm_num⟩
  | 4 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 4 else 5)
      else if row.val = 1 then (if column.val = 0 then 6 else 1)
      else (if column.val = 0 then 2 else 4), by
        intro row column
        dsimp only
        split_ifs <;> norm_num⟩
  | 5 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩

private theorem valid :
    (integerHermiteRowStageUpdate (Parameter := Empty) 3 2 3).precondition Empty.elim arguments := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · norm_num [arguments]

private noncomputable def result :=
  (integerHermiteRowStageUpdate (Parameter := Empty) 3 2 3).compute Empty.elim ⟨arguments, valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = -3 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by decide +kernel

example : result.2.val ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ = -2 ∧
    result.2.val ⟨2, by norm_num⟩ ⟨1, by norm_num⟩ = -1 ∧
    result.2.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 3 := by decide +kernel

example {Parameter : Type} [Fintype Parameter] (rows columns workspace : MvPolynomial Parameter ℕ) :
    (Realizable.Internal.integerHermiteRowStageUpdateWithin rows columns workspace).TM0Realizable :=
  (Realizable.Internal.integerHermiteRowStageUpdateWithin_realizable rows columns workspace).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns workspace : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (Realizable.Internal.hermiteStageContext rows columns)
      (Polytime2.EncodedDomain.boundedIndex rows) (Realizable.Internal.hermiteColumnState rows columns workspace)
      (Realizable.Internal.hermiteStageUpdateAllowed rows columns workspace)
      (Realizable.Internal.hermiteStageUpdate rows columns workspace)).TM0Realizable :=
  (Realizable.Internal.hermiteStageUpdate_realizable rows columns workspace).tm0

private def normalizationMatrix : Matrix (Fin 4) (Fin 2) ℤ := !![4, 5; 3, 2; 6, 1; 2, 4]

/-- Forward traversal of two earlier rows agrees with the mathematical stage. -/
example :
    ([0, 1] : List (Fin 4)).foldl
      (fun state row => Polytime2.IntegerMatrix.hermiteRowStage 2 3 0 [row] state.1 state.2)
      (Polytime2.IntegerMatrix.hermiteRowStep 2 3 0 normalizationMatrix 1) =
      Polytime2.IntegerMatrix.hermiteRowStage 2 3 0 [0, 1] normalizationMatrix 1 :=
  Polytime2.IntegerMatrix.hermiteRowStage_foldl_singletons 2 3 (by decide) 0 [0, 1]
    (by decide) (by decide) (by decide) normalizationMatrix 1 (by decide +kernel)

example : (Polytime2.IntegerMatrix.hermiteRowStage 2 3 0 [0, 1] normalizationMatrix 1).1 =
    !![0, -3; 1, -2; 2, 4; 0, 11] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

end Polytime2.Examples.HermiteStageUpdate
