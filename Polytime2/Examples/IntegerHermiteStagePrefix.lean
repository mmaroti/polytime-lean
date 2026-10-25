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

import Polytime2.Matrices.IntegerHermiteStagePrefix
import Polytime2.TM0.Computation

/-! # Runtime-selected earlier-row prefixes

The fixed row array contains both the source and incoming row in its inactive
suffix. Selecting its first two rows normalizes both; selecting zero rows
retains them while still performing incoming-row elimination.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteStagePrefix

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStagePrefix rows columns width length).TM0Realizable :=
  (integerHermiteRowStagePrefix_realizable rows columns width length).tm0

private noncomputable def arguments (count : ℕ) (bounded : count ≤ 4) :
    (integerHermiteRowStagePrefix (Parameter := Empty) 4 2 3 4).Arguments Empty.elim
  | 0 => ⟨2, by norm_num⟩
  | 1 => ⟨3, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 4 else 5)
      else if row.val = 1 then (if column.val = 0 then 3 else 2)
      else if row.val = 2 then (if column.val = 0 then 6 else 1)
      else (if column.val = 0 then 2 else 4), by
        intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 4 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩
  | 5 => id
  | 6 => ⟨count, by norm_num; omega⟩

private theorem valid : (integerHermiteRowStagePrefix (Parameter := Empty) 4 2 3 4).precondition
    Empty.elim (arguments 2 (by decide)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · norm_num [arguments]
  · exact (List.nodup_ofFn.mpr Function.injective_id).take
  all_goals
    intro member
    obtain ⟨index, bounded, same⟩ := List.mem_iff_getElem.mp member
    have values := congrArg Fin.val same
    norm_num [arguments, List.getElem_take, List.getElem_ofFn] at values
    simp only [arguments, List.length_take, List.length_ofFn] at bounded
    have before : index < 2 := lt_of_lt_of_le bounded (Nat.min_le_left _ _)
    interval_cases index <;> norm_num at values

private noncomputable def result :=
  (integerHermiteRowStagePrefix (Parameter := Empty) 4 2 3 4).compute Empty.elim ⟨arguments 2 (by decide), valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = -3 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = -2 ∧
    result.1.val ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 2 := by
  have observed := congrArg Prod.fst
    (integerHermiteRowStagePrefix_correct (Parameter := Empty) 4 2 3 4 Empty.elim ⟨arguments 2 (by decide), valid⟩)
  dsimp only at observed
  rw [show result.1.val = _ from observed]
  simp only [arguments, map_ofNat]
  decide +kernel

private theorem zeroValid : (integerHermiteRowStagePrefix (Parameter := Empty) 4 2 3 4).precondition
    Empty.elim (arguments 0 (by decide)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · norm_num [arguments]
  · simp [arguments]
  · simp [arguments]
  · simp [arguments]

example :
    let output := (integerHermiteRowStagePrefix (Parameter := Empty) 4 2 3 4).compute Empty.elim
      ⟨arguments 0 (by decide), zeroValid⟩
    output.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 4 ∧
      output.1.val ⟨3, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  dsimp only
  have observed := congrArg Prod.fst
    (integerHermiteRowStagePrefix_correct (Parameter := Empty) 4 2 3 4 Empty.elim ⟨arguments 0 (by decide), zeroValid⟩)
  dsimp only at observed
  rw [observed]
  decide +kernel

end Polytime2.Examples.IntegerHermiteStagePrefix
