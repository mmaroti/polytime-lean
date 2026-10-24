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

import Polytime2.Matrices.IntegerHermiteStage
import Polytime2.TM0.Computation

/-! # Complete runtime interleaved stage

Two earlier rows are normalized after one incoming-row elimination. The same
public operation handles an empty earlier-row array and still clears the
incoming entry. Both actual matrix and basis entries are checked.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteStage

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStage rows columns width length).TM0Realizable :=
  (integerHermiteRowStage_realizable rows columns width length).tm0

private noncomputable def arguments (length : MvPolynomial Empty ℕ)
    (tokens : (Polytime2.EncodedDomain.boundedIndex 4 |>.arrayOfLength length).Carrier Empty.elim) :
    (integerHermiteRowStage (Parameter := Empty) 4 2 3 length).Arguments Empty.elim
  | 0 => ⟨2, by norm_num⟩
  | 1 => ⟨3, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 4 else 5)
      else if row.val = 1 then (if column.val = 0 then 3 else 2)
      else if row.val = 2 then (if column.val = 0 then 6 else 1)
      else (if column.val = 0 then 2 else 4), by
        intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 4 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩
  | 5 => tokens

private noncomputable def tokens :
    (Polytime2.EncodedDomain.boundedIndex (Parameter := Empty) 4 |>.arrayOfLength 2).Carrier Empty.elim :=
  fun index => ⟨index.val, by have bounded := index.isLt; norm_num at bounded ⊢; omega⟩

private theorem valid : (integerHermiteRowStage (Parameter := Empty) 4 2 3 2).precondition
    Empty.elim (arguments 2 tokens) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · norm_num [arguments]
  · apply List.nodup_ofFn.mpr
    intro first second same
    have values := congrArg Fin.val same
    apply Fin.ext
    exact values
  · intro member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    have values := congrArg Fin.val same
    have bounded := index.isLt
    norm_num [arguments, tokens] at values bounded
    omega
  · intro member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    have values := congrArg Fin.val same
    have bounded := index.isLt
    norm_num [arguments, tokens] at values bounded
    omega

private noncomputable def result :=
  (integerHermiteRowStage (Parameter := Empty) 4 2 3 2).compute Empty.elim ⟨arguments 2 tokens, valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = -3 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = -2 ∧
    result.1.val ⟨3, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  simp only [result, integerHermiteRowStage, arguments, tokens, map_ofNat]
  decide +kernel

example : result.2.val ⟨0, by norm_num⟩ ⟨3, by norm_num⟩ = -2 ∧
    result.2.val ⟨1, by norm_num⟩ ⟨3, by norm_num⟩ = -1 ∧
    result.2.val ⟨3, by norm_num⟩ ⟨2, by norm_num⟩ = -1 := by
  simp only [result, integerHermiteRowStage, arguments, tokens, map_ofNat]
  decide +kernel

private noncomputable def emptyTokens :
    (Polytime2.EncodedDomain.boundedIndex (Parameter := Empty) 4 |>.arrayOfLength 0).Carrier Empty.elim :=
  fun index => False.elim (by have bounded := index.isLt; norm_num at bounded)

private theorem emptyValid : (integerHermiteRowStage (Parameter := Empty) 4 2 3 0).precondition
    Empty.elim (arguments 0 emptyTokens) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    norm_num [arguments] at values
  · norm_num [arguments]
  · simp
  · simp [arguments]
  · simp [arguments]

example : ((integerHermiteRowStage (Parameter := Empty) 4 2 3 0).compute Empty.elim
    ⟨arguments 0 emptyTokens, emptyValid⟩).1.val ⟨3, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by decide +kernel

end Polytime2.Examples.IntegerHermiteStage
