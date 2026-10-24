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

import Polytime2.Arrays.BoundedSnoc
import Polytime2.TM0.Computation

/-! # Appending arrays at their actual stored count

A capacity-five array with two live values calls snoc at count two. An empty
array calls it at zero, including when its original capacity is zero.
-/

namespace Polytime2.Examples.BoundedSnoc

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (element : EncodedDomain Parameter)
    (capacity : MvPolynomial Parameter ℕ) :
    (boundedArraySnocCall element capacity).TM0Realizable :=
  (boundedArraySnocCall_realizable element capacity).tm0

private noncomputable def arguments : (boundedArraySnocCall (Parameter := Empty) booleans 5).Arguments Empty.elim :=
  fun _ => (⟨⟨2, by norm_num⟩, fun index => decide (index.val = 1)⟩, true)

example : (((boundedArraySnocCall (Parameter := Empty) booleans 5).compute Empty.elim
    ⟨arguments, trivial⟩).1 (.inr ())).val = 2 :=
  boundedArraySnocCall_count booleans 5 Empty.elim ⟨arguments, trivial⟩

example : (((boundedArraySnocCall (Parameter := Empty) booleans 0).compute Empty.elim
    ⟨(fun _ => (⟨⟨0, by norm_num⟩, Fin.elim0⟩, true)), trivial⟩).1 (.inr ())).val = 0 := rfl

example : (((boundedArraySnocCall (Parameter := Empty) booleans 5).compute Empty.elim
    ⟨(fun _ => (⟨⟨0, by norm_num⟩, Fin.elim0⟩, true)), trivial⟩).1 (.inr ())).val = 0 := rfl

example : let result := (boundedArraySnocCall (Parameter := Empty) booleans 5).compute Empty.elim ⟨arguments, trivial⟩
    result.2 ⟨2, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change 2 < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      norm_num [arguments]⟩ = true :=
  boundedArraySnocCall_last booleans 5 Empty.elim ⟨arguments, trivial⟩

example : let result := (boundedArraySnocCall (Parameter := Empty) booleans 5).compute Empty.elim ⟨arguments, trivial⟩
    result.2 ⟨0, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change 0 < (result.1 (.inr ())).val + 1
      omega⟩ = false :=
  boundedArraySnocCall_get booleans 5 Empty.elim ⟨arguments, trivial⟩ ⟨0, by norm_num [arguments]⟩

example : let result := (boundedArraySnocCall (Parameter := Empty) booleans 5).compute Empty.elim ⟨arguments, trivial⟩
    result.2 ⟨1, by
      simp only [map_add, map_one, MvPolynomial.eval_X]
      change 1 < (result.1 (.inr ())).val + 1
      rw [boundedArraySnocCall_count]
      norm_num [arguments]⟩ = true :=
  boundedArraySnocCall_get booleans 5 Empty.elim ⟨arguments, trivial⟩ ⟨1, by norm_num [arguments]⟩

example {Parameter : Type} [Fintype Parameter] (element : EncodedDomain Parameter)
    (capacity : MvPolynomial Parameter ℕ) :
    (boundedArraySnoc element capacity).TM0Realizable := (boundedArraySnoc_realizable element capacity).tm0

private theorem valid : (boundedArraySnoc (Parameter := Empty) booleans 5).precondition Empty.elim arguments := by
  dsimp only [boundedArraySnoc, arguments]
  norm_num

private noncomputable def appended :=
  (boundedArraySnoc (Parameter := Empty) booleans 5).compute Empty.elim ⟨arguments, valid⟩

example : appended.1.val = 3 := rfl

example : appended.2 ⟨0, by dsimp only [appended, boundedArraySnoc, arguments]; norm_num⟩ = false :=
  boundedArraySnoc_get booleans 5 Empty.elim ⟨arguments, valid⟩ ⟨0, by norm_num [arguments]⟩

example : appended.2 ⟨1, by dsimp only [appended, boundedArraySnoc, arguments]; norm_num⟩ = true :=
  boundedArraySnoc_get booleans 5 Empty.elim ⟨arguments, valid⟩ ⟨1, by norm_num [arguments]⟩

example : appended.2 ⟨2, by dsimp only [appended, boundedArraySnoc, arguments]; norm_num⟩ = true :=
  boundedArraySnoc_last booleans 5 Empty.elim ⟨arguments, valid⟩

example : ¬(boundedArraySnoc (Parameter := Empty) booleans 0).precondition Empty.elim
    (fun _ => (⟨⟨0, by norm_num⟩, Fin.elim0⟩, true)) := by
  dsimp only [boundedArraySnoc]
  norm_num

end Polytime2.Examples.BoundedSnoc
