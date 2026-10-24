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

import Polytime2.Matrices.PivotPermutation
import Polytime2.TM0.Computation

/-! # Certified pivot-compaction permutation tables

A noncanonical two-pivot selection is moved into the leading two positions.
The full image table is bijective, and empty selections retain the identity,
including dimension zero. The scalar swap is checked when its values coincide.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.PivotPermutation

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (dimension count : MvPolynomial Parameter ℕ) :
    (pivotPermutationTable dimension count).TM0Realizable :=
  (pivotPermutationTable_realizable dimension count).tm0

private noncomputable def selected : ((boundedIndex (4 : MvPolynomial Empty ℕ)).arrayOfLength 2).Carrier Empty.elim :=
  fun index => if index.val = 0 then ⟨2, by norm_num⟩ else ⟨0, by norm_num⟩

private theorem injective : Function.Injective selected := by
  intro first second same
  have firstBound : first.val < 2 := by simpa using first.isLt
  have secondBound : second.val < 2 := by simpa using second.isLt
  have numbers := congrArg Fin.val same
  dsimp only [selected] at numbers
  split_ifs at numbers <;> apply Fin.ext <;> omega

private noncomputable def embedding : Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)) ↪
    Fin (MvPolynomial.eval Empty.elim (4 : MvPolynomial Empty ℕ)) := ⟨selected, injective⟩

example : Function.Bijective ((pivotPermutationTable (4 : MvPolynomial Empty ℕ) 2).compute Empty.elim
    ⟨(fun _ => selected), injective⟩) := pivotPermutationTable_bijective 4 2 Empty.elim ⟨(fun _ => selected), injective⟩

example : (pivotPermutationTable (4 : MvPolynomial Empty ℕ) 2).compute Empty.elim
    ⟨(fun _ => selected), injective⟩ ⟨0, by norm_num⟩ = ⟨2, by norm_num⟩ := by
  rw [pivotPermutationTable_correct 4 2 Empty.elim ⟨(fun _ => selected), injective⟩ embedding rfl]
  have leading := Polytime2.IntegerMatrix.pivotPermutation_apply embedding ⟨0, by norm_num⟩
  convert leading using 1 <;> rfl

example : (pivotPermutationTable (4 : MvPolynomial Empty ℕ) 2).compute Empty.elim
    ⟨(fun _ => selected), injective⟩ ⟨1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  rw [pivotPermutationTable_correct 4 2 Empty.elim ⟨(fun _ => selected), injective⟩ embedding rfl]
  have leading := Polytime2.IntegerMatrix.pivotPermutation_apply embedding ⟨1, by norm_num⟩
  convert leading using 1 <;> rfl

example {Parameter : Type} [Fintype Parameter] (dimension : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (pivotPermutationTable dimension 0).Arguments sizes //
      (pivotPermutationTable dimension 0).precondition sizes arguments}) :
    (pivotPermutationTable dimension 0).compute sizes arguments = id := by
  let selected : Fin (MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ)) ↪ Fin (MvPolynomial.eval sizes dimension) :=
    ⟨arguments.val (), arguments.property⟩
  rw [pivotPermutationTable_correct dimension 0 sizes arguments selected (by funext index; rfl)]
  simp only [Polytime2.IntegerMatrix.pivotPermutation, map_zero, Polytime2.IntegerMatrix.pivotPermutationPrefix]
  rfl

example : (elementsSwap (booleans : EncodedDomain Empty)).compute Empty.elim
    ⟨(fun name => if name.val = 2 then false else true), trivial⟩ = false := by
  simp [elementsSwap]

end Polytime2.Examples.PivotPermutation
