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

import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

/-! # Moving selected pivots to the front

Extend an injective pivot list to a deterministic permutation using one swap per
pivot. At each step, the next canonical position is sent to its selected pivot,
while previously fixed pivot positions are retained. This supplies actual row
and column permutations without an arbitrary complement bijection.
-/

namespace Polytime2.IntegerMatrix

private theorem pivotDimensionBound {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension) : rank ≤ dimension := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective selected selected.injective

/-- Align the first `count` positions with their selected pivots. -/
def pivotPermutationPrefix {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension) :
    (count : ℕ) → count ≤ rank → Equiv.Perm (Fin dimension)
  | 0, _ => Equiv.refl _
  | count + 1, within =>
    let previous := pivotPermutationPrefix selected count (by omega)
    let position : Fin dimension := ⟨count, lt_of_lt_of_le (by omega) (pivotDimensionBound selected)⟩
    previous.trans (Equiv.swap (previous position) (selected ⟨count, by omega⟩))

/-- Each completed prefix position has its prescribed image. -/
theorem pivotPermutationPrefix_apply {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension)
    (count : ℕ) (within : count ≤ rank) (index : Fin rank) (before : index.val < count) :
    pivotPermutationPrefix selected count within (Fin.castLE (pivotDimensionBound selected) index) = selected index := by
  induction count with
  | zero => omega
  | succ count induction =>
    let previous := pivotPermutationPrefix selected count (by omega)
    let position : Fin dimension := ⟨count, lt_of_lt_of_le (by omega) (pivotDimensionBound selected)⟩
    let next : Fin rank := ⟨count, by omega⟩
    change Equiv.swap (previous position) (selected next)
      (previous (Fin.castLE (pivotDimensionBound selected) index)) = selected index
    by_cases same : index.val = count
    · have indexEq : index = next := Fin.ext same
      rw [indexEq]
      exact Equiv.swap_apply_left _ _
    · have earlier : index.val < count := by omega
      have fixed := induction (by omega) earlier
      change previous (Fin.castLE (pivotDimensionBound selected) index) = selected index at fixed
      rw [fixed]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro equal
        have positions := previous.injective (fixed.trans equal)
        have values := congrArg Fin.val positions
        change index.val = count at values
        exact same values
      · intro equal
        have values := congrArg Fin.val (selected.injective equal)
        exact same values

/-- A deterministic permutation sends canonical pivot positions to the selected indices. -/
def pivotPermutation {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension) : Equiv.Perm (Fin dimension) :=
  pivotPermutationPrefix selected rank (by rfl)

theorem pivotPermutation_apply {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension) (index : Fin rank) :
    pivotPermutation selected (Fin.castLE (pivotDimensionBound selected) index) = selected index :=
  pivotPermutationPrefix_apply selected rank (by rfl) index index.isLt

/-- Positions beyond the canonical pivot prefix cannot map to selected pivots. -/
theorem pivotPermutation_outside {rank dimension : ℕ} (selected : Fin rank ↪ Fin dimension)
    (index : Fin dimension) (outside : rank ≤ index.val) : pivotPermutation selected index ∉ Set.range selected := by
  rintro ⟨pivot, equal⟩
  have positions := (pivotPermutation selected).injective ((pivotPermutation_apply selected pivot).trans equal)
  have values := congrArg Fin.val positions
  change pivot.val = index.val at values
  have before := pivot.isLt
  omega

/-- Equal dimensions and equal selected coordinates give equal permutation images. -/
theorem pivotPermutation_congr {rank dimension otherRank otherDimension : ℕ}
    (rankEqual : rank = otherRank) (dimensionEqual : dimension = otherDimension)
    (selected : Fin rank ↪ Fin dimension) (other : Fin otherRank ↪ Fin otherDimension)
    (same : ∀ first second, first.val = second.val → (selected first).val = (other second).val)
    (first : Fin dimension) (second : Fin otherDimension) (indexEqual : first.val = second.val) :
    (pivotPermutation selected first).val = (pivotPermutation other second).val := by
  subst otherRank
  subst otherDimension
  have embeddings : selected = other := by
    ext index
    exact same index index rfl
  have indices : first = second := Fin.ext indexEqual
  subst other
  subst second
  rfl

end Polytime2.IntegerMatrix
