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

import Mathlib.Data.List.FinRange

/-! # Mathematical finite-array search and adjacency

The first false position is an optional finite coordinate. Adjacent relation
flags omit any test beyond the final entry. These pure mathematical functions
are shared by the cleanup schedule and the certified array implementation.
-/

namespace Polytime2.ArraySearch

variable {length : ℕ}

/-- The least false coordinate, with no out-of-range sentinel in the result. -/
def firstFalse (flags : Fin length → Bool) : Option (Fin length) :=
  if within : (List.ofFn flags).findIdx (! ·) < length then
    some ⟨(List.ofFn flags).findIdx (! ·), within⟩ else none

theorem firstFalse_some_iff (flags : Fin length → Bool) (index : Fin length) :
    firstFalse flags = some index ↔ (List.ofFn flags).findIdx (! ·) = index.val := by
  unfold firstFalse
  split_ifs with within
  · simp only [Option.some.injEq, Fin.ext_iff]
  · constructor
    · intro impossible
      cases impossible
    · intro equal
      exact False.elim (within (equal.symm ▸ index.isLt))

theorem firstFalse_none (flags : Fin length → Bool) :
    firstFalse flags = none ↔ ∀ index, flags index = true := by
  have bound : (List.ofFn flags).findIdx (! ·) ≤ length := by
    simpa only [List.length_ofFn] using List.findIdx_le_length (p := (! ·)) (xs := List.ofFn flags)
  simp only [firstFalse, dite_eq_right_iff, Option.some_ne_none, imp_false]
  have sentinel : (List.ofFn flags).findIdx (! ·) = length ↔ ∀ index, flags index = true := by
    simpa using (List.findIdx_eq_length (p := (! ·)) (xs := List.ofFn flags))
  exact (show ¬(List.ofFn flags).findIdx (! ·) < length ↔ (List.ofFn flags).findIdx (! ·) = length by omega).trans sentinel

theorem firstFalse_found (flags : Fin length → Bool) (index : Fin length)
    (found : firstFalse flags = some index) : flags index = false := by
  have selected := (firstFalse_some_iff flags index).mp found
  have before : (List.ofFn flags).findIdx (! ·) < (List.ofFn flags).length := by
    simpa only [List.length_ofFn, selected] using index.isLt
  have failed := List.findIdx_getElem (p := (! ·)) (xs := List.ofFn flags) (w := before)
  simpa [selected] using failed

/-- Test a relation between successive entries, accepting the final coordinate. -/
def adjacentFlags {Element : Type} (relation : Element → Element → Prop) [DecidableRel relation]
    (values : Fin length → Element) (index : Fin length) : Bool :=
  if next : index.val + 1 < length then decide (relation (values index) (values ⟨index.val + 1, next⟩)) else true

theorem adjacentFlags_all {Element : Type} (relation : Element → Element → Prop) [DecidableRel relation]
    (values : Fin length → Element) :
    (∀ index, adjacentFlags relation values index = true) ↔
      ∀ first second : Fin length, second.val = first.val + 1 → relation (values first) (values second) := by
  constructor
  · intro accepted first second adjacent
    have next : first.val + 1 < length := by rw [← adjacent]; exact second.isLt
    have same : (⟨first.val + 1, next⟩ : Fin length) = second := Fin.ext adjacent.symm
    simpa only [adjacentFlags, next, ↓reduceDIte, same, decide_eq_true_eq] using accepted first
  · intro chain index
    by_cases next : index.val + 1 < length
    · simpa only [adjacentFlags, next, ↓reduceDIte, decide_eq_true_eq] using chain index ⟨index.val + 1, next⟩ rfl
    · simp [adjacentFlags, next]

end Polytime2.ArraySearch
