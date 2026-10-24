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

import Polytime2.Matrices.DiagonalProgressMath
import Polytime2.Arrays.FindFalseMath

/-! # Polynomially bounded mathematical diagonal cleanup

Scan for an adjacent divisibility failure, replace that pair by its gcd and
lcm, and repeat. A bounded recursion suffices: each effective iteration consumes
one bit of the weighted potential, initially at most `width * length² + 1`.
All positive entries remain bounded by the invariant total product. This is the
mathematical diagonal stage only. Matrix transformations and their realizations
are developed in subsequent modules.
-/

namespace Polytime2.IntegerMatrix

variable {length : ℕ}

/-- Divisibility of successive active entries in their mathematical order. -/
def diagonalDivisibilityChain (diagonal : Fin length → ℕ) : Prop :=
  ∀ first second : Fin length, second.val = first.val + 1 → diagonal first ∣ diagonal second

/-- Find the first failed adjacent relation by scanning the mathematical diagonal flags. -/
def diagonalViolation (diagonal : Fin length → ℕ) : Option (Fin length × Fin length) :=
  (ArraySearch.firstFalse (ArraySearch.adjacentFlags (fun first second : ℕ => first ∣ second) diagonal)).bind
    (fun first => if next : first.val + 1 < length then some (first, ⟨first.val + 1, next⟩) else none)

theorem diagonalViolation_some (diagonal : Fin length → ℕ) (first second : Fin length)
    (found : diagonalViolation diagonal = some (first, second)) :
    second.val = first.val + 1 ∧ ¬diagonal first ∣ diagonal second := by
  unfold diagonalViolation at found
  obtain ⟨index, selected, converted⟩ := Option.bind_eq_some_iff.mp found
  split_ifs at converted with next
  · have equal := Option.some.inj converted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have failure := ArraySearch.firstFalse_found _ index selected
    refine ⟨rfl, ?_⟩
    simpa only [ArraySearch.adjacentFlags, next, ↓reduceDIte, decide_eq_false_iff_not] using failure

theorem diagonalViolation_none (diagonal : Fin length → ℕ) :
    diagonalViolation diagonal = none ↔ diagonalDivisibilityChain diagonal := by
  let flags := ArraySearch.adjacentFlags (fun first second : ℕ => first ∣ second) diagonal
  have none_iff : diagonalViolation diagonal = none ↔ ArraySearch.firstFalse flags = none := by
    unfold diagonalViolation
    change (ArraySearch.firstFalse flags).bind _ = none ↔ _
    cases selected : ArraySearch.firstFalse flags with
    | none => simp
    | some index =>
      have failure := ArraySearch.firstFalse_found flags index selected
      have next : index.val + 1 < length := by
        by_contra outside
        simp [flags, ArraySearch.adjacentFlags, outside] at failure
      simp [next]
  exact none_iff.trans ((ArraySearch.firstFalse_none flags).trans
    (ArraySearch.adjacentFlags_all (fun first second : ℕ => first ∣ second) diagonal))

/-- Bounded recursion uses the certified gcd/lcm pair update at every effective step. -/
def diagonalCleanup : ℕ → (Fin length → ℕ) → (Fin length → ℕ)
  | 0, diagonal => diagonal
  | remaining + 1, diagonal => match diagonalViolation diagonal with
    | none => diagonal
    | some (first, second) => diagonalCleanup remaining (diagonalNormalizePair diagonal first second)

/-- Every prefix preserves positivity and product; enough measure fuel also gives a chain. -/
theorem diagonalCleanup_correct (fuel : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) :
    (∀ index, 0 < diagonalCleanup fuel diagonal index) ∧
      (∏ index, diagonalCleanup fuel diagonal index) = (∏ index, diagonal index) ∧
      ((diagonalPotential diagonal).size ≤ fuel → diagonalDivisibilityChain (diagonalCleanup fuel diagonal)) := by
  induction fuel generalizing diagonal with
  | zero =>
    refine ⟨positive, rfl, ?_⟩
    intro measureBound
    have none : diagonalViolation diagonal = none := by
      cases found : diagonalViolation diagonal with
      | none => rfl
      | some pair =>
        obtain ⟨first, second⟩ := pair
        have failure := diagonalViolation_some diagonal first second found
        have decrease := diagonalNormalizePair_size_decreases diagonal positive first second failure.1 failure.2
        omega
    exact (diagonalViolation_none diagonal).mp none
  | succ fuel inductionHypothesis =>
    cases found : diagonalViolation diagonal with
    | none =>
      simp only [diagonalCleanup, found]
      exact ⟨positive, trivial, fun _ => (diagonalViolation_none diagonal).mp found⟩
    | some pair =>
      obtain ⟨first, second⟩ := pair
      have failure := diagonalViolation_some diagonal first second found
      have decrease := diagonalNormalizePair_size_decreases diagonal positive first second failure.1 failure.2
      have updated := inductionHypothesis (diagonalNormalizePair diagonal first second)
        (diagonalNormalizePair_positive diagonal positive first second)
      have different : first ≠ second := by intro same; subst second; omega
      simp only [diagonalCleanup, found]
      refine ⟨updated.1, updated.2.1.trans (diagonalNormalizePair_product diagonal first second different), ?_⟩
      intro measureBound
      exact updated.2.2 (by omega)

/-- The same bit bound holds after any number of iterations, including unfinished prefixes. -/
theorem diagonalCleanup_entry_bound (fuel width : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (entryBound : ∀ index, diagonal index < 2 ^ width) :
    ∀ index, diagonalCleanup fuel diagonal index < 2 ^ (width * length + 1) := by
  have invariants := diagonalCleanup_correct fuel diagonal positive
  exact diagonalEntries_bound_of_product width diagonal _ entryBound invariants.1 invariants.2.1

/-- A fixed polynomial iteration budget suffices for bounded positive input entries. -/
theorem diagonalCleanup_polynomial (width : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := diagonalCleanup (width * length * length + 1) diagonal
    diagonalDivisibilityChain result ∧ (∀ index, 0 < result index) ∧
      (∀ index, result index < 2 ^ (width * length + 1)) ∧
      (∏ index, result index) = ∏ index, diagonal index := by
  have correct := diagonalCleanup_correct (width * length * length + 1) diagonal positive
  exact ⟨correct.2.2 (diagonalPotential_initial_size_bound width diagonal entryBound), correct.1,
    diagonalEntries_bound_of_product width diagonal _ entryBound correct.1 correct.2.1, correct.2.1⟩

end Polytime2.IntegerMatrix
