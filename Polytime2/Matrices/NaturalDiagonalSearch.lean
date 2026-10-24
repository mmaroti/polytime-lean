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

import Polytime2.Matrices.DiagonalSearch
import Polytime2.Matrices.DiagonalCleanupMath

/-! # Certified search on the natural active Smith diagonal

Nonnegative bounded entries are converted by the existing signed construction
and passed to the adjacent-divisibility scan. Every returned coordinate has an
actual successor witnessing failure. On positive diagonals, the corresponding
gcd/lcm replacement strictly decreases the already proved global bit measure.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Test adjacent natural entries using the shared signed divisibility operations. -/
noncomputable def naturalDiagonalDivisibilityFlags (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (mapArray (binaryNaturalsOfWidth width) (binaryIntegers width) length
    (fun _ value => ⟨(value.val : ℤ), by simpa using value.isLt⟩)).followedBy
      (diagonalDivisibilityFlags length width) rfl (by intros; trivial)

theorem naturalDiagonalDivisibilityFlags_realizable (length width : MvPolynomial Parameter ℕ) :
    (naturalDiagonalDivisibilityFlags length width).Realizable :=
  (mapArray_realizable (binaryNaturalsOfWidth width) (binaryIntegers width) length
    (fun _ value => ⟨(value.val : ℤ), by simpa using value.isLt⟩)
    (Realizable.Internal.integerOfMagnitude_realizable width)).followedBy
      (diagonalDivisibilityFlags_realizable length width) rfl (by intros; trivial)

/-- Find an adjacent divisibility failure in an ordinary bounded natural diagonal. -/
noncomputable def naturalDiagonalSearch (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (naturalDiagonalDivisibilityFlags length width).followedBy (arrayFindFalse length) rfl (by intros; trivial)

theorem naturalDiagonalSearch_realizable (length width : MvPolynomial Parameter ℕ) :
    (naturalDiagonalSearch length width).Realizable :=
  (naturalDiagonalDivisibilityFlags_realizable length width).followedBy (arrayFindFalse_realizable length) rfl
    (by intros; trivial)

/-- The natural flags have exactly the ordinary adjacent-divisibility specification. -/
theorem naturalDiagonalDivisibilityFlags_spec (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    (naturalDiagonalDivisibilityFlags length width).compute sizes ⟨(fun _ => values), trivial⟩ =
      ArraySearch.adjacentFlags (fun first second : ℕ => first ∣ second) (fun index => (values index).val) := by
  classical
  funext index
  by_cases next : index.val + 1 < MvPolynomial.eval sizes length
  all_goals simp [naturalDiagonalDivisibilityFlags, Computation.followedBy, mapArray,
    diagonalDivisibilityFlags, ArraySearch.adjacentFlags, next, Int.natCast_dvd_natCast]

/-- The scan returns exactly the same first failing coordinate as the pure schedule. -/
theorem naturalDiagonalSearch_spec (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    (naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩ =
      ArraySearch.firstFalse (ArraySearch.adjacentFlags (fun first second : ℕ => first ∣ second)
        (fun index => (values index).val)) := by
  change (arrayFindFalse length).compute sizes
    ⟨(fun _ => (naturalDiagonalDivisibilityFlags length width).compute sizes ⟨(fun _ => values), trivial⟩), trivial⟩ = _
  exact (arrayFindFalse_spec length sizes _).trans
    (congrArg ArraySearch.firstFalse (naturalDiagonalDivisibilityFlags_spec length width sizes values))

/-- Reconstructing the actual successor gives exactly the pair used by the cleanup schedule. -/
theorem naturalDiagonalSearch_pair (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    ((naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩).bind
      (fun first => if next : first.val + 1 < MvPolynomial.eval sizes length then
        some (first, ⟨first.val + 1, next⟩) else none) =
      IntegerMatrix.diagonalViolation (fun index => (values index).val) := by
  rw [naturalDiagonalSearch_spec]
  rfl

/-- The machine's stopping condition agrees with the mathematical cleanup schedule. -/
theorem naturalDiagonalSearch_none (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    (naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = none ↔
      IntegerMatrix.diagonalViolation (fun index => (values index).val) = none := by
  rw [naturalDiagonalSearch_spec, IntegerMatrix.diagonalViolation_none]
  exact (ArraySearch.firstFalse_none _).trans
    (ArraySearch.adjacentFlags_all (fun first second : ℕ => first ∣ second) (fun index => (values index).val))

/-- A returned first coordinate always has a genuine adjacent divisibility failure. -/
theorem naturalDiagonalSearch_found (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes length))
    (found : (naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = some index) :
    ∃ successor : Fin (MvPolynomial.eval sizes length), successor.val = index.val + 1 ∧
      ¬(values index).val ∣ (values successor).val := by
  have failed := diagonalDivisibilitySearch_found length width sizes
    (fun position => ⟨((values position).val : ℤ), by simpa using (values position).isLt⟩) index found
  simpa only [Int.natCast_dvd_natCast] using failed

/-- Every repair selected by the certified scan consumes at least one potential bit. -/
theorem naturalDiagonalSearch_progress (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes)
    (positive : ∀ index, 0 < (values index).val) (index : Fin (MvPolynomial.eval sizes length))
    (found : (naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = some index) :
    ∃ successor : Fin (MvPolynomial.eval sizes length), successor.val = index.val + 1 ∧
      (IntegerMatrix.diagonalPotential (IntegerMatrix.diagonalNormalizePair
        (fun position => (values position).val) index successor)).size <
          (IntegerMatrix.diagonalPotential (fun position => (values position).val)).size := by
  obtain ⟨successor, adjacent, failure⟩ := naturalDiagonalSearch_found length width sizes values index found
  exact ⟨successor, adjacent, IntegerMatrix.diagonalNormalizePair_size_decreases
    (fun position => (values position).val) positive index successor adjacent failure⟩

end Polytime2.Computation
