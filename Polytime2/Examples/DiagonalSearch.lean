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

import Polytime2.Matrices.DiagonalRepairCoordinates
import Polytime2.Matrices.DiagonalChain
import Polytime2.Matrices.DiagonalSelectedRepair
import Polytime2.TM0.Computation

/-! # Certified adjacent-divisibility search examples

Search returns an actual optional coordinate, including at empty and singleton
lengths. Signed zero-divisor tests exercise both arithmetic branches. A positive
diagonal's returned failure is linked to the mathematical cleanup bit measure.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.DiagonalSearch

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (width : MvPolynomial Parameter ℕ) : (integerDivides width).TM0Realizable :=
  (integerDivides_realizable width).tm0

example (length : MvPolynomial Parameter ℕ) : (arrayFindFalse length).TM0Realizable :=
  (arrayFindFalse_realizable length).tm0

example (length width : MvPolynomial Parameter ℕ) : (naturalDiagonalSearch length width).TM0Realizable :=
  (naturalDiagonalSearch_realizable length width).tm0

private noncomputable def naturalArguments (first second third : ℕ)
    (firstBound : first < 16) (secondBound : second < 16) (thirdBound : third < 16) :
    (naturalDiagonalSearch (Parameter := Empty) 3 4).Arguments Empty.elim :=
  fun _ index => if index.val = 0 then ⟨first, by simpa using firstBound⟩
    else if index.val = 1 then ⟨second, by simpa using secondBound⟩
    else ⟨third, by simpa using thirdBound⟩

private theorem firstFailure : (naturalDiagonalSearch (Parameter := Empty) 3 4).compute Empty.elim
    ⟨naturalArguments 6 10 15 (by decide) (by decide) (by decide), trivial⟩ = some ⟨0, by norm_num⟩ := by
  dsimp only [naturalDiagonalSearch, naturalDiagonalDivisibilityFlags, diagonalDivisibilitySearch, Computation.followedBy]
  erw [arrayFindFalse_some_iff]
  dsimp only [diagonalDivisibilityFlags, mapArray]
  rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)]
  norm_num [naturalArguments, List.ofFn_succ]
  decide +kernel

example : (naturalDiagonalSearch (Parameter := Empty) 3 4).compute Empty.elim
    ⟨naturalArguments 1 3 12 (by decide) (by decide) (by decide), trivial⟩ = none := by
  apply (naturalDiagonalSearch_none _ _ _ _).mpr
  rw [IntegerMatrix.diagonalViolation_none]
  intro first second adjacent
  have bounded := second.isLt
  norm_num at bounded
  have cases : first.val = 0 ∨ first.val = 1 := by omega
  rcases cases with zero | one
  · have secondOne : second.val = 1 := by omega
    simp [zero, secondOne]
  · have secondTwo : second.val = 2 := by omega
    simp [one, secondTwo]

example : (naturalDiagonalSearch (Parameter := Empty) 3 4).compute Empty.elim
    ⟨naturalArguments 0 0 3 (by decide) (by decide) (by decide), trivial⟩ = some ⟨1, by norm_num⟩ := by
  dsimp only [naturalDiagonalSearch, naturalDiagonalDivisibilityFlags, diagonalDivisibilitySearch, Computation.followedBy]
  erw [arrayFindFalse_some_iff]
  dsimp only [diagonalDivisibilityFlags, mapArray]
  rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)]
  norm_num [naturalArguments, List.ofFn_succ]
  decide +kernel

example : (naturalDiagonalSearch (Parameter := Empty) 0 0).compute Empty.elim
    ⟨(fun _ index => by have bounded := index.isLt; norm_num at bounded), trivial⟩ = none := by
  apply (naturalDiagonalSearch_none _ _ _ _).mpr
  rw [IntegerMatrix.diagonalViolation_none]
  intro first second adjacent
  have bounded := first.isLt
  norm_num at bounded

example : (naturalDiagonalSearch (Parameter := Empty) 1 0).compute Empty.elim
    ⟨(fun _ _ => ⟨0, by norm_num⟩), trivial⟩ = none := by
  apply (naturalDiagonalSearch_none _ _ _ _).mpr
  rw [IntegerMatrix.diagonalViolation_none]
  intro first second adjacent
  have firstBound := first.isLt
  have secondBound := second.isLt
  norm_num at firstBound secondBound
  omega

example : (integerDivides (Parameter := Empty) 0).compute Empty.elim
    ⟨(fun _ => ⟨0, by norm_num⟩), trivial⟩ = true := by
  change @Eq Bool _ true
  dsimp only [integerDivides]
  decide +kernel

example : (integerDivides (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun choice => if choice then ⟨3, by norm_num⟩ else ⟨0, by norm_num⟩), trivial⟩ = false := by
  change @Eq Bool _ false
  dsimp only [integerDivides]
  decide +kernel

example : (integerDivides (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun choice => if choice then ⟨6, by norm_num⟩ else ⟨-3, by norm_num⟩), trivial⟩ = true := by
  change @Eq Bool _ true
  dsimp only [integerDivides]
  decide +kernel

example (length : MvPolynomial Parameter ℕ) : (arraySearchFound length).TM0Realizable :=
  (arraySearchFound_realizable length).tm0

example (length : MvPolynomial Parameter ℕ) : (arrayIndexSuccessor length).TM0Realizable :=
  (arrayIndexSuccessor_realizable length).tm0

example (length : MvPolynomial Parameter ℕ) : (arraySearchAdjacentPair length).TM0Realizable :=
  (arraySearchAdjacentPair_realizable length).tm0

example (length width : MvPolynomial Parameter ℕ) : (diagonalRepairCoordinates length width).TM0Realizable :=
  (diagonalRepairCoordinates_realizable length width).tm0

private theorem repairAllowed :
    (diagonalRepairCoordinates (Parameter := Empty) 3 4).precondition Empty.elim
      (naturalArguments 6 10 15 (by decide) (by decide) (by decide)) := by
  intro chain
  have divides := chain ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
  norm_num [naturalArguments] at divides

example :
    let result := (diagonalRepairCoordinates (Parameter := Empty) 3 4).compute Empty.elim
      ⟨naturalArguments 6 10 15 (by decide) (by decide) (by decide), repairAllowed⟩
    result.1.val = 0 ∧ result.2.val = 1 := by
  let arguments := naturalArguments 6 10 15 (by decide) (by decide) (by decide)
  let result := (diagonalRepairCoordinates (Parameter := Empty) 3 4).compute Empty.elim
    ⟨arguments, repairAllowed⟩
  have selected := diagonalRepairCoordinates_first (Parameter := Empty) 3 4 Empty.elim
    ⟨arguments, repairAllowed⟩ ⟨0, by norm_num⟩ firstFailure
  have first := congrArg Fin.val selected
  have correct := diagonalRepairCoordinates_correct (Parameter := Empty) 3 4 Empty.elim ⟨arguments, repairAllowed⟩
  change result.1.val = 0 ∧ result.2.val = 1
  have adjacent : result.2.val = result.1.val + 1 := correct.1
  rw [first] at adjacent
  exact ⟨first, adjacent⟩

example : ¬(arraySearchFound (Parameter := Empty) 0).precondition Empty.elim (fun _ => none) := by
  change ¬(false = true)
  decide

example : ¬(arraySearchAdjacentPair (Parameter := Empty) 3).precondition Empty.elim
    (fun _ => some ⟨2, by norm_num⟩) := by
  intro valid
  have next := valid.2 ⟨2, by norm_num⟩ rfl
  norm_num at next

example : (arrayIndexSuccessor (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun _ => ⟨1, by norm_num⟩), by
      change (1 : ℕ) + 1 < MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)
      norm_num⟩ = ⟨2, by norm_num⟩ := rfl

example (length : MvPolynomial Parameter ℕ) : (arrayAllTrue length).TM0Realizable :=
  (arrayAllTrue_realizable length).tm0

example (length width : MvPolynomial Parameter ℕ) : (naturalDiagonalIsChain length width).TM0Realizable :=
  (naturalDiagonalIsChain_realizable length width).tm0

example : (naturalDiagonalIsChain (Parameter := Empty) 3 4).compute Empty.elim
    ⟨naturalArguments 6 10 15 (by decide) (by decide) (by decide), trivial⟩ = false := by
  change @Eq Bool _ false
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact repairAllowed ((naturalDiagonalIsChain_correct (Parameter := Empty) 3 4 Empty.elim _).mp accepted)

example : (naturalDiagonalIsChain (Parameter := Empty) 0 0).compute Empty.elim
    ⟨(fun _ index => by have bound := index.isLt; norm_num at bound), trivial⟩ = true := by
  apply (naturalDiagonalIsChain_correct _ _ _ _).mpr
  intro first second _adjacent
  have bound := first.isLt
  norm_num at bound

example : (arrayAllTrue (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun _ _ => true), trivial⟩ = true :=
  (arrayAllTrue_correct _ _ _).mpr (fun _ => rfl)

example (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (Realizable.Internal.diagonalSelectedRepair length diagonalWidth basisWidth).TM0Realizable :=
  (Realizable.Internal.diagonalSelectedRepair_realizable length diagonalWidth basisWidth).tm0

private noncomputable def selectedArguments :
    (Realizable.Internal.diagonalSelectedRepair (Parameter := Empty) 3 4 21).Arguments Empty.elim
  | 0 => (naturalArguments 6 10 15 (by decide) (by decide) (by decide)) ()
  | 1 | 2 => ⟨1, by
      intro row column
      by_cases same : row = column <;> simp [Matrix.one_apply, same]⟩

private theorem selectedAllowed :
    (Realizable.Internal.diagonalSelectedRepair (Parameter := Empty) 3 4 21).precondition Empty.elim selectedArguments := by
  refine ⟨repairAllowed, 2, ?_, ?_, ?_⟩
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 2
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 2
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · norm_num

example :
    let result := (Realizable.Internal.diagonalSelectedRepair (Parameter := Empty) 3 4 21).compute Empty.elim
      ⟨selectedArguments, selectedAllowed⟩
    result.1.1.val = 0 ∧ result.1.2.val = 1 ∧ result.2.1.1.val = 2 ∧ result.2.1.2.val = 30 := by
  let result := (Realizable.Internal.diagonalSelectedRepair (Parameter := Empty) 3 4 21).compute Empty.elim
    ⟨selectedArguments, selectedAllowed⟩
  have first : result.1.1 = ⟨0, by norm_num⟩ :=
    diagonalRepairCoordinates_first (Parameter := Empty) 3 4 Empty.elim
      ⟨(fun _ => selectedArguments 0), selectedAllowed.1⟩ ⟨0, by norm_num⟩ firstFailure
  have schedule := Realizable.Internal.diagonalSelectedRepair_coordinates (Parameter := Empty) 3 4 21 Empty.elim
    ⟨selectedArguments, selectedAllowed⟩
  have adjacent := (IntegerMatrix.diagonalViolation_some _ _ _ schedule.symm).1
  change result.1.2.val = result.1.1.val + 1 at adjacent
  rw [first] at adjacent
  have second : result.1.2 = ⟨1, by norm_num⟩ := Fin.ext adjacent
  have values := Realizable.Internal.diagonalSelectedRepair_values (Parameter := Empty) 3 4 21 Empty.elim
    ⟨selectedArguments, selectedAllowed⟩
  change result.2.1.1.val = (Nat.gcd (selectedArguments 0 result.1.1).val (selectedArguments 0 result.1.2).val : ℤ) ∧
    result.2.1.2.val = (Nat.lcm (selectedArguments 0 result.1.1).val (selectedArguments 0 result.1.2).val : ℤ) at values
  rw [first, second] at values
  norm_num [selectedArguments, naturalArguments] at values
  exact ⟨congrArg Fin.val first, adjacent, values.1, values.2⟩

end Polytime2.Examples.DiagonalSearch
