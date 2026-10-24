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

import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.IntegerRename
import Polytime2.Matrices.IntegerRowPair
import Polytime2.Matrices.IntegerBezout
import Polytime2.Matrices.BezoutMath
import Polytime2.Matrices.SmithCoordinates
import Polytime2.Matrices.AugmentedMath
import Polytime2.TM0.Computation

/-! # Integer matrix operations for Smith normal form

The examples cover signed coefficients, rectangular and singular matrices,
coincident indices, empty dimensions, and standalone machine export.
-/

namespace Polytime2.Examples.IntegerMatrices

open Polytime2.Computation

private noncomputable abbrev rows : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 0
private noncomputable abbrev columns : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 1
private noncomputable abbrev width : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 2

example : (integerRowAdd rows columns width).Realizable :=
  integerRowAdd_realizable rows columns width

example : (integerColumnAdd rows columns width).Realizable :=
  integerColumnAdd_realizable rows columns width

example : (integerRowAdd rows columns width).TM0Realizable :=
  (integerRowAdd_realizable rows columns width).tm0

example : (integerColumnAdd rows columns width).TM0Realizable :=
  (integerColumnAdd_realizable rows columns width).tm0

example : (integerMatrixTranspose rows columns width).TM0Realizable :=
  (integerMatrixTranspose_realizable rows columns width).tm0

private def singular : Matrix (Fin 2) (Fin 3) ℤ := !![2, -4, 0; 3, -6, 0]

example : IntegerMatrix.rowAdd 0 1 (-1) singular = !![-1, 2, 0; 3, -6, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [IntegerMatrix.rowAdd, singular]

example : IntegerMatrix.columnAdd 1 0 2 singular = !![2, 0, 0; 3, 0, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [IntegerMatrix.columnAdd, IntegerMatrix.rowAdd, singular]

example : IntegerMatrix.rowAdd 0 0 (-1) singular = !![0, 0, 0; 3, -6, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [IntegerMatrix.rowAdd, singular]

example (matrix : Matrix (Fin 2) (Fin 0) ℤ) : IntegerMatrix.rowAdd 0 1 7 matrix = matrix := by
  ext row column
  exact column.elim0

example (matrix : Matrix (Fin 0) (Fin 2) ℤ) : IntegerMatrix.columnAdd 0 1 7 matrix = matrix := by
  ext row column
  exact row.elim0

example : (Matrix.transvection (0 : Fin 2) 1 (-1 : ℤ)).det = 1 :=
  IntegerMatrix.rowAdd_unimodular 0 1 (by decide) (-1)


private def smithDiagonal : Matrix (Fin 2) (Fin 3) ℤ := !![2, 0, 0; 0, 0, 0]

private theorem smithDiagonal_contract : IntegerMatrix.IsSmithDiagonal smithDiagonal 1 := by
  norm_num [IntegerMatrix.IsSmithDiagonal, IntegerMatrix.diagonalEntry,
    smithDiagonal, Fin.forall_fin_succ]
  intro first second next zero
  omega

example : IntegerMatrix.diagonalFeasible smithDiagonal 1 smithDiagonal_contract.1 ![4, 0] := by
  intro row
  fin_cases row <;> norm_num [IntegerMatrix.diagonalFeasible, smithDiagonal]

example : smithDiagonal.mulVec
    (IntegerMatrix.diagonalSolution smithDiagonal 1 smithDiagonal_contract.1 ![4, 0]) = ![4, 0] := by
  apply IntegerMatrix.diagonalSolution_correct smithDiagonal 1 smithDiagonal_contract
  intro row
  fin_cases row <;> norm_num [IntegerMatrix.diagonalFeasible, smithDiagonal]

example : ¬ ∃ values, smithDiagonal.mulVec values = ![3, 0] := by
  rw [← IntegerMatrix.diagonalFeasible_iff smithDiagonal 1 smithDiagonal_contract]
  intro feasible
  have divides := feasible 0
  norm_num [IntegerMatrix.diagonalFeasible, smithDiagonal] at divides

example : ¬ ∃ values, smithDiagonal.mulVec values = ![4, 1] := by
  rw [← IntegerMatrix.diagonalFeasible_iff smithDiagonal 1 smithDiagonal_contract]
  intro feasible
  have zeroRow := feasible 1
  norm_num [IntegerMatrix.diagonalFeasible, smithDiagonal] at zeroRow

example : IntegerMatrix.IsSmithDiagonal (0 : Matrix (Fin 0) (Fin 3) ℤ) 0 := by
  norm_num [IntegerMatrix.IsSmithDiagonal, IntegerMatrix.diagonalEntry,
    smithDiagonal, Fin.forall_fin_succ]

example : IntegerMatrix.IsSmithDiagonal (0 : Matrix (Fin 3) (Fin 0) ℤ) 0 := by
  norm_num [IntegerMatrix.IsSmithDiagonal, IntegerMatrix.diagonalEntry,
    smithDiagonal, Fin.forall_fin_succ]

example : ∃ values : Fin 2 → ℤ, (
    !![1, 2] : Matrix (Fin 1) (Fin 2) ℤ).mulVec values = ![1] := by
  refine ⟨![1, 0], ?_⟩
  ext row
  fin_cases row
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : ¬ ∃ values : Fin 1 → ℤ, (
    !![2] : Matrix (Fin 1) (Fin 1) ℤ).mulVec values = ![1] := by
  rintro ⟨values, solution⟩
  have equation := congrFun solution 0
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at equation
  omega

example : ∃ values, (IntegerMatrix.augmentedMatrix
    (!![2] : Matrix (Fin 1) (Fin 1) ℤ) (fun _ => 3)).mulVec values = ![1] := by
  rw [IntegerMatrix.augmented_feasible_iff]
  refine ⟨![2], ?_⟩
  intro row
  fin_cases row
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]


private def leftChange : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; -3, 2]
private def rightChange : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, 0; 0, 1, 0; 0, 0, 1]
private def unitDiagonal : Matrix (Fin 2) (Fin 3) ℤ := !![1, 0, 0; 0, 0, 0]

private theorem singular_smith :
    IntegerMatrix.IsSmithForm singular unitDiagonal leftChange rightChange 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, singular, leftChange, rightChange, unitDiagonal]
  · norm_num [leftChange, Matrix.det_fin_two]
  · norm_num [rightChange, Matrix.det_fin_three]
  · norm_num [IntegerMatrix.IsSmithDiagonal, IntegerMatrix.diagonalEntry,
      unitDiagonal, Fin.forall_fin_succ]
    intro first second next zero
    omega

example : singular.mulVec (rightChange.mulVec
    (IntegerMatrix.diagonalSolution unitDiagonal 1 singular_smith.2.2.2.1
      (leftChange.mulVec ![2, 3]))) = ![2, 3] := by
  apply IntegerMatrix.smithSolution_correct singular unitDiagonal leftChange rightChange 1 singular_smith
  intro row
  fin_cases row <;> norm_num [IntegerMatrix.diagonalFeasible, unitDiagonal,
    Matrix.mulVec, dotProduct, leftChange, Fin.sum_univ_succ]


example : ¬ ∃ values, singular.mulVec values = ![1, 1] := by
  rw [IntegerMatrix.smithFeasible_iff singular unitDiagonal leftChange rightChange 1 singular_smith]
  intro feasible
  have zeroRow := feasible 1
  norm_num [IntegerMatrix.diagonalFeasible, unitDiagonal,
    Matrix.mulVec, dotProduct, leftChange, Fin.sum_univ_succ] at zeroRow


example : IntegerMatrix.diagonalFeasibilityTest smithDiagonal 1 smithDiagonal_contract.1 ![4, 0] = true := by
  decide +kernel

example : IntegerMatrix.diagonalSolve smithDiagonal 1 smithDiagonal_contract.1 ![3, 0] = none := by
  decide +kernel


example : IntegerMatrix.diagonalCoordinates smithDiagonal 1 smithDiagonal_contract.1 ![3, 4] =
    IntegerMatrix.diagonalCoordinates smithDiagonal 1 smithDiagonal_contract.1 ![1, 4] := by
  funext row
  fin_cases row
  · change (3 : ZMod 2) = (1 : ZMod 2)
    decide
  · change (4 : ZMod 0) = (4 : ZMod 0)
    rfl

example : IntegerMatrix.diagonalCoordinates smithDiagonal 1 smithDiagonal_contract.1 ![3, 4] ≠
    IntegerMatrix.diagonalCoordinates smithDiagonal 1 smithDiagonal_contract.1 ![1, 5] := by
  intro equal
  have freeCoordinate := congrFun equal 1
  change (4 : ZMod 0) = (5 : ZMod 0) at freeCoordinate
  norm_num at freeCoordinate

example : IntegerMatrix.smithQuotientEquiv singular unitDiagonal leftChange rightChange 1 singular_smith
    (QuotientAddGroup.mk ![2, 3]) = 0 := by
  rw [IntegerMatrix.smithQuotientEquiv_mk,
    IntegerMatrix.smithCoordinates_zero_iff singular unitDiagonal leftChange rightChange 1 singular_smith]
  refine ⟨![1, 0, 0], ?_⟩
  ext row
  fin_cases row <;> norm_num [singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]


private theorem bezout_30_18 : IntegerMatrix.bezoutMatrix 30 18 = !![2, -3; -3, 5] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : IntegerMatrix.bezoutMatrix 30 18 * (!![30, 7; 18, -2] : Matrix (Fin 2) (Fin 2) ℤ) =
    !![6, 20; 0, -31] := by
  rw [bezout_30_18]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

example : IntegerMatrix.bezoutMatrix (-30) 18 = !![1, 2; -3, -5] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : IntegerMatrix.bezoutMatrix 30 (-18) = !![2, 3; 3, 5] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : IntegerMatrix.bezoutMatrix (-30) 0 = !![-1, 0; 0, -1] := by
  ext row column
  fin_cases row <;> fin_cases column <;> decide +kernel

example : IntegerMatrix.bezoutMatrix 0 0 = 1 := by
  simp [IntegerMatrix.bezoutMatrix]


example : (integerRowPair rows columns width).TM0Realizable :=
  (integerRowPair_realizable rows columns width).tm0

example : IntegerMatrix.rowPair (0 : Fin 3) 1 (IntegerMatrix.bezoutMatrix 30 18)
    (!![30, 7; 18, -2; 5, 9] : Matrix (Fin 3) (Fin 2) ℤ) = !![6, 20; 0, -31; 5, 9] := by
  rw [bezout_30_18]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [IntegerMatrix.rowPair]


example : IsUnit (IntegerMatrix.rowPair (0 : Fin 3) 1
    (IntegerMatrix.bezoutMatrix 30 18) (1 : Matrix (Fin 3) (Fin 3) ℤ)).det :=
  IntegerMatrix.rowPair_unimodular 0 1 (by decide) _ (IntegerMatrix.bezoutMatrix_det 30 18)


example : (integerBezoutRows rows columns width).TM0Realizable :=
  (integerBezoutRows_realizable rows columns width).tm0

example : (integerBezoutColumns rows columns width).TM0Realizable :=
  (integerBezoutColumns_realizable rows columns width).tm0

private def eliminationMatrix (first second : ℤ) :
    Matrix (Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
      (Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ))) ℤ := fun row column =>
  if row.val = 0 then (if column.val = 0 then first else 7)
  else if row.val = 1 then (if column.val = 0 then second else -2)
  else if column.val = 0 then 5 else 9

private noncomputable def eliminationArguments (first second : ℤ)
    (firstBound : first.natAbs < 32) (secondBound : second.natAbs < 32) :
    (integerBezoutRows (Parameter := Empty) 3 2 5).Arguments Empty.elim
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨1, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨eliminationMatrix first second, by
      intro row column
      dsimp only [eliminationMatrix]
      split_ifs <;> norm_num <;> assumption⟩

private theorem eliminationArguments_valid (first second : ℤ)
    (firstBound : first.natAbs < 32) (secondBound : second.natAbs < 32) :
    (integerBezoutRows (Parameter := Empty) 3 2 5).precondition Empty.elim
      (eliminationArguments first second firstBound secondBound) := by
  intro equal
  have valueEq := congrArg Fin.val equal
  norm_num [integerBezoutRows, eliminationArguments] at valueEq

example : ((integerBezoutRows (Parameter := Empty) 3 2 5).compute Empty.elim
    ⟨eliminationArguments 30 18 (by norm_num) (by norm_num),
      eliminationArguments_valid 30 18 (by norm_num) (by norm_num)⟩).val =
      (fun row column => if row.val = 0 then (if column.val = 0 then 6 else 20)
        else if row.val = 1 then (if column.val = 0 then 0 else -31)
        else if column.val = 0 then 5 else 9) := by
  change IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (IntegerMatrix.bezoutMatrix 30 18) (eliminationMatrix 30 18) = _
  rw [bezout_30_18]
  ext row column
  by_cases rowZero : row.val = 0 <;> by_cases rowOne : row.val = 1 <;> by_cases columnZero : column.val = 0
  all_goals norm_num [eliminationMatrix, IntegerMatrix.rowPair,
    Matrix.updateRow, Function.update, Fin.ext_iff, rowZero, rowOne, columnZero] at *

example : ((integerBezoutRows (Parameter := Empty) 3 2 5).compute Empty.elim
    ⟨eliminationArguments 0 0 (by norm_num) (by norm_num),
      eliminationArguments_valid 0 0 (by norm_num) (by norm_num)⟩).val = eliminationMatrix 0 0 := by
  simp [integerBezoutRows, eliminationArguments, eliminationMatrix, IntegerMatrix.bezoutMatrix,
    IntegerMatrix.rowPair_one]

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (integerMatrixRenamedView rows columns width names).TM0Realizable :=
  (integerMatrixRenamedView_realizable rows columns width names).tm0

private noncomputable def renamedNegativeArguments (_name : Unit) :
    ((integerMatrixRenamedView (1 : MvPolynomial Empty ℕ) 2 2
      (Empty.elim : Empty → Unit)).inputDomains ()).Carrier (fun _ => 7) :=
  ⟨fun _ _ => -3, by intro row column; norm_num⟩

example : ((integerMatrixRenamedView (1 : MvPolynomial Empty ℕ) 2 2
    (Empty.elim : Empty → Unit)).compute (fun _ => 7)
      ⟨renamedNegativeArguments, trivial⟩).val = (fun _ _ => -3) := rfl

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (integerMatrixOriginalView rows columns width names).TM0Realizable :=
  (integerMatrixOriginalView_realizable rows columns width names).tm0

example {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (sizes : Parameter → ℕ)
    (value : ((Polytime2.EncodedDomain.integerMatrices rows columns width).renameParameters names).Carrier sizes) :
    (integerMatrixOriginalView rows columns width names).compute sizes
      ⟨(fun _ => (integerMatrixRenamedView rows columns width names).compute sizes ⟨(fun _ => value), trivial⟩), trivial⟩ =
        value :=
  (Polytime2.EncodedDomain.integerMatricesRenameEquiv rows columns width names sizes).symm_apply_apply value

end Polytime2.Examples.IntegerMatrices
