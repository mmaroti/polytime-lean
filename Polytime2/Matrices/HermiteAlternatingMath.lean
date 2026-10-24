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

import Polytime2.Matrices.HermiteTriangularMath

/-! # Alternating square Hermite passes

The input is a lower triangular integer matrix with positive diagonal. A row
pass either finishes diagonalization or is followed by the transpose-dual
column pass. The result is lower triangular again, retains both actual bases,
and strictly decreases the diagonal bit measure unless it is diagonal.
-/

namespace Polytime2.IntegerMatrix

private instance diagonalDecidable {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    Decidable (∀ row column : Fin dimension, row ≠ column → matrix row column = 0) := by
  letI : ∀ row : Fin dimension, Decidable (∀ column : Fin dimension, row ≠ column → matrix row column = 0) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- One row pass, followed when necessary by the transpose-dual column pass. -/
def hermiteAlternatingStep {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    Matrix (Fin dimension) (Fin dimension) ℤ ×
      Matrix (Fin dimension) (Fin dimension) ℤ × Matrix (Fin dimension) (Fin dimension) ℤ :=
  let first := (hermiteRowsSweep matrix).1
  if ∀ row column : Fin dimension, row ≠ column → first.1 row column = 0 then (first.1, first.2, 1)
  else
    let second := (hermiteRowsSweep first.1.transpose).1
    (second.1.transpose, first.2, second.2.transpose)

/-- A complete pair of passes returns lower triangular positive input for the next pair. -/
theorem hermiteAlternatingStep_triangular {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index) :
    (hermiteAlternatingStep matrix).1.IsLowerTriangular ∧
      (∀ index, 0 < (hermiteAlternatingStep matrix).1 index index) := by
  have first := hermiteRowsSweep_upper_positive matrix lower positive
  have second := hermiteRowsSweep_upper_positive (hermiteRowsSweep matrix).1.1.transpose
    first.1.transpose first.2
  unfold hermiteAlternatingStep
  dsimp only
  split_ifs with diagonal
  · refine ⟨?_, first.2⟩
    intro row column before
    exact diagonal row column (ne_of_lt before)
  · exact ⟨second.1.transpose, second.2⟩

/-- Both returned bases retain the original presentation and are unimodular. -/
theorem hermiteAlternatingStep_preserves {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    (hermiteAlternatingStep matrix).2.1 * matrix * (hermiteAlternatingStep matrix).2.2 =
      (hermiteAlternatingStep matrix).1 ∧
      IsUnit (hermiteAlternatingStep matrix).2.1.det ∧
      IsUnit (hermiteAlternatingStep matrix).2.2.det := by
  have first := hermiteRowsSweep_correct matrix
  have second := hermiteRowsSweep_correct (hermiteRowsSweep matrix).1.1.transpose
  unfold hermiteAlternatingStep
  dsimp only
  split_ifs
  · exact ⟨by simpa only [Matrix.mul_one] using first.1, first.2.1, by simp⟩
  · refine ⟨?_, first.2.1, ?_⟩
    · have equation := congrArg Matrix.transpose second.1
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, first.1] using equation
    · simpa only [Matrix.det_transpose] using second.2.1

/-- A non-diagonal output of the pair forces a strict decrease of the input bit measure. -/
theorem hermiteAlternatingStep_diagonal_or_progress {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index) :
    (∀ row column, row ≠ column → (hermiteAlternatingStep matrix).1 row column = 0) ∨
      (diagonalPotential (fun row => ((hermiteAlternatingStep matrix).1 row row).natAbs)).size <
        (diagonalPotential (fun row => (matrix row row).natAbs)).size := by
  have first := hermiteRowsSweep_upper_positive matrix lower positive
  have progress := hermiteRowsSweep_diagonal_or_progress matrix lower positive
  have second := hermiteRowsPrefix_canonical (hermiteRowsSweep matrix).1.1.transpose
    first.1.transpose first.2 _ (by rfl)
  unfold hermiteAlternatingStep
  dsimp only
  split_ifs with diagonal
  · exact Or.inl diagonal
  · right
    have strict := progress.resolve_left diagonal
    exact second.2.2.trans_lt strict

/-- Bounded alternating reduction, stopping on diagonal input and composing both actual bases. -/
def hermiteAlternatingRun {dimension : ℕ} : ℕ → Matrix (Fin dimension) (Fin dimension) ℤ →
    Matrix (Fin dimension) (Fin dimension) ℤ ×
      Matrix (Fin dimension) (Fin dimension) ℤ × Matrix (Fin dimension) (Fin dimension) ℤ
  | 0, matrix => (matrix, 1, 1)
  | fuel + 1, matrix =>
    if ∀ row column, row ≠ column → matrix row column = 0 then (matrix, 1, 1)
    else
      let step := hermiteAlternatingStep matrix
      let rest := hermiteAlternatingRun fuel step.1
      (rest.1, rest.2.1 * step.2.1, step.2.2 * rest.2.2)

/-- Diagonal input is retained exactly, for any budget. -/
theorem hermiteAlternatingRun_of_diagonal {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (diagonal : ∀ row column, row ≠ column → matrix row column = 0) :
    hermiteAlternatingRun fuel matrix = (matrix, 1, 1) := by
  cases fuel <;> simp only [hermiteAlternatingRun, ite_eq_left diagonal]

/-- Extend a bounded run at its final state, composing both bases in forward order. -/
theorem hermiteAlternatingRun_succ_right {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    hermiteAlternatingRun (fuel + 1) matrix =
      let current := hermiteAlternatingRun fuel matrix
      if ∀ row column, row ≠ column → current.1 row column = 0 then current else
        let step := hermiteAlternatingStep current.1
        (step.1, step.2.1 * current.2.1, current.2.2 * step.2.2) := by
  classical
  induction fuel generalizing matrix with
  | zero => simp [hermiteAlternatingRun]
  | succ fuel induction =>
    by_cases diagonal : ∀ row column, row ≠ column → matrix row column = 0
    · simp only [hermiteAlternatingRun_of_diagonal _ matrix diagonal]
      exact (ite_eq_left diagonal).symm
    · let step := hermiteAlternatingStep matrix
      let current := hermiteAlternatingRun fuel step.1
      have previous : hermiteAlternatingRun (fuel + 1) matrix =
          (current.1, current.2.1 * step.2.1, step.2.2 * current.2.2) := by
        rw [hermiteAlternatingRun, ite_eq_right diagonal]
      rw [previous]
      rw [hermiteAlternatingRun, ite_eq_right diagonal]
      change ((hermiteAlternatingRun (fuel + 1) step.1).1,
        (hermiteAlternatingRun (fuel + 1) step.1).2.1 * step.2.1,
        step.2.2 * (hermiteAlternatingRun (fuel + 1) step.1).2.2) = _
      rw [induction step.1]
      dsimp only
      split_ifs <;> simp [current, Matrix.mul_assoc]

/-- Advance a current matrix and its accumulated bases, retaining stopped states. -/
def hermiteAlternatingAdvance {dimension : ℕ}
    (current : Matrix (Fin dimension) (Fin dimension) ℤ ×
      Matrix (Fin dimension) (Fin dimension) ℤ × Matrix (Fin dimension) (Fin dimension) ℤ) :=
  if ∀ row column, row ≠ column → current.1 row column = 0 then current else
    let step := hermiteAlternatingStep current.1
    (step.1, step.2.1 * current.2.1, current.2.2 * step.2.2)

/-- Forward accumulation and the recursive run return exactly the same matrices. -/
theorem hermiteAlternatingRun_eq_iterate {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    hermiteAlternatingRun fuel matrix = hermiteAlternatingAdvance^[fuel] (matrix, 1, 1) := by
  induction fuel with
  | zero => rfl
  | succ fuel induction =>
    rw [hermiteAlternatingRun_succ_right, Function.iterate_succ_apply', ← induction]
    rfl

/-- Every bounded run retains its presentation and both unimodular bases, even at zero budget. -/
theorem hermiteAlternatingRun_preserves {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    (hermiteAlternatingRun fuel matrix).2.1 * matrix * (hermiteAlternatingRun fuel matrix).2.2 =
      (hermiteAlternatingRun fuel matrix).1 ∧
      IsUnit (hermiteAlternatingRun fuel matrix).2.1.det ∧
      IsUnit (hermiteAlternatingRun fuel matrix).2.2.det := by
  induction fuel generalizing matrix with
  | zero => simp [hermiteAlternatingRun]
  | succ fuel induction =>
    have step := hermiteAlternatingStep_preserves matrix
    have rest := induction (hermiteAlternatingStep matrix).1
    simp only [hermiteAlternatingRun]
    split_ifs
    · simp
    · refine ⟨?_, ?_, ?_⟩
      · simpa only [Matrix.mul_assoc, ← step.1] using rest.1
      · rw [Matrix.det_mul]
        exact rest.2.1.mul step.2.1
      · rw [Matrix.det_mul]
        exact step.2.2.mul rest.2.2

/-- The bounded run preserves the positive triangular input contract. -/
theorem hermiteAlternatingRun_triangular {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index) :
    (hermiteAlternatingRun fuel matrix).1.IsLowerTriangular ∧
      (∀ index, 0 < (hermiteAlternatingRun fuel matrix).1 index index) := by
  induction fuel generalizing matrix with
  | zero => exact ⟨lower, positive⟩
  | succ fuel induction =>
    have step := hermiteAlternatingStep_triangular matrix lower positive
    simp only [hermiteAlternatingRun]
    split_ifs
    · exact ⟨lower, positive⟩
    · exact induction _ step.1 step.2

/-- More fuel than the input measure suffices for a diagonal result. -/
theorem hermiteAlternatingRun_diagonal {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (budget : (diagonalPotential (fun row => (matrix row row).natAbs)).size < fuel) :
    ∀ row column, row ≠ column → (hermiteAlternatingRun fuel matrix).1 row column = 0 := by
  induction fuel generalizing matrix with
  | zero => omega
  | succ fuel induction =>
    by_cases diagonal : ∀ row column, row ≠ column → matrix row column = 0
    · rw [hermiteAlternatingRun_of_diagonal _ _ diagonal]
      exact diagonal
    · simp only [hermiteAlternatingRun, ite_eq_right diagonal]
      have step := hermiteAlternatingStep_triangular matrix lower positive
      rcases hermiteAlternatingStep_diagonal_or_progress matrix lower positive with finished | strict
      · rw [hermiteAlternatingRun_of_diagonal _ _ finished]
        exact finished
      · exact induction _ step.1 step.2 (by omega)

/-- A dimension and input-width budget suffices, including the empty matrix. -/
theorem hermiteAlternatingRun_polynomial_budget {dimension : ℕ} (width : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, row ≠ column →
      (hermiteAlternatingRun (width * dimension * dimension + 2) matrix).1 row column = 0 := by
  apply hermiteAlternatingRun_diagonal _ matrix lower positive
  have bound := diagonalPotential_initial_size_bound width (fun row => (matrix row row).natAbs)
    (fun row => entryBound row row)
  omega

end Polytime2.IntegerMatrix
