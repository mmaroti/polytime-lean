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

import Polytime2.Matrices.DiagonalCleanupMath
import Polytime2.Matrices.RowPairMath

/-! # Actual basis transformations for diagonal cleanup

The active square block uses the already proved gcd/lcm cleanup schedule.
Each pair replacement applies its explicit left and right two-by-two matrices
to the accumulated bases, retaining actual integer matrices throughout.
-/

namespace Polytime2.IntegerMatrix

variable {Index : Type} [DecidableEq Index]

/-- Each coupled pair repair adds at most `4 * diagonalWidth + 3` basis bits. -/
theorem diagonalPair_basis_bound (diagonalWidth basisWidth : ℕ) (firstIndex secondIndex : Index)
    (first second : ℤ) (left right : Matrix Index Index ℤ)
    (firstBound : first.natAbs < 2 ^ diagonalWidth) (secondBound : second.natAbs < 2 ^ diagonalWidth)
    (leftBound : ∀ row column, (left row column).natAbs < 2 ^ basisWidth)
    (rightBound : ∀ row column, (right row column).natAbs < 2 ^ basisWidth) :
    (∀ row column, (rowPair firstIndex secondIndex (bezoutMatrix first second) left row column).natAbs <
      2 ^ (basisWidth + (4 * diagonalWidth + 3))) ∧
    (∀ row column, (columnPair firstIndex secondIndex (diagonalPairRight first second) right row column).natAbs <
      2 ^ (basisWidth + (4 * diagonalWidth + 3))) := by
  have leftCoefficient := bezoutMatrix_bound diagonalWidth first second firstBound secondBound
  have rightCoefficient := diagonalPairRight_bound diagonalWidth first second firstBound secondBound
  have nextLeft := rowPair_bound_of_widths (2 * diagonalWidth + 1) basisWidth firstIndex secondIndex
    (bezoutMatrix first second) left leftCoefficient leftBound
  have nextRight := rowPair_bound_of_widths (2 * (2 * diagonalWidth + 1)) basisWidth firstIndex secondIndex
    (diagonalPairRight first second).transpose right.transpose
    (fun row column => rightCoefficient column row) (fun row column => rightBound column row)
  have leftWidth : (2 * diagonalWidth + 1) + basisWidth + 1 ≤ basisWidth + (4 * diagonalWidth + 3) := by omega
  have rightWidth : (2 * (2 * diagonalWidth + 1)) + basisWidth + 1 = basisWidth + (4 * diagonalWidth + 3) := by omega
  refine ⟨fun row column => (nextLeft row column).trans_le (pow_le_pow_right₀ (by decide) leftWidth), ?_⟩
  intro row column
  simpa only [columnPair, Matrix.transpose_apply, rightWidth] using nextRight column row

/-- A two-coordinate diagonal identity lifts to the full active block. -/
theorem rowPair_diagonal_pair (diagonal : Index → ℤ) (first second : Index)
    (different : first ≠ second) (left right : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℤ)
    (localEquation : left * !![diagonal first, 0; 0, diagonal second] * right = !![a, 0; 0, b]) :
    (rowPair first second right.transpose (rowPair first second left (Matrix.diagonal diagonal)).transpose).transpose =
      Matrix.diagonal (Function.update (Function.update diagonal first a) second b) := by
  have entry00 := congrFun (congrFun localEquation 0) 0
  have entry01 := congrFun (congrFun localEquation 0) 1
  have entry10 := congrFun (congrFun localEquation 1) 0
  have entry11 := congrFun (congrFun localEquation 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at entry00 entry01 entry10 entry11
  ext row column
  by_cases rowFirst : row = first
  · subst row
    by_cases columnFirst : column = first
    · subst column
      simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply, different, different.symm,
        Matrix.transpose_apply]
      linear_combination entry00
    · by_cases columnSecond : column = second
      · subst column
        simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply, different, different.symm,
          Matrix.transpose_apply]
        linear_combination entry01
      · simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply, different,
          columnFirst, (Ne.symm columnFirst), columnSecond, (Ne.symm columnSecond), Matrix.transpose_apply]
  · by_cases rowSecond : row = second
    · subst row
      by_cases columnFirst : column = first
      · subst column
        simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply, different, different.symm,
          Matrix.transpose_apply]
        linear_combination entry10
      · by_cases columnSecond : column = second
        · subst column
          simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply, different, different.symm,
            Matrix.transpose_apply]
          linear_combination entry11
        · simp [rowPair, Matrix.updateRow, Function.update, Matrix.diagonal_apply,
            columnFirst, (Ne.symm columnFirst), columnSecond, (Ne.symm columnSecond), Matrix.transpose_apply]
    · by_cases columnFirst : column = first <;> by_cases columnSecond : column = second
      all_goals simp [rowPair, Matrix.updateRow, Matrix.of_apply, Function.update, Matrix.diagonal_apply,
        rowFirst, rowSecond, columnFirst, columnSecond, different, Matrix.transpose_apply]

variable {length : ℕ}

/-- The embedded pair transformations change precisely the selected diagonal entries. -/
theorem diagonalNormalizePair_equation (diagonal : Fin length → ℕ) (first second : Fin length)
    (different : first ≠ second) :
    let left := rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) 1
    let right := (rowPair first second (diagonalPairRight (diagonal first) (diagonal second)).transpose 1).transpose
    left * Matrix.diagonal (fun index => (diagonal index : ℤ)) * right =
      Matrix.diagonal (fun index => (diagonalNormalizePair diagonal first second index : ℤ)) := by
  have lifted := rowPair_diagonal_pair (fun index => (diagonal index : ℤ)) first second different
    (bezoutMatrix (diagonal first) (diagonal second)) (diagonalPairRight (diagonal first) (diagonal second))
    (Nat.gcd (diagonal first) (diagonal second)) (Nat.lcm (diagonal first) (diagonal second))
    (diagonalPair_nat_equation (diagonal first) (diagonal second))
  rw [rowPair_eq_mul first second _ (Matrix.diagonal _), rowPair_eq_mul first second _ _] at lifted
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at lifted ⊢
  refine lifted.trans ?_
  congr 1
  funext index
  by_cases atFirst : index = first <;> by_cases atSecond : index = second
  all_goals simp [diagonalNormalizePair, Function.update, atFirst, atSecond]

/-- Retain the diagonal and both actual basis matrices through the same bounded schedule. -/
def diagonalCleanupWithBases : ℕ → (Fin length → ℕ) → Matrix (Fin length) (Fin length) ℤ →
    Matrix (Fin length) (Fin length) ℤ → (Fin length → ℕ) ×
      (Matrix (Fin length) (Fin length) ℤ × Matrix (Fin length) (Fin length) ℤ)
  | 0, diagonal, left, right => (diagonal, (left, right))
  | remaining + 1, diagonal, left, right => match diagonalViolation diagonal with
    | none => (diagonal, (left, right))
    | some (first, second) => diagonalCleanupWithBases remaining (diagonalNormalizePair diagonal first second)
        (rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) left)
        (columnPair first second (diagonalPairRight (diagonal first) (diagonal second)) right)

/-- Append one cleanup iteration after any already computed prefix. -/
theorem diagonalCleanupWithBases_succ_last (fuel : ℕ) (diagonal : Fin length → ℕ)
    (left right : Matrix (Fin length) (Fin length) ℤ) :
    diagonalCleanupWithBases (fuel + 1) diagonal left right =
      let prefixState := diagonalCleanupWithBases fuel diagonal left right
      diagonalCleanupWithBases 1 prefixState.1 prefixState.2.1 prefixState.2.2 := by
  induction fuel generalizing diagonal left right with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    cases found : diagonalViolation diagonal with
    | none => simp only [diagonalCleanupWithBases, found]
    | some pair =>
      obtain ⟨first, second⟩ := pair
      simpa only [diagonalCleanupWithBases, found] using inductionHypothesis
        (diagonalNormalizePair diagonal first second)
        (rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) left)
        (columnPair first second (diagonalPairRight (diagonal first) (diagonal second)) right)

theorem diagonalCleanupWithBases_diagonal (fuel : ℕ) (diagonal : Fin length → ℕ)
    (left right : Matrix (Fin length) (Fin length) ℤ) :
    (diagonalCleanupWithBases fuel diagonal left right).1 = diagonalCleanup fuel diagonal := by
  induction fuel generalizing diagonal left right with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    cases found : diagonalViolation diagonal with
    | none => simp [diagonalCleanupWithBases, diagonalCleanup, found]
    | some pair =>
      obtain ⟨first, second⟩ := pair
      simpa only [diagonalCleanupWithBases, diagonalCleanup, found] using inductionHypothesis
        (diagonalNormalizePair diagonal first second) _ _

/-- One replacement updates both bases while preserving the original-to-current equation. -/
theorem diagonalNormalizePair_preserves (diagonal : Fin length → ℕ) (first second : Fin length)
    (different : first ≠ second) (original left right : Matrix (Fin length) (Fin length) ℤ)
    (equation : left * original * right = Matrix.diagonal (fun index => (diagonal index : ℤ)))
    (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) :
    let updatedLeft := rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) left
    let updatedRight := (columnPair first second (diagonalPairRight (diagonal first) (diagonal second)) right)
    updatedLeft * original * updatedRight = Matrix.diagonal (fun index => (diagonalNormalizePair diagonal first second index : ℤ)) ∧
      IsUnit updatedLeft.det ∧ IsUnit updatedRight.det := by
  have leftEquation := rowPair_eq_mul first second (bezoutMatrix (diagonal first) (diagonal second)) left
  have rightEquation := columnPair_eq_mul first second (diagonalPairRight (diagonal first) (diagonal second)) right
  dsimp only
  rw [leftEquation, rightEquation]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) 1 *
          (left * original * right) *
          (rowPair first second (diagonalPairRight (diagonal first) (diagonal second)).transpose 1).transpose := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [equation]; exact diagonalNormalizePair_equation diagonal first second different
  · rw [Matrix.det_mul]
    exact (rowPair_unimodular first second different _ (bezoutMatrix_det _ _)).mul leftUnit
  · rw [Matrix.det_mul, Matrix.det_transpose]
    exact rightUnit.mul (rowPair_unimodular first second different _
      (by rw [Matrix.det_transpose, diagonalPairRight_det]))

/-- Every accumulated state retains actual unimodular bases, even before the loop finishes. -/
theorem diagonalCleanupWithBases_preserves (fuel : ℕ) (diagonal : Fin length → ℕ)
    (original left right : Matrix (Fin length) (Fin length) ℤ)
    (equation : left * original * right = Matrix.diagonal (fun index => (diagonal index : ℤ)))
    (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) :
    let result := diagonalCleanupWithBases fuel diagonal left right
    result.2.1 * original * result.2.2 = Matrix.diagonal (fun index => (result.1 index : ℤ)) ∧
      IsUnit result.2.1.det ∧ IsUnit result.2.2.det := by
  induction fuel generalizing diagonal left right with
  | zero => exact ⟨equation, leftUnit, rightUnit⟩
  | succ fuel inductionHypothesis =>
    cases found : diagonalViolation diagonal with
    | none => simpa only [diagonalCleanupWithBases, found] using And.intro equation (And.intro leftUnit rightUnit)
    | some pair =>
      obtain ⟨first, second⟩ := pair
      have failure := diagonalViolation_some diagonal first second found
      have different : first ≠ second := by intro same; subst second; omega
      have updated := diagonalNormalizePair_preserves diagonal first second different original left right equation leftUnit rightUnit
      simpa only [diagonalCleanupWithBases, found] using inductionHypothesis
        (diagonalNormalizePair diagonal first second) _ _ updated.1 updated.2.1 updated.2.2

/-- A positive divisibility chain is a Smith diagonal for the entire active square block. -/
theorem diagonal_isSmithDiagonal (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (chain : diagonalDivisibilityChain diagonal) :
    IsSmithDiagonal (Matrix.diagonal (fun index => (diagonal index : ℤ))) length := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro row column different
    have unequal : row ≠ column := by intro same; subst column; exact different rfl
    simp [unequal]
  · intro row column inactive
    have bounded := row.isLt
    omega
  · intro row column same active
    have equal : row = column := Fin.ext same
    subst column
    simpa using positive row
  · intro first second consecutive active
    have divides := chain (first.castLE (Nat.min_le_left length length))
      (second.castLE (Nat.min_le_left length length)) consecutive
    simpa [diagonalEntry] using (Int.natCast_dvd_natCast.mpr divides)

/-- The bounded active-block cleanup returns actual matrices satisfying the Smith contract. -/
theorem diagonalCleanupWithBases_isSmithForm (width : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := diagonalCleanupWithBases (width * length * length + 1) diagonal 1 1
    IsSmithForm (Matrix.diagonal (fun index => (diagonal index : ℤ)))
      (Matrix.diagonal (fun index => (result.1 index : ℤ))) result.2.1 result.2.2 length := by
  have invariant := diagonalCleanupWithBases_preserves (width * length * length + 1) diagonal
    (Matrix.diagonal (fun index => (diagonal index : ℤ))) 1 1 (by simp) (by simp) (by simp)
  have output := diagonalCleanup_polynomial width diagonal positive entryBound
  refine ⟨invariant.1, invariant.2.1, invariant.2.2, ?_⟩
  rw [diagonalCleanupWithBases_diagonal]
  exact diagonal_isSmithDiagonal _ output.2.1 output.1

end Polytime2.IntegerMatrix
