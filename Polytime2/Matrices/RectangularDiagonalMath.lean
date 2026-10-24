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

import Polytime2.Matrices.DiagonalBoundsMath
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Extending diagonal cleanup to rectangular matrices

The mathematical dimensions are independent row and column counts, with an
active length bounded by both. A rectangular diagonal has the supplied active
entries followed by zeros. An active change of basis extends by identity on
the unused coordinates, preserving determinant and the transformation equation.
-/

namespace Polytime2.IntegerMatrix

variable {rows columns rank : ℕ}

/-- The ordinary rectangular matrix with these active diagonal entries and zeros elsewhere. -/
def rectangularDiagonal (rows columns : ℕ) (diagonal : Fin rank → ℕ) : Matrix (Fin rows) (Fin columns) ℤ :=
  fun row column => if row.val = column.val then
    if active : row.val < rank then (diagonal ⟨row.val, active⟩ : ℤ) else 0
  else 0

private def splitIndex (rank dimension : ℕ) (within : rank ≤ dimension) :
    Fin rank ⊕ Fin (dimension - rank) ≃ Fin dimension :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le within))

private theorem splitIndex_left_val (dimension : ℕ) (within : rank ≤ dimension) (index : Fin rank) :
    (splitIndex rank dimension within (.inl index)).val = index.val := rfl

private theorem splitIndex_right_val (dimension : ℕ) (within : rank ≤ dimension) (index : Fin (dimension - rank)) :
    (splitIndex rank dimension within (.inr index)).val = rank + index.val := rfl

/-- Place a square active block in a rectangular matrix, with zero inactive strips. -/
def rectangularBlock (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (matrix : Matrix (Fin rank) (Fin rank) ℤ) : Matrix (Fin rows) (Fin columns) ℤ :=
  Matrix.reindexLinearEquiv ℤ ℤ (splitIndex rank rows rowBound) (splitIndex rank columns columnBound)
    (Matrix.fromBlocks matrix 0 0 0)

/-- The rectangular block reads active entries and is zero on both inactive strips. -/
theorem rectangularBlock_apply (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (matrix : Matrix (Fin rank) (Fin rank) ℤ) (row : Fin rows) (column : Fin columns) :
    rectangularBlock rowBound columnBound matrix row column =
      if rowActive : row.val < rank then
        if columnActive : column.val < rank then matrix ⟨row.val, rowActive⟩ ⟨column.val, columnActive⟩ else 0
      else 0 := by
  obtain ⟨row, rfl⟩ := (splitIndex rank rows rowBound).surjective row
  obtain ⟨column, rfl⟩ := (splitIndex rank columns columnBound).surjective column
  change Matrix.fromBlocks matrix 0 0 0
    ((splitIndex rank rows rowBound).symm (splitIndex rank rows rowBound row))
    ((splitIndex rank columns columnBound).symm (splitIndex rank columns columnBound column)) = _
  simp only [Equiv.symm_apply_apply]
  cases row with
  | inl row =>
    cases column with
    | inl column => simp [Matrix.fromBlocks, splitIndex_left_val, row.isLt, column.isLt]
    | inr column =>
      have outside : ¬rank + column.val < rank := by omega
      simp [Matrix.fromBlocks, splitIndex_left_val, splitIndex_right_val, row.isLt, outside]
  | inr row =>
    have outside : ¬rank + row.val < rank := by omega
    cases column <;> simp [Matrix.fromBlocks, splitIndex_right_val, outside]

/-- Every matrix supported on its active square block is its zero rectangular extension. -/
theorem rectangularBlock_submatrix (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (matrix : Matrix (Fin rows) (Fin columns) ℤ)
    (zeroRows : ∀ row : Fin rows, rank ≤ row.val → matrix row = 0)
    (zeroColumns : ∀ column : Fin columns, rank ≤ column.val → matrix.transpose column = 0) :
    rectangularBlock rowBound columnBound (matrix.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)) = matrix := by
  ext row column
  rw [rectangularBlock_apply]
  split_ifs with rowActive columnActive
  · rfl
  · exact (congrFun (zeroColumns column (by omega)) row).symm
  · exact (congrFun (zeroRows row (by omega)) column).symm

/-- Zero extension preserves any magnitude width, including width zero. -/
theorem rectangularBlock_bound (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ row column, (rectangularBlock rowBound columnBound matrix row column).natAbs < 2 ^ width := by
  intro row column
  rw [rectangularBlock_apply]
  split_ifs
  · exact entryBound _ _
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

private theorem rectangularDiagonal_block (diagonal : Fin rank → ℕ)
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns) :
    Matrix.reindexLinearEquiv ℤ ℤ (splitIndex rank rows rowBound) (splitIndex rank columns columnBound)
      (Matrix.fromBlocks (Matrix.diagonal (fun index => (diagonal index : ℤ))) 0 0 0) =
        rectangularDiagonal rows columns diagonal := by
  change rectangularBlock rowBound columnBound _ = _
  ext row column
  rw [rectangularBlock_apply]
  by_cases same : row.val = column.val
  · by_cases active : column.val < rank <;> simp [rectangularDiagonal, same, active]
  · simp [rectangularDiagonal, Fin.ext_iff, same]

/-- A positive diagonal active matrix extends to the ordinary rectangular diagonal. -/
theorem rectangularBlock_of_positive_diagonal (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (diagonal : ∀ row column, row ≠ column → matrix row column = 0)
    (positive : ∀ index, 0 < matrix index index) :
    rectangularBlock rowBound columnBound matrix =
      rectangularDiagonal rows columns (fun index => (matrix index index).natAbs) := by
  have equal : matrix = Matrix.diagonal (fun index => ((matrix index index).natAbs : ℤ)) := by
    ext row column
    by_cases same : row = column
    · subst column
      simp only [Matrix.diagonal_apply_eq, Int.natCast_natAbs, abs_of_pos (positive row)]
    · change matrix row column = if row = column then _ else 0
      rw [ite_eq_right same]
      exact diagonal row column same
  calc
    rectangularBlock rowBound columnBound matrix =
        rectangularBlock rowBound columnBound (Matrix.diagonal (fun index => ((matrix index index).natAbs : ℤ))) :=
      congrArg (rectangularBlock rowBound columnBound) equal
    _ = _ := rectangularDiagonal_block _ rowBound columnBound

/-- Extend an active square basis by the identity, using the full mathematical dimension. -/
def extendDiagonalBasis (dimension : ℕ) (within : rank ≤ dimension)
    (basis : Matrix (Fin rank) (Fin rank) ℤ) : Matrix (Fin dimension) (Fin dimension) ℤ :=
  Matrix.reindexLinearEquiv ℤ ℤ (splitIndex rank dimension within) (splitIndex rank dimension within)
    (Matrix.fromBlocks basis 0 0 1)

/-- The extended basis reads the active block and acts as identity on its complement. -/
theorem extendDiagonalBasis_apply (dimension : ℕ) (within : rank ≤ dimension)
    (basis : Matrix (Fin rank) (Fin rank) ℤ) (row column : Fin dimension) :
    extendDiagonalBasis dimension within basis row column =
      if rowActive : row.val < rank then
        if columnActive : column.val < rank then basis ⟨row.val, rowActive⟩ ⟨column.val, columnActive⟩ else 0
      else if row.val = column.val then 1 else 0 := by
  obtain ⟨row, rfl⟩ := (splitIndex rank dimension within).surjective row
  obtain ⟨column, rfl⟩ := (splitIndex rank dimension within).surjective column
  change (Matrix.fromBlocks basis 0 0 1
    ((splitIndex rank dimension within).symm (splitIndex rank dimension within row))
    ((splitIndex rank dimension within).symm (splitIndex rank dimension within column))) = _
  simp only [Equiv.symm_apply_apply]
  cases row with
  | inl row =>
    cases column with
    | inl column => simp [Matrix.fromBlocks, splitIndex_left_val, row.isLt, column.isLt]
    | inr column =>
      have outside : ¬rank + column.val < rank := by omega
      simp [Matrix.fromBlocks, splitIndex_left_val, splitIndex_right_val, row.isLt, outside]
  | inr row =>
    have outside : ¬rank + row.val < rank := by omega
    cases column with
    | inl column =>
      have different : rank + row.val ≠ column.val := by have := column.isLt; omega
      simp [Matrix.fromBlocks, splitIndex_left_val, splitIndex_right_val, outside, different]
    | inr column =>
      simp [Matrix.fromBlocks, splitIndex_right_val, outside, Matrix.one_apply, Fin.ext_iff]

theorem extendDiagonalBasis_det (dimension : ℕ) (within : rank ≤ dimension)
    (basis : Matrix (Fin rank) (Fin rank) ℤ) :
    (extendDiagonalBasis dimension within basis).det = basis.det := by
  rw [extendDiagonalBasis, Matrix.det_reindexLinearEquiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem rectangularDiagonal_isSmithDiagonal (diagonal : Fin rank → ℕ)
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (positive : ∀ index, 0 < diagonal index) (chain : diagonalDivisibilityChain diagonal) :
    IsSmithDiagonal (rectangularDiagonal rows columns diagonal) rank := by
  refine ⟨Nat.le_min.mpr ⟨rowBound, columnBound⟩, ?_, ?_, ?_, ?_⟩
  · intro row column different
    simp [rectangularDiagonal, different]
  · intro row column inactive
    simp [rectangularDiagonal, show ¬row.val < rank by omega]
  · intro row column same active
    have columnActive : column.val < rank := by omega
    have valuePositive : (0 : ℤ) < diagonal ⟨column.val, columnActive⟩ := by
      exact_mod_cast positive ⟨column.val, columnActive⟩
    simpa [rectangularDiagonal, same, columnActive] using valuePositive
  · intro first second consecutive active
    have firstActive : first.val < rank := by omega
    have divides := chain ⟨first.val, firstActive⟩ ⟨second.val, active⟩ consecutive
    simpa [diagonalEntry, rectangularDiagonal, firstActive, active] using Int.natCast_dvd_natCast.mpr divides

/-- Identity extensions transport an arbitrary active-block equation to full rectangular dimensions. -/
theorem extendDiagonalBasis_block_equation (original current : Matrix (Fin rank) (Fin rank) ℤ)
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (left right : Matrix (Fin rank) (Fin rank) ℤ) (equation : left * original * right = current) :
    extendDiagonalBasis rows rowBound left * rectangularBlock rowBound columnBound original *
      extendDiagonalBasis columns columnBound right = rectangularBlock rowBound columnBound current := by
  unfold rectangularBlock extendDiagonalBasis
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
  apply congrArg
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_one]
  rw [equation]

/-- Active transformations extend to the independent full row and column dimensions. -/
theorem extendDiagonalBasis_equation (diagonal normalized : Fin rank → ℕ)
    (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (left right : Matrix (Fin rank) (Fin rank) ℤ)
    (equation : left * Matrix.diagonal (fun index => (diagonal index : ℤ)) * right =
      Matrix.diagonal (fun index => (normalized index : ℤ))) :
    extendDiagonalBasis rows rowBound left * rectangularDiagonal rows columns diagonal *
      extendDiagonalBasis columns columnBound right = rectangularDiagonal rows columns normalized := by
  simpa only [rectangularBlock, rectangularDiagonal_block] using
    extendDiagonalBasis_block_equation _ _ rowBound columnBound left right equation

/-- Adding an identity block preserves any magnitude width that can contain one. -/
theorem extendDiagonalBasis_bound (dimension width : ℕ) (within : rank ≤ dimension)
    (widthPositive : 0 < width) (basis : Matrix (Fin rank) (Fin rank) ℤ)
    (basisBound : ∀ row column, (basis row column).natAbs < 2 ^ width) :
    ∀ row column, (extendDiagonalBasis dimension within basis row column).natAbs < 2 ^ width := by
  intro row column
  obtain ⟨row, rfl⟩ := (splitIndex rank dimension within).surjective row
  obtain ⟨column, rfl⟩ := (splitIndex rank dimension within).surjective column
  change (Matrix.fromBlocks basis 0 0 1
    ((splitIndex rank dimension within).symm (splitIndex rank dimension within row))
    ((splitIndex rank dimension within).symm (splitIndex rank dimension within column))).natAbs < _
  simp only [Equiv.symm_apply_apply]
  cases row with
  | inl row =>
    cases column with
    | inl column => exact basisBound row column
    | inr column => simp [Matrix.fromBlocks]
  | inr row =>
    cases column with
    | inl column => simp [Matrix.fromBlocks]
    | inr column =>
      have oneBound : 1 < 2 ^ width := Nat.one_lt_two_pow (Nat.ne_of_gt widthPositive)
      by_cases same : row = column <;> simp [Matrix.fromBlocks, same, oneBound]

/-- Rectangular zero padding preserves the active diagonal entry bound. -/
theorem rectangularDiagonal_bound (width : ℕ) (diagonal : Fin rank → ℕ)
    (entryBound : ∀ index, diagonal index < 2 ^ width) :
    ∀ row column, (rectangularDiagonal rows columns diagonal row column).natAbs < 2 ^ width := by
  intro row column
  dsimp only [rectangularDiagonal]
  split_ifs with same active
  · simpa using entryBound ⟨row.val, active⟩
  · simp
  · simp

/-- Clean up an already diagonal rectangular matrix, retaining full-sized bases. -/
def rectangularDiagonalCleanup (rows columns : ℕ) (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (diagonal : Fin rank → ℕ) : Matrix (Fin rows) (Fin columns) ℤ ×
      (Matrix (Fin rows) (Fin rows) ℤ × Matrix (Fin columns) (Fin columns) ℤ) :=
  let result := diagonalCleanupWithBases (width * rank * rank + 1) diagonal 1 1
  (rectangularDiagonal rows columns result.1,
    (extendDiagonalBasis rows rowBound result.2.1, extendDiagonalBasis columns columnBound result.2.2))

/-- The cleanup contract now covers rank-deficient rectangular matrices and empty dimensions. -/
theorem rectangularDiagonalCleanup_isSmithForm (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (diagonal : Fin rank → ℕ) (positive : ∀ index, 0 < diagonal index)
    (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := rectangularDiagonalCleanup rows columns rowBound columnBound width diagonal
    IsSmithForm (rectangularDiagonal rows columns diagonal) result.1 result.2.1 result.2.2 rank := by
  have active := diagonalCleanupWithBases_isSmithForm width diagonal positive entryBound
  have cleaned := diagonalCleanup_polynomial width diagonal positive entryBound
  dsimp only [rectangularDiagonalCleanup]
  refine ⟨extendDiagonalBasis_equation diagonal _ rowBound columnBound _ _ active.1, ?_, ?_, ?_⟩
  · rw [extendDiagonalBasis_det]
    exact active.2.1
  · rw [extendDiagonalBasis_det]
    exact active.2.2.1
  · rw [diagonalCleanupWithBases_diagonal]
    exact rectangularDiagonal_isSmithDiagonal _ rowBound columnBound cleaned.2.1 cleaned.1

/-- The rectangular bases satisfy exactly the same polynomial width bound as the active bases. -/
theorem rectangularDiagonalCleanup_basis_bound (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (diagonal : Fin rank → ℕ) (positive : ∀ index, 0 < diagonal index)
    (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := rectangularDiagonalCleanup rows columns rowBound columnBound width diagonal
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ (1 + (width * rank * rank + 1) * (4 * (width * rank + 1) + 3))) ∧
    (∀ row column, (result.2.2 row column).natAbs <
      2 ^ (1 + (width * rank * rank + 1) * (4 * (width * rank + 1) + 3))) := by
  have active := diagonalCleanupWithBases_polynomial_bound width diagonal positive entryBound
  exact ⟨extendDiagonalBasis_bound rows _ rowBound (by omega) _ active.1,
    extendDiagonalBasis_bound columns _ columnBound (by omega) _ active.2⟩

/-- The returned rectangular diagonal has the same polynomial entry bound as its active part. -/
theorem rectangularDiagonalCleanup_entry_bound (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (diagonal : Fin rank → ℕ) (positive : ∀ index, 0 < diagonal index)
    (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := rectangularDiagonalCleanup rows columns rowBound columnBound width diagonal
    ∀ row column, (result.1 row column).natAbs < 2 ^ (width * rank + 1) := by
  dsimp only [rectangularDiagonalCleanup]
  apply rectangularDiagonal_bound
  rw [diagonalCleanupWithBases_diagonal]
  exact diagonalCleanup_entry_bound _ width diagonal positive entryBound

/-- Compose the cleanup with an existing rectangular diagonal presentation. -/
theorem rectangularDiagonalCleanup_of_presentation (rowBound : rank ≤ rows) (columnBound : rank ≤ columns)
    (width : ℕ) (diagonal : Fin rank → ℕ) (positive : ∀ index, 0 < diagonal index)
    (entryBound : ∀ index, diagonal index < 2 ^ width)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (equation : left * original * right = rectangularDiagonal rows columns diagonal)
    (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) :
    let result := rectangularDiagonalCleanup rows columns rowBound columnBound width diagonal
    IsSmithForm original result.1 (result.2.1 * left) (right * result.2.2) rank :=
  (rectangularDiagonalCleanup_isSmithForm rowBound columnBound width diagonal positive entryBound).of_equation
    equation leftUnit rightUnit

end Polytime2.IntegerMatrix
