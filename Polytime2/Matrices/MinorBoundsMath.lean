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

import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! # Original-minor bounds for supported reduced blocks

Suppose `original = factor * current` and selected columns of `current` vanish
outside selected rows. The selected original minor factors through the current
square block, allowing different original and current row selections. Its
determinant is divisible by the current determinant. A
nonzero original minor consequently bounds the current determinant. The
Leibniz determinant estimate gives a polynomial binary-width bound from the
original entry width, including the empty minor.
-/

namespace Polytime2.IntegerMatrix

/-- Restrict a product whenever the omitted summands vanish. -/
theorem supported_product_factorization {Row Column Index OriginalIndex : Type} [Fintype Row] {rank : ℕ}
    (originalRows : OriginalIndex → Row) (currentRows : Fin rank ↪ Row) (selectedColumns : Index → Column)
    (original current : Matrix Row Column ℤ) (factor : Matrix Row Row ℤ)
    (equation : original = factor * current)
    (support : ∀ row : OriginalIndex, ∀ other ∉ Set.range currentRows, ∀ column,
      factor (originalRows row) other * current other (selectedColumns column) = 0) :
    original.submatrix originalRows selectedColumns =
      factor.submatrix originalRows currentRows * current.submatrix currentRows selectedColumns := by
  classical
  ext row column
  rw [equation]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_of_injective currentRows currentRows.injective
    (fun index => factor (originalRows row) (currentRows index) * current (currentRows index) (selectedColumns column))
    (fun index => factor (originalRows row) index * current index (selectedColumns column))
    (fun index outside => support row index outside column) (fun _ => rfl)).symm

/-- Restricting a product needs only selected rows when the other rows contribute zero. -/
theorem supported_minor_factorization {Row Column Index OriginalIndex : Type} [Fintype Row] {rank : ℕ}
    (originalRows : OriginalIndex → Row) (currentRows : Fin rank ↪ Row) (selectedColumns : Index → Column)
    (original current : Matrix Row Column ℤ) (factor : Matrix Row Row ℤ)
    (equation : original = factor * current)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row (selectedColumns column) = 0) :
    original.submatrix originalRows selectedColumns =
      factor.submatrix originalRows currentRows * current.submatrix currentRows selectedColumns := by
  exact supported_product_factorization originalRows currentRows selectedColumns original current factor equation
    (fun row other outside column => by rw [support other outside column, mul_zero])

/-- A transformation with no coefficients on omitted inputs restricts to those inputs. -/
theorem supported_minor_factorization_of_left {Row Column Index OriginalIndex : Type} [Fintype Row] {rank : ℕ}
    (originalRows : OriginalIndex → Row) (currentRows : Fin rank ↪ Row) (selectedColumns : Index → Column)
    (original current : Matrix Row Column ℤ) (factor : Matrix Row Row ℤ)
    (equation : original = factor * current)
    (support : ∀ row : OriginalIndex, ∀ other ∉ Set.range currentRows, factor (originalRows row) other = 0) :
    original.submatrix originalRows selectedColumns =
      factor.submatrix originalRows currentRows * current.submatrix currentRows selectedColumns := by
  exact supported_product_factorization originalRows currentRows selectedColumns original current factor equation
    (fun row other outside column => by rw [support row other outside, zero_mul])

/-- A supported current block determinant divides the corresponding original minor. -/
theorem supported_minor_dvd {Row Column : Type} [Fintype Row] {rank : ℕ}
    (originalRows currentRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (factor : Matrix Row Row ℤ)
    (equation : original = factor * current)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row (selectedColumns column) = 0) :
    (current.submatrix currentRows selectedColumns).det ∣ (original.submatrix originalRows selectedColumns).det := by
  refine ⟨(factor.submatrix originalRows currentRows).det, ?_⟩
  rw [supported_minor_factorization originalRows currentRows selectedColumns original current factor equation support, Matrix.det_mul]
  ring

/-- A unimodular row transformation supplies the inverse factor without extra witnesses. -/
theorem unimodular_supported_minor_dvd {Row Column : Type} [Fintype Row] [DecidableEq Row] {rank : ℕ}
    (originalRows currentRows : Fin rank ↪ Row) (selectedColumns : Fin rank ↪ Column)
    (original current : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (equation : left * original = current) (unit : IsUnit left.det)
    (support : ∀ row ∉ Set.range currentRows, ∀ column, current row (selectedColumns column) = 0) :
    (current.submatrix currentRows selectedColumns).det ∣ (original.submatrix originalRows selectedColumns).det := by
  have recovered : original = left⁻¹ * current := calc
    original = left⁻¹ * (left * original) := (Matrix.nonsing_inv_mul_cancel_left left original unit).symm
    _ = left⁻¹ * current := by rw [equation]
  exact supported_minor_dvd originalRows currentRows selectedColumns original current left⁻¹ recovered support

/-- Original integer entry widths give a polynomial determinant width. -/
theorem determinant_bound (width rank : ℕ) (matrix : Matrix (Fin rank) (Fin rank) ℤ)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    matrix.det.natAbs < 2 ^ (rank * (width + rank) + 1) := by
  have raw := Matrix.det_le (A := matrix) (abv := AbsoluteValue.abs) (x := (2 : ℤ) ^ width) (fun row column => by
    change |matrix row column| ≤ (2 : ℤ) ^ width
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (entryBound row column).le)
  have determinantLe : matrix.det.natAbs ≤ rank.factorial * (2 ^ width) ^ rank := by
    simp only [Fintype.card_fin] at raw
    change |matrix.det| ≤ rank.factorial • ((2 : ℤ) ^ width) ^ rank at raw
    simp only [Int.abs_eq_natAbs, Int.nsmul_eq_mul] at raw
    exact_mod_cast raw
  have factorialBound : rank.factorial ≤ 2 ^ (rank * rank) := calc
    rank.factorial ≤ rank ^ rank := Nat.factorial_le_pow rank
    _ ≤ (2 ^ rank) ^ rank := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (rank * rank) := by rw [← pow_mul]
  have wholeBound : rank.factorial * (2 ^ width) ^ rank ≤ 2 ^ (rank * (width + rank)) := calc
    _ ≤ 2 ^ (rank * rank) * (2 ^ width) ^ rank := Nat.mul_le_mul_right _ factorialBound
    _ = 2 ^ (rank * (width + rank)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
  apply (determinantLe.trans wholeBound).trans_lt
  rw [pow_succ]
  have positive : 0 < (2 : ℕ) ^ (rank * (width + rank)) := by positivity
  omega

end Polytime2.IntegerMatrix
