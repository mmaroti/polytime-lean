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

import Polytime2.Matrices.DiagonalTrackingMath

/-! # Polynomial bounds for accumulated diagonal-cleanup transformations

Positive diagonal entries are controlled by their invariant total product.
Consequently each local coefficient has a fixed linear width in that product's
bit bound. Applying a local matrix adds this coefficient width to the current
basis width. Polynomially many repairs therefore give polynomial bounds for the
actual accumulated left and right matrices, including every unfinished prefix.
-/

namespace Polytime2.IntegerMatrix

variable {length : ℕ}

/-- The basis width grows additively per effective step, rather than doubling. -/
theorem diagonalCleanupWithBases_bound (fuel productWidth basisWidth : ℕ)
    (diagonal : Fin length → ℕ) (left right : Matrix (Fin length) (Fin length) ℤ)
    (positive : ∀ index, 0 < diagonal index) (productBound : (∏ index, diagonal index) ≤ 2 ^ productWidth)
    (leftBound : ∀ row column, (left row column).natAbs < 2 ^ basisWidth)
    (rightBound : ∀ row column, (right row column).natAbs < 2 ^ basisWidth) :
    let result := diagonalCleanupWithBases fuel diagonal left right
    (∀ row column, (result.2.1 row column).natAbs < 2 ^ (basisWidth + fuel * (4 * (productWidth + 1) + 3))) ∧
      (∀ row column, (result.2.2 row column).natAbs < 2 ^ (basisWidth + fuel * (4 * (productWidth + 1) + 3))) := by
  induction fuel generalizing diagonal basisWidth left right with
  | zero => simpa only [diagonalCleanupWithBases, Nat.zero_mul, Nat.add_zero] using And.intro leftBound rightBound
  | succ fuel inductionHypothesis =>
    cases found : diagonalViolation diagonal with
    | none =>
      have wider : 2 ^ basisWidth ≤ 2 ^ (basisWidth + (fuel + 1) * (4 * (productWidth + 1) + 3)) :=
        pow_le_pow_right₀ (by decide) (by omega)
      simp only [diagonalCleanupWithBases, found]
      exact ⟨fun row column => (leftBound row column).trans_le wider,
        fun row column => (rightBound row column).trans_le wider⟩
    | some pair =>
      obtain ⟨first, second⟩ := pair
      have failure := diagonalViolation_some diagonal first second found
      have different : first ≠ second := by intro same; subst second; omega
      have entryBound := diagonalEntries_bound productWidth diagonal positive productBound
      have nextBounds := diagonalPair_basis_bound (productWidth + 1) basisWidth first second
        (diagonal first) (diagonal second) left right
        (by simpa using entryBound first) (by simpa using entryBound second) leftBound rightBound
      have updatedProduct : (∏ index, diagonalNormalizePair diagonal first second index) ≤ 2 ^ productWidth := by
        rw [diagonalNormalizePair_product diagonal first second different]
        exact productBound
      have recursive := inductionHypothesis (basisWidth + (4 * (productWidth + 1) + 3))
        (diagonalNormalizePair diagonal first second)
        (rowPair first second (bezoutMatrix (diagonal first) (diagonal second)) left)
        (columnPair first second (diagonalPairRight (diagonal first) (diagonal second)) right)
        (diagonalNormalizePair_positive diagonal positive first second) updatedProduct nextBounds.1 nextBounds.2
      have widthEqual : basisWidth + (4 * (productWidth + 1) + 3) + fuel * (4 * (productWidth + 1) + 3) =
          basisWidth + (fuel + 1) * (4 * (productWidth + 1) + 3) := by ring
      rw [widthEqual] at recursive
      simpa only [diagonalCleanupWithBases, found] using recursive

/-- Both accumulated transformations have polynomial width at the certified iteration budget. -/
theorem diagonalCleanupWithBases_polynomial_bound (width : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (entryBound : ∀ index, diagonal index < 2 ^ width) :
    let result := diagonalCleanupWithBases (width * length * length + 1) diagonal 1 1
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ (1 + (width * length * length + 1) * (4 * (width * length + 1) + 3))) ∧
    (∀ row column, (result.2.2 row column).natAbs <
      2 ^ (1 + (width * length * length + 1) * (4 * (width * length + 1) + 3))) := by
  have productBound : (∏ index, diagonal index) ≤ 2 ^ (width * length) := by
    calc
      _ ≤ ∏ _index : Fin length, 2 ^ width := Finset.prod_le_prod (fun index _ => (entryBound index).le)
      _ = _ := by simp [← pow_mul]
  have identityBound : ∀ row column : Fin length, ((1 : Matrix (Fin length) (Fin length) ℤ) row column).natAbs < 2 ^ 1 := by
    intro row column
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  exact diagonalCleanupWithBases_bound _ (width * length) 1 diagonal 1 1 positive productBound identityBound identityBound

end Polytime2.IntegerMatrix
