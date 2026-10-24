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

import Polytime2.Matrices.HermiteAlternatingMath

/-! # Uniform bounds for alternating Hermite reduction

The determinant magnitude is fixed by the returned unimodular bases. Reduced
triangular pass outputs have all entries bounded by that fixed magnitude.
-/

namespace Polytime2.IntegerMatrix

private theorem identity_entry_bound {dimension : ℕ} (budget : ℕ) (row column : Fin dimension) :
    ((1 : Matrix (Fin dimension) (Fin dimension) ℤ) row column).natAbs < 2 ^ (1 + budget) := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp only [Int.natAbs_one, Int.natAbs_zero]
  · exact (by norm_num : 1 < 2 ^ 1).trans_le (pow_le_pow_right₀ (by decide) (by omega))
  · exact Nat.two_pow_pos _

/-- A square unimodular presentation preserves determinant magnitude. -/
theorem unimodular_presentation_det_natAbs {Index : Type} [Fintype Index] [DecidableEq Index]
    (original current left right : Matrix Index Index ℤ)
    (equation : left * original * right = current)
    (leftUnit : IsUnit left.det) (rightUnit : IsUnit right.det) :
    current.det.natAbs = original.det.natAbs := by
  rw [← equation, Matrix.det_mul, Matrix.det_mul, Int.natAbs_mul, Int.natAbs_mul,
    Int.isUnit_iff_natAbs_eq.mp leftUnit, Int.isUnit_iff_natAbs_eq.mp rightUnit, one_mul, mul_one]

/-- The actual row sweep preserves the square input determinant magnitude. -/
theorem hermiteRowsSweep_det_natAbs {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    (hermiteRowsSweep matrix).1.1.det.natAbs = matrix.det.natAbs := by
  have correct := hermiteRowsSweep_correct matrix
  exact unimodular_presentation_det_natAbs matrix _ _ 1
    (by simpa only [Matrix.mul_one] using correct.1) correct.2.1 (by simp)

/-- Normalized square row-sweep output entries are bounded by the original determinant. -/
theorem hermiteRowsSweep_entry_le_det {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index) :
    ∀ row column, ((hermiteRowsSweep matrix).1.1 row column).natAbs ≤ matrix.det.natAbs := by
  have canonical := hermiteRowsPrefix_canonical matrix lower positive dimension (by rfl)
  have invariant := hermiteRowsSweep_correct matrix
  have indices := canonical.1
  change (hermiteRowsSweep matrix).2 = _ at indices
  have reduced := invariant.2.2.2.2.2.2.1
  rw [indices] at reduced
  have shape := hermiteRowsSweep_upper_positive matrix lower positive
  have bound := normalized_block_entry_le_det (hermiteRowsSweep matrix).1.1 shape.1 shape.2 reduced
  simpa only [hermiteRowsSweep_det_natAbs] using bound

/-- Each alternating pair preserves the fixed determinant magnitude. -/
theorem hermiteAlternatingStep_det_natAbs {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    (hermiteAlternatingStep matrix).1.det.natAbs = matrix.det.natAbs := by
  have correct := hermiteAlternatingStep_preserves matrix
  exact unimodular_presentation_det_natAbs matrix _ _ _ correct.1 correct.2.1 correct.2.2

/-- Every pair output has entries bounded by the same input determinant magnitude. -/
theorem hermiteAlternatingStep_entry_le_det {dimension : ℕ}
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index) :
    ∀ row column, ((hermiteAlternatingStep matrix).1 row column).natAbs ≤ matrix.det.natAbs := by
  have first := hermiteRowsSweep_entry_le_det matrix lower positive
  have shape := hermiteRowsSweep_upper_positive matrix lower positive
  have second := hermiteRowsSweep_entry_le_det (hermiteRowsSweep matrix).1.1.transpose shape.1.transpose shape.2
  unfold hermiteAlternatingStep
  dsimp only
  split_ifs
  · exact first
  · intro row column
    simpa only [Matrix.transpose_apply, Matrix.det_transpose, hermiteRowsSweep_det_natAbs] using second column row

/-- Every bounded run preserves determinant magnitude, independently of the budget. -/
theorem hermiteAlternatingRun_det_natAbs {dimension : ℕ} (fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ) :
    (hermiteAlternatingRun fuel matrix).1.det.natAbs = matrix.det.natAbs := by
  have correct := hermiteAlternatingRun_preserves fuel matrix
  exact unimodular_presentation_det_natAbs matrix _ _ _ correct.1 correct.2.1 correct.2.2

/-- A common width for entries and the determinant is retained by every bounded run. -/
theorem hermiteAlternatingRun_entry_bound {dimension : ℕ} (width fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (detBound : matrix.det.natAbs < 2 ^ width) :
    ∀ row column, ((hermiteAlternatingRun fuel matrix).1 row column).natAbs < 2 ^ width := by
  induction fuel generalizing matrix with
  | zero => exact entryBound
  | succ fuel induction =>
    have shape := hermiteAlternatingStep_triangular matrix lower positive
    have bounded := hermiteAlternatingStep_entry_le_det matrix lower positive
    simp only [hermiteAlternatingRun]
    split_ifs
    · exact entryBound
    · exact induction _ shape.1 shape.2 (fun row column => (bounded row column).trans_lt detBound)
        (by simpa only [hermiteAlternatingStep_det_natAbs] using detBound)

/-- Each pair returns two bases with the single-sweep polynomial width at a common determinant width. -/
theorem hermiteAlternatingStep_basis_bound {dimension : ℕ} (width : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (detBound : matrix.det.natAbs < 2 ^ width) :
    (∀ row column, ((hermiteAlternatingStep matrix).2.1 row column).natAbs <
      2 ^ (1 + dimension * hermiteSweepBasisIncrement dimension width)) ∧
    (∀ row column, ((hermiteAlternatingStep matrix).2.2 row column).natAbs <
      2 ^ (1 + dimension * hermiteSweepBasisIncrement dimension width)) := by
  have first := hermiteRowsSweep_basis_bound width matrix entryBound
  have entries := hermiteRowsSweep_entry_le_det matrix lower positive
  have second := hermiteRowsSweep_basis_bound width (hermiteRowsSweep matrix).1.1.transpose
    (fun row column => (entries column row).trans_lt detBound)
  unfold hermiteAlternatingStep
  dsimp only
  split_ifs
  · exact ⟨first, identity_entry_bound _⟩
  · exact ⟨first, fun row column => second column row⟩

/-- Actual accumulated bases grow additively in the number of pairs at the fixed determinant width. -/
theorem hermiteAlternatingRun_basis_bound {dimension : ℕ} (width fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (detBound : matrix.det.natAbs < 2 ^ width) :
    (∀ row column, ((hermiteAlternatingRun fuel matrix).2.1 row column).natAbs <
      2 ^ (1 + fuel * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1))) ∧
    (∀ row column, ((hermiteAlternatingRun fuel matrix).2.2 row column).natAbs <
      2 ^ (1 + fuel * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1))) := by
  induction fuel generalizing matrix with
  | zero =>
    simpa only [hermiteAlternatingRun, Nat.zero_mul] using And.intro (identity_entry_bound 0) (identity_entry_bound 0)
  | succ fuel induction =>
    have shape := hermiteAlternatingStep_triangular matrix lower positive
    have entries := hermiteAlternatingStep_entry_le_det matrix lower positive
    have step := hermiteAlternatingStep_basis_bound width matrix lower positive entryBound detBound
    have rest := induction (hermiteAlternatingStep matrix).1 shape.1 shape.2
      (fun row column => (entries row column).trans_lt detBound)
      (by simpa only [hermiteAlternatingStep_det_natAbs] using detBound)
    have leftBound := mul_bound _ _ _ _ rest.1 step.1
    have rightBound := mul_bound _ _ _ _ step.2 rest.2
    simp only [hermiteAlternatingRun]
    split_ifs
    · exact ⟨identity_entry_bound _, identity_entry_bound _⟩
    · constructor
      · intro row column
        exact (leftBound row column).trans_le (pow_le_pow_right₀ (by decide) (by
          simp only [Fintype.card_fin, Nat.add_mul, one_mul]; omega))
      · intro row column
        exact (rightBound row column).trans_le (pow_le_pow_right₀ (by decide) (by
          simp only [Fintype.card_fin, Nat.add_mul, one_mul]; omega))

/-- Run widths depend only on mathematical input width, dimension, and the pair budget. -/
theorem hermiteAlternatingRun_bound {dimension : ℕ} (width fuel : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    let commonWidth := width + dimension * (width + dimension) + 1
    (∀ row column, ((hermiteAlternatingRun fuel matrix).1 row column).natAbs < 2 ^ commonWidth) ∧
    (∀ row column, ((hermiteAlternatingRun fuel matrix).2.1 row column).natAbs <
      2 ^ (1 + fuel * (1 + dimension * hermiteSweepBasisIncrement dimension commonWidth + dimension + 1))) ∧
    (∀ row column, ((hermiteAlternatingRun fuel matrix).2.2 row column).natAbs <
      2 ^ (1 + fuel * (1 + dimension * hermiteSweepBasisIncrement dimension commonWidth + dimension + 1))) := by
  let commonWidth := width + dimension * (width + dimension) + 1
  have widened : ∀ row column, (matrix row column).natAbs < 2 ^ commonWidth := by
    intro row column
    exact (entryBound row column).trans_le (pow_le_pow_right₀ (by decide) (by dsimp [commonWidth]; omega))
  have determinant : matrix.det.natAbs < 2 ^ commonWidth :=
    (determinant_bound width dimension matrix entryBound).trans_le
      (pow_le_pow_right₀ (by decide) (by dsimp [commonWidth]; omega))
  exact ⟨hermiteAlternatingRun_entry_bound commonWidth fuel matrix lower positive widened determinant,
    hermiteAlternatingRun_basis_bound commonWidth fuel matrix lower positive widened determinant⟩

/-- Every forward prefix fits one matrix width and one budget-derived basis width. -/
theorem hermiteAlternatingAdvance_prefix_bound {dimension : ℕ} (width budget count : ℕ)
    (matrix : Matrix (Fin dimension) (Fin dimension) ℤ)
    (lower : matrix.IsLowerTriangular) (positive : ∀ index, 0 < matrix index index)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (detBound : matrix.det.natAbs < 2 ^ width) (within : count ≤ budget) :
    let result := hermiteAlternatingAdvance^[count] (matrix, 1, 1)
    (∀ row column, (result.1 row column).natAbs < 2 ^ width) ∧
    (∀ row column, (result.2.1 row column).natAbs <
      2 ^ (1 + budget * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1))) ∧
    (∀ row column, (result.2.2 row column).natAbs <
      2 ^ (1 + budget * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1))) := by
  rw [← hermiteAlternatingRun_eq_iterate]
  have entries := hermiteAlternatingRun_entry_bound width count matrix lower positive entryBound detBound
  have bases := hermiteAlternatingRun_basis_bound width count matrix lower positive entryBound detBound
  have growth : 2 ^ (1 + count * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1)) ≤
      2 ^ (1 + budget * (1 + dimension * hermiteSweepBasisIncrement dimension width + dimension + 1)) :=
    pow_le_pow_right₀ (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_right _ within) 1)
  exact ⟨entries, fun row column => (bases.1 row column).trans_le growth,
    fun row column => (bases.2 row column).trans_le growth⟩

end Polytime2.IntegerMatrix
