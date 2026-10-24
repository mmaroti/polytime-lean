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

import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Augmented integer systems for finite cyclic coordinates

For integer representatives `H` of generators and `a` of a target in a product
of cyclic groups, integer coefficients generate the target exactly when
`[H | diag(m)] x = a` has an integer solution. The generator columns are retained;
the additional columns account for multiples of each coordinate modulus.
-/

namespace Polytime2.IntegerMatrix

variable {Row Generator : Type} [Fintype Row] [Fintype Generator] [DecidableEq Row]

omit [Fintype Row] [DecidableEq Row] in
/-- Reindexing columns by an equivalence preserves existence of integer solutions. -/
theorem feasible_reindex_columns_iff {Other : Type} [Fintype Other]
    (matrix : Matrix Row Generator ℤ) (columns : Other ≃ Generator) (target : Row → ℤ) :
    (∃ values, (matrix.submatrix id columns).mulVec values = target) ↔
      ∃ values, matrix.mulVec values = target := by
  constructor
  · rintro ⟨values, solution⟩
    refine ⟨values ∘ columns.symm, ?_⟩
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_id] using solution
  · rintro ⟨values, solution⟩
    refine ⟨values ∘ columns, ?_⟩
    simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply, Function.id_def] using solution

/-- Append one coordinate-modulus column for each row of the generator matrix. -/
def augmentedMatrix (generators : Matrix Row Generator ℤ) (moduli : Row → ℤ) :
    Matrix Row (Generator ⊕ Row) ℤ :=
  Matrix.fromCols generators (Matrix.diagonal moduli)

/-- A supplied augmented solution retains its actual generator coefficients. -/
theorem augmented_solution_divisibility (generators : Matrix Row Generator ℤ) (moduli target : Row → ℤ)
    (values : Generator ⊕ Row → ℤ) (solution : (augmentedMatrix generators moduli).mulVec values = target) :
    ∀ row, moduli row ∣ target row - generators.mulVec (values ∘ Sum.inl) row := by
  intro row
  have entry := congrFun solution row
  simp only [augmentedMatrix, Matrix.fromCols_mulVec, Pi.add_apply,
    Matrix.mulVec_diagonal, Function.comp_apply] at entry
  refine ⟨values (.inr row), ?_⟩
  linear_combination -entry

/-- Augmentation preserves all generator coefficients and adds modulus multiples. -/
theorem augmented_feasible_iff (generators : Matrix Row Generator ℤ) (moduli target : Row → ℤ) :
    (∃ values, (augmentedMatrix generators moduli).mulVec values = target) ↔
      ∃ coefficients, ∀ row, moduli row ∣ target row - generators.mulVec coefficients row := by
  classical
  constructor
  · rintro ⟨values, solution⟩
    exact ⟨values ∘ Sum.inl, augmented_solution_divisibility generators moduli target values solution⟩
  · rintro ⟨coefficients, divides⟩
    choose multiples multiple_eq using divides
    refine ⟨Sum.elim coefficients multiples, ?_⟩
    funext row
    simp only [augmentedMatrix, Matrix.fromCols_mulVec_sumElim, Pi.add_apply,
      Matrix.mulVec_diagonal]
    linear_combination -(multiple_eq row)

/-- Membership in the product of cyclic coordinates is precisely augmented feasibility.
Positive moduli give finite cyclic groups; the equivalence also holds for modulus zero. -/
theorem cyclic_span_iff_augmented (generators : Matrix Row Generator ℤ)
    (moduli : Row → ℕ) (target : Row → ℤ) :
    (∃ coefficients : Generator → ℤ, ∀ row,
      (∑ generator, (coefficients generator : ZMod (moduli row)) *
        (generators row generator : ZMod (moduli row))) = (target row : ZMod (moduli row))) ↔
      ∃ values, (augmentedMatrix generators (fun row => (moduli row : ℤ))).mulVec values = target := by
  rw [augmented_feasible_iff]
  apply exists_congr
  intro coefficients
  apply forall_congr'
  intro row
  simpa [Matrix.mulVec, dotProduct, mul_comm] using
    ZMod.intCast_eq_intCast_iff_dvd_sub (generators.mulVec coefficients row) (target row) (moduli row)

/-- The generator coefficients of an actual augmented solution represent the cyclic target. -/
theorem cyclic_coefficients_of_augmented_solution (generators : Matrix Row Generator ℤ)
    (moduli : Row → ℕ) (target : Row → ℤ) (values : Generator ⊕ Row → ℤ)
    (solution : (augmentedMatrix generators (fun row => (moduli row : ℤ))).mulVec values = target) :
    ∀ row, (∑ generator, (values (.inl generator) : ZMod (moduli row)) *
      (generators row generator : ZMod (moduli row))) = (target row : ZMod (moduli row)) := by
  intro row
  have divides := augmented_solution_divisibility generators (fun row => (moduli row : ℤ)) target values solution row
  simpa [Matrix.mulVec, dotProduct, mul_comm] using
    (ZMod.intCast_eq_intCast_iff_dvd_sub (generators.mulVec (values ∘ Sum.inl) row) (target row) (moduli row)).mpr divides

end Polytime2.IntegerMatrix
