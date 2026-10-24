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

import Polytime2.Matrices.SmithMath
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Smith quotient coordinates

A row on the active diagonal contributes its finite cyclic factor. Every
remaining row contributes `ZMod 0`, which is the ordinary integer group.
Thus the dependent product retains both torsion and free coordinates without
padding the matrix or discarding its singular part. Applying the left Smith
transformation gives coordinates of an original integer vector modulo the
matrix image.
-/

namespace Polytime2.IntegerMatrix

variable {rows columns : ℕ}

/-- Active diagonal moduli, with modulus zero for the free coordinates. -/
def diagonalModulus (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (row : Fin rows) : ℕ :=
  if active : row.val < rank then
    (diagonal row ⟨row.val, active.trans_le (within.trans (Nat.min_le_right rows columns))⟩).natAbs
  else 0

/-- Ordinary cyclic and integer quotient coordinates of a diagonal system. -/
def diagonalCoordinates (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) (target : Fin rows → ℤ) :
    ∀ row, ZMod (diagonalModulus diagonal rank within row) :=
  fun row => (target row : ZMod (diagonalModulus diagonal rank within row))

/-- The coordinate map vanishes exactly on the feasible right-hand sides. -/
theorem diagonalCoordinates_zero_iff (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (rank : ℕ) (within : rank ≤ min rows columns) (target : Fin rows → ℤ) :
    diagonalCoordinates diagonal rank within target = 0 ↔
      diagonalFeasible diagonal rank within target := by
  rw [funext_iff]
  apply forall_congr'
  intro row
  change ((target row : ZMod (diagonalModulus diagonal rank within row)) = 0) ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  dsimp only [diagonalModulus, diagonalFeasible]
  by_cases active : row.val < rank
  · simp only [active, ↓reduceDIte, Int.natCast_dvd, Int.natAbs_dvd_natAbs]
  · simp [active]

/-- Transported coordinates vanish exactly on the original integer matrix image. -/
theorem smithCoordinates_zero_iff (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) (target : Fin rows → ℤ) :
    diagonalCoordinates diagonal rank smith.2.2.2.1 (left.mulVec target) = 0 ↔
      ∃ values, matrix.mulVec values = target := by
  rw [diagonalCoordinates_zero_iff, smithFeasible_iff matrix diagonal left right rank smith]

/-- Equality of transported coordinates is precisely equality modulo the matrix image. -/
theorem smithCoordinates_eq_iff (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank)
    (first second : Fin rows → ℤ) :
    diagonalCoordinates diagonal rank smith.2.2.2.1 (left.mulVec first) =
      diagonalCoordinates diagonal rank smith.2.2.2.1 (left.mulVec second) ↔
        ∃ values, matrix.mulVec values = first - second := by
  rw [← smithCoordinates_zero_iff matrix diagonal left right rank smith]
  simp only [Matrix.mulVec_sub, diagonalCoordinates, Pi.sub_apply, Int.cast_sub,
    funext_iff, Pi.zero_apply, sub_eq_zero]


/-- The diagonal coordinate map is an additive homomorphism. -/
def diagonalCoordinatesHom (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (within : rank ≤ min rows columns) :
    (Fin rows → ℤ) →+ (∀ row, ZMod (diagonalModulus diagonal rank within row)) where
  toFun := diagonalCoordinates diagonal rank within
  map_zero' := by ext row; simp [diagonalCoordinates]
  map_add' := by intro first second; ext row; simp [diagonalCoordinates]

/-- Every cyclic or free coordinate tuple has an integer representative. -/
theorem diagonalCoordinates_surjective (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (rank : ℕ) (within : rank ≤ min rows columns) :
    Function.Surjective (diagonalCoordinates diagonal rank within) := by
  intro coordinates
  refine ⟨fun row => ZMod.cast (coordinates row), ?_⟩
  funext row
  exact ZMod.intCast_zmod_cast (coordinates row)

/-- Apply the left Smith change and retain its actual quotient coordinates. -/
def smithCoordinatesHom (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (rank : ℕ) (within : rank ≤ min rows columns) :
    (Fin rows → ℤ) →+ (∀ row, ZMod (diagonalModulus diagonal rank within row)) :=
  (diagonalCoordinatesHom diagonal rank within).comp left.mulVecLin.toAddMonoidHom

/-- The kernel of the transported coordinate homomorphism is the original image. -/
theorem smithCoordinatesHom_ker (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) :
    (smithCoordinatesHom diagonal left rank smith.2.2.2.1).ker =
      matrix.mulVecLin.toAddMonoidHom.range := by
  ext target
  exact smithCoordinates_zero_iff matrix diagonal left right rank smith target

/-- Every quotient coordinate has an original integer vector representing it. -/
theorem smithCoordinatesHom_surjective (diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (rank : ℕ) (within : rank ≤ min rows columns)
    (leftUnit : IsUnit left.det) :
    Function.Surjective (smithCoordinatesHom diagonal left rank within) :=
  (diagonalCoordinates_surjective diagonal rank within).comp
    (Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det left).mpr leftUnit))

/-- The integer cokernel is isomorphic to the product of the Smith cyclic and free factors. -/
noncomputable def smithQuotientEquiv (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) :
    ((Fin rows → ℤ) ⧸ matrix.mulVecLin.toAddMonoidHom.range) ≃+
      (∀ row, ZMod (diagonalModulus diagonal rank smith.2.2.2.1 row)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (smithCoordinatesHom_ker matrix diagonal left right rank smith).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (smithCoordinatesHom diagonal left rank smith.2.2.2.1)
      (smithCoordinatesHom_surjective diagonal left rank smith.2.2.2.1 smith.2.1))


/-- The quotient isomorphism computes the transported coordinates of a representative. -/
@[simp]
theorem smithQuotientEquiv_mk (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ) (right : Matrix (Fin columns) (Fin columns) ℤ)
    (rank : ℕ) (smith : IsSmithForm matrix diagonal left right rank) (target : Fin rows → ℤ) :
    smithQuotientEquiv matrix diagonal left right rank smith (QuotientAddGroup.mk target) =
      diagonalCoordinates diagonal rank smith.2.2.2.1 (left.mulVec target) := rfl

end Polytime2.IntegerMatrix
