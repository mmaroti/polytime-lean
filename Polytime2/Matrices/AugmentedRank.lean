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

import Polytime2.Matrices.AugmentedMath
import Polytime2.Matrices.SmithCoordinates
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Full-rank augmented presentations and finite Smith quotients

Nonzero coordinate moduli give full row rank. A Smith presentation with no
free coordinates gives a finite integer cokernel.
-/

namespace Polytime2.IntegerMatrix

variable {Row Generator : Type} [Fintype Row] [Fintype Generator] [DecidableEq Row]

/-- Nonzero coordinate moduli force the augmented presentation to have full row rank. -/
theorem augmentedMatrix_rank (generators : Matrix Row Generator ℤ) (moduli : Row → ℤ)
    (nonzero : ∀ row, moduli row ≠ 0) :
    (augmentedMatrix generators moduli).rank = Fintype.card Row := by
  have diagonalRank : (Matrix.diagonal moduli).rank = Fintype.card Row :=
    Matrix.rank_of_det_ne_zero (by simpa [Matrix.det_diagonal] using Finset.prod_ne_zero_iff.mpr (by
      intro row _
      exact nonzero row))
  apply Nat.le_antisymm (Matrix.rank_le_card_height _)
  calc
    Fintype.card Row = (Matrix.diagonal moduli).rank := diagonalRank.symm
    _ = ((augmentedMatrix generators moduli).submatrix id Sum.inr).rank := rfl
    _ ≤ (augmentedMatrix generators moduli).rank := Matrix.rank_submatrix_le _ _ _

variable {rows columns : ℕ}

/-- A full-row-rank Smith presentation has finite integer cokernel. -/
theorem smithQuotient_finite (matrix diagonal : Matrix (Fin rows) (Fin columns) ℤ)
    (left : Matrix (Fin rows) (Fin rows) ℤ)
    (right : Matrix (Fin columns) (Fin columns) ℤ)
    (smith : IsSmithForm matrix diagonal left right rows) :
    Finite ((Fin rows → ℤ) ⧸ matrix.mulVecLin.toAddMonoidHom.range) := by
  have nonzero (row : Fin rows) :
      diagonalModulus diagonal rows smith.2.2.2.1 row ≠ 0 := by
    simp only [diagonalModulus, row.isLt, ↓reduceDIte, Int.natAbs_ne_zero]
    exact ne_of_gt (smith.2.2.2.2.2.2.1 row _ rfl row.isLt)
  let (row : Fin rows) : NeZero (diagonalModulus diagonal rows smith.2.2.2.1 row) :=
    ⟨nonzero row⟩
  exact Finite.of_injective (smithQuotientEquiv matrix diagonal left right rows smith)
    (smithQuotientEquiv matrix diagonal left right rows smith).injective


end Polytime2.IntegerMatrix
