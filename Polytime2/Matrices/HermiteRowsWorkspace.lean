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

import Polytime2.Matrices.IntegerHermiteAdvance

/-! # A fixed workspace for the outer Hermite row traversal

Both matrix and accumulated-basis widths are derived from the original entry
width and row count. Canonical-prefix equality supplies each next-state bound;
local insertion widths are not iterated across the outer loop.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- One exact polynomial capacity for every matrix and basis in the outer row traversal. -/
noncomputable def hermiteRowsWorkspace (width rows : MvPolynomial Parameter ℕ) : MvPolynomial Parameter ℕ :=
  (2 * (rows * (width + rows) + 1) + width + 2 * rows + 2) +
    1 + rows * IntegerMatrix.hermiteSweepBasisIncrement rows width

omit [Fintype Parameter] in
/-- Every canonical outer prefix fits the same original-input-derived workspace. -/
theorem hermiteRowsWorkspace_bound (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ MvPolynomial.eval sizes width)
    (processed : ℕ) (within : processed ≤ MvPolynomial.eval sizes rows) :
    let state := (IntegerMatrix.hermiteRowsPrefix original processed within).val
    (∀ row column, (state.1.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace width rows)) ∧
    (∀ row column, (state.1.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace width rows)) := by
  have matrixBound := IntegerMatrix.hermiteRowPrefix_matrix_bound (MvPolynomial.eval sizes width) processed within
    original _ (IntegerMatrix.hermiteRowsPrefix original processed within).property entryBound
  have basisBound := IntegerMatrix.hermiteRowsPrefix_basis_bound (MvPolynomial.eval sizes width) original entryBound processed within
  constructor
  · intro row column
    apply (matrixBound row column).trans_le
    apply pow_le_pow_right₀ (by decide)
    simp only [hermiteRowsWorkspace, IntegerMatrix.hermiteSweepBasisIncrement, map_add, map_mul, map_one, map_ofNat]
    omega
  · intro row column
    apply (basisBound row column).trans_le
    apply pow_le_pow_right₀ (by decide)
    have multiplied := Nat.mul_le_mul_right
      (IntegerMatrix.hermiteSweepBasisIncrement (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes width)) within
    simp only [hermiteRowsWorkspace, IntegerMatrix.hermiteSweepBasisIncrement, map_add, map_mul, map_one, map_ofNat] at *
    omega

/-- Advancing a canonical prefix returns matrices that fit the fixed outer workspace. -/
theorem integerHermiteAdvance_workspace (rows columns inputWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).Arguments sizes //
      (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ MvPolynomial.eval sizes inputWidth)
    (prefixEqual : (((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1) =
      (IntegerMatrix.hermiteRowsPrefix original (arguments.val () 0).2.val (Nat.le_of_lt (arguments.val () 0).2.isLt)).val) :
    let result := (integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes arguments
    (∀ row column, (result.1.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace inputWidth rows)) ∧
    (∀ row column, (result.1.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteRowsWorkspace inputWidth rows)) := by
  have invariant : IntegerMatrix.HermiteRowPrefix original (arguments.val () 0).2.val
      (((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1) := by
    rw [prefixEqual]
    exact (IntegerMatrix.hermiteRowsPrefix original _ _).property
  have advanced := integerHermiteAdvance_correct rows columns (hermiteRowsWorkspace inputWidth rows) sizes arguments original invariant
  have next : (((((integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes arguments).1.1.val,
      ((integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes arguments).1.2.val),
      ((integerHermiteAdvance rows columns (hermiteRowsWorkspace inputWidth rows)).compute sizes arguments).2)) =
      (IntegerMatrix.hermiteRowsPrefix original ((arguments.val () 0).2.val + 1) (arguments.val () 0).2.isLt).val := by
    apply advanced.trans
    apply congrArg (fun state => (IntegerMatrix.hermiteRowAdvance original (arguments.val () 0).2 state).val)
    exact Subtype.ext prefixEqual
  have bounds := hermiteRowsWorkspace_bound rows columns inputWidth sizes original entryBound
    ((arguments.val () 0).2.val + 1) (arguments.val () 0).2.isLt
  have pairs := congrArg Prod.fst next
  dsimp only at bounds
  rw [← pairs] at bounds
  exact bounds

end Polytime2.Computation
