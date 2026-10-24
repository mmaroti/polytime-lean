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

import Polytime2.Matrices.DiagonalBasisStep
import Polytime2.Matrices.IntegerPairNarrow

/-! # Returning cleanup bases to a fixed workspace

A coupled cleanup step temporarily widens both bases. Given proofs that the
returned entries fit the workspace bound, retain the diagonal values and narrow
both bases without changing their mathematical values. The cleanup controller
will discharge these internal preconditions using its prefix growth invariant.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Narrow both bases of a coupled pair result to their original workspace. -/
noncomputable def diagonalBasisNarrow (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (integerDiagonalBasisStep length diagonalWidth basisWidth).outputDomain
  outputDomain := (integerGcdLcm diagonalWidth).outputDomain.prod
    ((integerMatrices length length basisWidth).prod (integerMatrices length length basisWidth))
  precondition sizes arguments :=
    (∀ row column, ((arguments ()).2.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes basisWidth) ∧
    (∀ row column, ((arguments ()).2.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes basisWidth)
  compute _ arguments := ((arguments.val ()).1,
    (⟨(arguments.val ()).2.1.val, arguments.property.1⟩,
     ⟨(arguments.val ()).2.2.val, arguments.property.2⟩))

theorem diagonalBasisNarrow_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalBasisNarrow length diagonalWidth basisWidth).Realizable := by
  let computation := diagonalBasisNarrow length diagonalWidth basisWidth
  let values := (integerGcdLcm diagonalWidth).outputDomain
  let left := integerMatrices length length ((2 * diagonalWidth + 1) + basisWidth + 1)
  let right := integerMatrices length length ((2 * (2 * diagonalWidth + 1)) + basisWidth + 1)
  have bases := pairProjection_realizable values (left.prod right) true
  have narrowed := (bases.withPrecondition computation.precondition (by intros; trivial)).followedBy
    (integerMatrixPairNarrow_realizable length length length length
      ((2 * diagonalWidth + 1) + basisWidth + 1) ((2 * (2 * diagonalWidth + 1)) + basisWidth + 1) basisWidth
      (by intro sizes; simp only [map_add]; omega) (by intro sizes; simp only [map_add]; omega)) rfl
    (by intro sizes arguments valid; exact valid)
  have kept := (pairProjection_realizable values (left.prod right) false).withPrecondition
    computation.precondition (by intros; trivial)
  have complete := Realizable.pairOutputs computation.inputDomains values
    ((integerMatrices length length basisWidth).prod (integerMatrices length length basisWidth))
    computation.precondition _ _ kept narrowed
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A prefix bound with enough room discharges the fixed-workspace narrowing. -/
theorem diagonalBasisNarrow_step_valid (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerDiagonalBasisStep length diagonalWidth basisWidth).Arguments sizes //
      (integerDiagonalBasisStep length diagonalWidth basisWidth).precondition sizes arguments})
    (prefixWidth : ℕ)
    (leftBound : ∀ row column, ((arguments.val 4).val row column).natAbs < 2 ^ prefixWidth)
    (rightBound : ∀ row column, ((arguments.val 5).val row column).natAbs < 2 ^ prefixWidth)
    (room : prefixWidth + (4 * MvPolynomial.eval sizes diagonalWidth + 3) ≤ MvPolynomial.eval sizes basisWidth) :
    (diagonalBasisNarrow length diagonalWidth basisWidth).precondition sizes
      (fun _ => (integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments) := by
  have bounds := IntegerMatrix.diagonalPair_basis_bound (Index := Fin (MvPolynomial.eval sizes length))
    (MvPolynomial.eval sizes diagonalWidth) prefixWidth
    (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
    (arguments.val 4).val (arguments.val 5).val (arguments.val 2).property (arguments.val 3).property
    leftBound rightBound
  have computed := integerDiagonalBasisStep_correct length diagonalWidth basisWidth sizes arguments
  have leftEqual := congrArg Prod.fst computed
  have rightEqual := congrArg Prod.snd computed
  dsimp only at leftEqual rightEqual
  change (∀ row column, (((integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments).2.1.val
      row column).natAbs < 2 ^ MvPolynomial.eval sizes basisWidth) ∧
    (∀ row column, (((integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments).2.2.val
      row column).natAbs < 2 ^ MvPolynomial.eval sizes basisWidth)
  rw [leftEqual, rightEqual]
  exact ⟨fun row column => (bounds.1 row column).trans_le (pow_le_pow_right₀ (by decide) room),
    fun row column => (bounds.2 row column).trans_le (pow_le_pow_right₀ (by decide) room)⟩

/-- Repair and return both bases to their fixed workspace using a logical prefix bound. -/
noncomputable def diagonalBasisStepWithin (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) :=
  ((integerDiagonalBasisStep length diagonalWidth basisWidth).withPrecondition
    (fun sizes arguments => arguments 0 ≠ arguments 1 ∧ ∃ prefixWidth : ℕ,
      (∀ row column, ((arguments 4).val row column).natAbs < 2 ^ prefixWidth) ∧
      (∀ row column, ((arguments 5).val row column).natAbs < 2 ^ prefixWidth) ∧
      prefixWidth + (4 * MvPolynomial.eval sizes diagonalWidth + 3) ≤ MvPolynomial.eval sizes basisWidth)
    (by intro sizes arguments valid; exact valid.1)).followedBy
      (diagonalBasisNarrow length diagonalWidth basisWidth) rfl (by
        intro sizes arguments valid
        obtain ⟨prefixWidth, leftBound, rightBound, room⟩ := valid.2
        exact diagonalBasisNarrow_step_valid length diagonalWidth basisWidth sizes ⟨arguments, valid.1⟩
          prefixWidth leftBound rightBound room)

theorem diagonalBasisStepWithin_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalBasisStepWithin length diagonalWidth basisWidth).Realizable := by
  let computation := diagonalBasisStepWithin length diagonalWidth basisWidth
  have step := (integerDiagonalBasisStep_realizable length diagonalWidth basisWidth).withPrecondition
    computation.precondition (by intro sizes arguments valid; exact valid.1)
  have complete := step.followedBy (diagonalBasisNarrow_realizable length diagonalWidth basisWidth) rfl (by
    intro sizes arguments valid
    obtain ⟨prefixWidth, leftBound, rightBound, room⟩ := valid.2
    exact diagonalBasisNarrow_step_valid length diagonalWidth basisWidth sizes ⟨arguments, valid.1⟩
      prefixWidth leftBound rightBound room)
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

/-- Fixed-workspace repair retains all values of the original coupled operation. -/
theorem diagonalBasisStepWithin_values (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalBasisStepWithin length diagonalWidth basisWidth).Arguments sizes //
      (diagonalBasisStepWithin length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalBasisStepWithin length diagonalWidth basisWidth).compute sizes arguments
    let original := (integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes
      ⟨arguments.val, arguments.property.1⟩
    result.1 = original.1 ∧ result.2.1.val = original.2.1.val ∧ result.2.2.val = original.2.2.val := ⟨rfl, rfl, rfl⟩

/-- Narrowing changes only the encodings of the bases. -/
theorem diagonalBasisNarrow_values (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalBasisNarrow length diagonalWidth basisWidth).Arguments sizes //
      (diagonalBasisNarrow length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalBasisNarrow length diagonalWidth basisWidth).compute sizes arguments
    result.1 = (arguments.val ()).1 ∧
      result.2.1.val = (arguments.val ()).2.1.val ∧
      result.2.2.val = (arguments.val ()).2.2.val := ⟨rfl, rfl, rfl⟩

end Polytime2.Computation.Realizable.Internal
