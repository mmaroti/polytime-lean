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

import Polytime2.Matrices.DiagonalCleanupController
import Polytime2.Matrices.Identity
import Polytime2.Matrices.IntegerOperations

/-! # Certified cleanup of a positive bounded natural diagonal

The input is a positive natural diagonal of length n with magnitude width w.
Return its divisibility-normalized diagonal and both actual unimodular bases.
Only positivity is required. Derive the iteration budget, product bound, and
basis workspace internally, widen the entries, and initialize identity bases
before calling the bounded controller. Empty diagonals are admissible.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

namespace Realizable.Internal

noncomputable def positiveDiagonalProductWidth (length width : MvPolynomial Parameter ℕ) := width * length + width
noncomputable def positiveDiagonalBudget (length width : MvPolynomial Parameter ℕ) := width * length * length + 1
noncomputable def positiveDiagonalBasisWidth (length width : MvPolynomial Parameter ℕ) :=
  diagonalCleanupWorkspace (positiveDiagonalProductWidth length width) (positiveDiagonalBudget length width) 1

end Realizable.Internal

private noncomputable def widenedEntry (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((integerOfMagnitude width).followedBy
    (integerWidenTo width (width * length + 1) (positiveDiagonalProductWidth length width + 1) (by dsimp [positiveDiagonalProductWidth]; ring))
    rfl (by intros; trivial)).followedBy (integerMagnitude (positiveDiagonalProductWidth length width + 1)) rfl (by intros; trivial)

private theorem widenedEntry_realizable (length width : MvPolynomial Parameter ℕ) :
    (widenedEntry length width).Realizable :=
  ((integerOfMagnitude_realizable width).followedBy
    (integerWidenTo_realizable width (width * length + 1) (positiveDiagonalProductWidth length width + 1) (by dsimp [positiveDiagonalProductWidth]; ring))
    rfl (by intros; trivial)).followedBy (integerMagnitude_realizable (positiveDiagonalProductWidth length width + 1)) rfl (by intros; trivial)

private theorem widenedEntry_value (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (binaryNaturalsOfWidth width).Carrier sizes) :
    ((widenedEntry length width).compute sizes ⟨(fun _ => value), trivial⟩).val = value.val := by
  change (value.val : ℤ).natAbs = value.val
  exact Int.natAbs_natCast _

private noncomputable def widenedDiagonal (length width : MvPolynomial Parameter ℕ) :=
  mapArray (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth (positiveDiagonalProductWidth length width + 1)) length
    (fun sizes value => (widenedEntry length width).compute sizes ⟨(fun _ => value), trivial⟩)

private theorem widenedDiagonal_realizable (length width : MvPolynomial Parameter ℕ) :
    (widenedDiagonal length width).Realizable := by
  have scalar := (widenedEntry_realizable length width).withSpecification (fun _ _ => True)
    (fun sizes value => (widenedEntry length width).compute sizes ⟨(fun _ => value.val ()), trivial⟩)
    (by intros; trivial) (by intros; rfl)
  exact mapArray_realizable (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth (positiveDiagonalProductWidth length width + 1))
    length _ scalar

private noncomputable def initialIdentity (length width : MvPolynomial Parameter ℕ) :=
  (integerIdentity length).followedBy
    (integerMatrixWiden length length 1
      (positiveDiagonalBudget length width * (4 * (positiveDiagonalProductWidth length width + 1) + 3)) (positiveDiagonalBasisWidth length width) rfl)
    rfl (by intros; trivial)

private theorem initialIdentity_realizable (length width : MvPolynomial Parameter ℕ) :
    (initialIdentity length width).Realizable :=
  (integerIdentity_realizable length).followedBy
    (integerMatrixWiden_realizable length length 1
      (positiveDiagonalBudget length width * (4 * (positiveDiagonalProductWidth length width + 1) + 3)) (positiveDiagonalBasisWidth length width) rfl)
    rfl (by intros; trivial)

private noncomputable def initialState (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (binaryNaturalsOfWidth width).arrayOfLength length
  outputDomain := diagonalCleanupState length (positiveDiagonalProductWidth length width) (positiveDiagonalBasisWidth length width)
  precondition _ arguments := ∀ index, 0 < (arguments () index).val
  compute sizes arguments := ((widenedDiagonal length width).compute sizes ⟨arguments.val, trivial⟩,
    ((initialIdentity length width).compute sizes ⟨(fun impossible => impossible.elim), trivial⟩,
     (initialIdentity length width).compute sizes ⟨(fun impossible => impossible.elim), trivial⟩))

private theorem initialState_realizable (length width : MvPolynomial Parameter ℕ) :
    (initialState length width).Realizable := by
  let computation := initialState length width
  have diagonal := (widenedDiagonal_realizable length width).withPrecondition computation.precondition (by intros; trivial)
  have identity := (initialIdentity_realizable length width).onResults computation.inputDomains computation.precondition
    (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  exact (diagonal.prodMk (identity.prodMk identity)).withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

private theorem initialState_entries (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (initialState length width).Arguments sizes //
      (initialState length width).precondition sizes arguments}) :
    (fun index => (((initialState length width).compute sizes arguments).1 index).val) =
      (fun index => (arguments.val () index).val) := by
  funext index
  exact widenedEntry_value length width sizes (arguments.val () index)

private theorem initialState_valid (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (initialState length width).Arguments sizes //
      (initialState length width).precondition sizes arguments}) :
    (diagonalCleanupController length (positiveDiagonalProductWidth length width) (positiveDiagonalBudget length width) 1).precondition sizes
      (fun _ => (initialState length width).compute sizes arguments) := by
  have entries := initialState_entries length width sizes arguments
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index
    rw [congrFun entries index]
    exact arguments.property index
  · change (∏ index, (((initialState length width).compute sizes arguments).1 index).val) ≤ _
    rw [entries]
    have bound : (∏ index, (arguments.val () index).val) ≤ 2 ^ (MvPolynomial.eval sizes width * MvPolynomial.eval sizes length) := by
      calc
        _ ≤ ∏ _index : Fin (MvPolynomial.eval sizes length), 2 ^ MvPolynomial.eval sizes width :=
          Finset.prod_le_prod (fun index _ => (arguments.val () index).isLt.le)
        _ = _ := by simp [← pow_mul]
    apply bound.trans
    apply pow_le_pow_right₀ (by decide)
    simp only [positiveDiagonalProductWidth, map_add, map_mul]
    omega
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ MvPolynomial.eval sizes (1 : MvPolynomial Parameter ℕ)
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ MvPolynomial.eval sizes (1 : MvPolynomial Parameter ℕ)
    by_cases same : row = column <;> simp [Matrix.one_apply, same]

/-- Normalize a positive natural diagonal and return its actual unimodular bases. -/
noncomputable def positiveDiagonalCleanup (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (initialState length width).followedBy
    (diagonalCleanupController length (positiveDiagonalProductWidth length width) (positiveDiagonalBudget length width) 1) rfl
    (fun sizes arguments valid => initialState_valid length width sizes ⟨arguments, valid⟩)

theorem positiveDiagonalCleanup_realizable (length width : MvPolynomial Parameter ℕ) :
    (positiveDiagonalCleanup length width).Realizable :=
  (initialState_realizable length width).followedBy
    (diagonalCleanupController_realizable length (positiveDiagonalProductWidth length width) (positiveDiagonalBudget length width) 1) rfl
    (fun sizes arguments valid => initialState_valid length width sizes ⟨arguments, valid⟩)

/-- The public computation runs exactly the polynomially bounded mathematical cleanup. -/
theorem positiveDiagonalCleanup_correct (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (positiveDiagonalCleanup length width).Arguments sizes //
      (positiveDiagonalCleanup length width).precondition sizes arguments}) :
    let result := (positiveDiagonalCleanup length width).compute sizes arguments
    ((fun index => (result.1 index).val), (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.diagonalCleanupWithBases (MvPolynomial.eval sizes width * MvPolynomial.eval sizes length *
        MvPolynomial.eval sizes length + 1) (fun index => (arguments.val () index).val) 1 1 := by
  have computed := diagonalCleanupController_correct length (positiveDiagonalProductWidth length width) (positiveDiagonalBudget length width) 1 sizes
    ⟨(fun _ => (initialState length width).compute sizes arguments), initialState_valid length width sizes arguments⟩
  change ((fun index => (((positiveDiagonalCleanup length width).compute sizes arguments).1 index).val), _) = _ at computed
  rw [initialState_entries] at computed
  change ((fun index => (((positiveDiagonalCleanup length width).compute sizes arguments).1 index).val),
    (((positiveDiagonalCleanup length width).compute sizes arguments).2.1.val,
     ((positiveDiagonalCleanup length width).compute sizes arguments).2.2.val)) =
    IntegerMatrix.diagonalCleanupWithBases (MvPolynomial.eval sizes (positiveDiagonalBudget length width))
      (fun index => (arguments.val () index).val) 1 1 at computed
  simpa only [positiveDiagonalBudget, map_add, map_mul, map_one] using computed

/-- The returned active diagonal and both bases satisfy the complete square Smith contract. -/
theorem positiveDiagonalCleanup_isSmithForm (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (positiveDiagonalCleanup length width).Arguments sizes //
      (positiveDiagonalCleanup length width).precondition sizes arguments}) :
    let result := (positiveDiagonalCleanup length width).compute sizes arguments
    IntegerMatrix.IsSmithForm (Matrix.diagonal (fun index => ((arguments.val () index).val : ℤ)))
      (Matrix.diagonal (fun index => ((result.1 index).val : ℤ))) result.2.1.val result.2.2.val
      (MvPolynomial.eval sizes length) := by
  have computed := positiveDiagonalCleanup_correct length width sizes arguments
  have pure := IntegerMatrix.diagonalCleanupWithBases_isSmithForm (MvPolynomial.eval sizes width)
    (fun index => (arguments.val () index).val) arguments.property (fun index => (arguments.val () index).isLt)
  have transfer := congrArg (fun result => IntegerMatrix.IsSmithForm
    (Matrix.diagonal (fun index => ((arguments.val () index).val : ℤ)))
    (Matrix.diagonal (fun index => (result.1 index : ℤ))) result.2.1 result.2.2 (MvPolynomial.eval sizes length)) computed
  exact transfer.mpr pure

end Polytime2.Computation
