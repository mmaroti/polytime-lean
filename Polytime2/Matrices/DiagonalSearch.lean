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

import Polytime2.Arithmetic.SignedDivides
import Polytime2.Arrays.FindFalse
import Polytime2.Arrays.Queue
import Polytime2.Arrays.ZipWith
import Polytime2.Arithmetic.SignedConstruction
import Polytime2.Arithmetic.SignedWidth

/-! # Certified adjacent-divisibility search for diagonal cleanup

The input is an ordinary array of bounded integers. Each flag tests whether an
entry divides its successor; the final flag is true. Internally, append a zero
and drop the first element, then reuse pointwise combination and the existing
first-false search. The public result is an optional coordinate, including for
empty input. No sentinel or extra mathematical dimension is exposed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def zeroForSearch (width : MvPolynomial Parameter ℕ) : Computation Parameter Empty :=
  (Realizable.Internal.integerBooleanOperationWiden width (Argument := Empty) (fun _ => ⟨0, by decide⟩)).followedBy
    (Realizable.Internal.integerNarrowAtWidths (width + 1) width) rfl (by intros; change (0 : ℤ).natAbs < _; simp)

private theorem zeroForSearch_realizable (width : MvPolynomial Parameter ℕ) : (zeroForSearch width).Realizable :=
  (Realizable.Internal.integerBooleanOperationWiden_realizable width (Argument := Empty) (fun _ => ⟨0, by decide⟩)).followedBy
    (Realizable.Internal.integerNarrowAtWidths_realizable (width + 1) width
      (by intro sizes; simp only [map_add, map_one]; omega)) rfl (by intros; change (0 : ℤ).natAbs < _; simp)

/-- Test every adjacent divisibility relation, treating the final coordinate as accepted. -/
noncomputable def diagonalDivisibilityFlags (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit := by
  classical
  exact {
    inputDomains := fun _ => (binaryIntegers width).arrayOfLength length
    outputDomain := booleans.arrayOfLength length
    precondition := fun _ _ => True
    compute := fun sizes arguments index => if next : index.val + 1 < MvPolynomial.eval sizes length then
      decide ((arguments.val () index).val ∣ (arguments.val () ⟨index.val + 1, next⟩).val) else true }

theorem diagonalDivisibilityFlags_realizable (length width : MvPolynomial Parameter ℕ) :
    (diagonalDivisibilityFlags length width).Realizable := by
  classical
  let computation := diagonalDivisibilityFlags length width
  let inputs := computation.inputDomains
  let scalar := binaryIntegers width
  have zero := (zeroForSearch_realizable width).withArguments inputs
    ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)
  have paired := (pairConstructor_realizable (scalar.arrayOfLength length) scalar).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val ()
      | 1 => (zeroForSearch width).compute sizes ⟨Empty.elim, trivial⟩)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs () (fun _ _ => True)
      · exact zero)
  have appended := paired.reinterpretOutput (scalar.arrayOfLength (length + 1))
    (fun sizes values => snocValues length sizes values.1 values.2)
    (by
      intro sizes
      change MvPolynomial.eval sizes ((length + 1) * scalar.widthPolynomial) =
        MvPolynomial.eval sizes (length * scalar.widthPolynomial + scalar.widthPolynomial)
      congr 1
      ring)
    (fun sizes values => arraySnoc_encode_bits scalar length sizes values.1 values.2)
  let shiftedValue sizes (arguments : {arguments : ∀ name, (inputs name).Carrier sizes // True}) :
      (scalar.arrayOfLength length).Carrier sizes :=
    Fin.tail (successorValues length sizes (snocValues length sizes (arguments.val ()) ⟨0, by simp⟩))
  have shifted : (Computation.mk inputs (scalar.arrayOfLength length) (fun _ _ => True) shiftedValue).Realizable :=
    appended.followedBy (arrayTail_realizable scalar length) rfl (by intros; trivial)
  let operation (_sizes : Parameter → ℕ) (_context : ∀ name : Empty, (Empty.elim name : EncodedDomain Parameter).Carrier _sizes)
      (first second : (binaryIntegers width).Carrier _sizes) := decide (first.val ∣ second.val)
  have step : (arrayZipWithStep (Context := Empty) Empty.elim scalar scalar booleans operation).Realizable :=
    (integerDivides_realizable width).withArguments
      (arrayZipWithStep (Context := Empty) Empty.elim scalar scalar booleans operation).inputDomains
      ⟨Sum.inr, Sum.inr_injective⟩
      (by intro choice; cases choice <;> rfl)
  have zipped := (arrayZipWith_realizable (Context := Empty) Empty.elim scalar scalar booleans length operation step).onResults
    inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl impossible => impossible.elim
      | .inr false => arguments.val ()
      | .inr true => shiftedValue sizes arguments)
    (by intros; trivial) (by
      intro name
      cases name with
      | inl impossible => exact impossible.elim
      | inr choice => cases choice; exact Realizable.argument inputs () (fun _ _ => True); exact shifted)
  apply zipped.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  funext index
  change decide ((arguments () index).val ∣ (Fin.snoc (α := fun _ : Fin (MvPolynomial.eval sizes length + 1) => scalar.Carrier sizes)
    (arguments ()) ⟨0, by simp⟩ index.succ).val) = _
  by_cases next : index.val + 1 < MvPolynomial.eval sizes length
  · have same : index.succ = Fin.castSucc ⟨index.val + 1, next⟩ := Fin.ext rfl
    erw [same, Fin.snoc_castSucc]
    simp [computation, diagonalDivisibilityFlags, next]
  · have same : index.succ = Fin.last (MvPolynomial.eval sizes length) := by
      apply Fin.ext
      have bounded := index.isLt
      dsimp
      omega
    erw [same, Fin.snoc_last]
    simp [computation, diagonalDivisibilityFlags, next]

/-- Find the first failed adjacent divisibility relation, or return `none` for a chain. -/
noncomputable def diagonalDivisibilitySearch (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (diagonalDivisibilityFlags length width).followedBy (arrayFindFalse length) rfl (by intros; trivial)

theorem diagonalDivisibilitySearch_realizable (length width : MvPolynomial Parameter ℕ) :
    (diagonalDivisibilitySearch length width).Realizable :=
  (diagonalDivisibilityFlags_realizable length width).followedBy (arrayFindFalse_realizable length) rfl (by intros; trivial)

/-- Search returns `none` exactly when all adjacent entries form a divisibility chain. -/
theorem diagonalDivisibilitySearch_none (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryIntegers width).arrayOfLength length).Carrier sizes) :
    (diagonalDivisibilitySearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = none ↔
      ∀ first second : Fin (MvPolynomial.eval sizes length), second.val = first.val + 1 →
        (values first).val ∣ (values second).val := by
  classical
  change (arrayFindFalse length).compute sizes
    ⟨(fun _ => (diagonalDivisibilityFlags length width).compute sizes ⟨(fun _ => values), trivial⟩), trivial⟩ = none ↔ _
  erw [arrayFindFalse_none]
  exact ArraySearch.adjacentFlags_all (fun first second : ℤ => first ∣ second)
    (fun index => (values index).val)

/-- Every returned coordinate has a genuine successor that violates divisibility. -/
theorem diagonalDivisibilitySearch_found (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryIntegers width).arrayOfLength length).Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes length))
    (found : (diagonalDivisibilitySearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = some index) :
    ∃ successor : Fin (MvPolynomial.eval sizes length), successor.val = index.val + 1 ∧
      ¬(values index).val ∣ (values successor).val := by
  classical
  have rejected := arrayFindFalse_found length sizes
    ((diagonalDivisibilityFlags length width).compute sizes ⟨(fun _ => values), trivial⟩) index found
  by_cases next : index.val + 1 < MvPolynomial.eval sizes length
  · refine ⟨⟨index.val + 1, next⟩, rfl, ?_⟩
    simpa only [diagonalDivisibilityFlags, next, ↓reduceDIte, decide_eq_false_iff_not] using rejected
  · simp [diagonalDivisibilityFlags, next] at rejected

end Polytime2.Computation
