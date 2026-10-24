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

import Polytime2.Matrices.IntegerPositivePivot
import Polytime2.Matrices.RemainderSweepController

/-! # Runtime extension by a new Hermite pivot

Given a nonzero selected entry and distinct old rows excluding its source,
make that entry positive and reduce the old rows against it. Both input
matrices use their original common width; sign normalization, widening, and
remainder traversal are composed internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width length : MvPolynomial Parameter ℕ) : Fin 5 → EncodedDomain Parameter
  | 0 => boundedIndex rows
  | 1 => boundedIndex columns
  | 2 => integerMatrices rows columns width
  | 3 => integerMatrices rows rows width
  | 4 => (boundedIndex rows).arrayOfLength length

private def allowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :=
  (List.ofFn (arguments 4)).Nodup ∧ arguments 0 ∉ List.ofFn (arguments 4) ∧
    (arguments 2).val (arguments 0) (arguments 1) ≠ 0

private noncomputable def signed (rows columns width length : MvPolynomial Parameter ℕ) :=
  (integerPositivePivotWithLeft rows columns width).withArguments (inputs rows columns width length)
    (Fin.castLEEmb (by decide : 4 ≤ 5)) (by intro name; fin_cases name <;> rfl)

private noncomputable def prepared (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width length name).Carrier sizes //
      allowed rows columns width length sizes arguments}) :
    (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes :=
  let pair := (signed rows columns width length).compute sizes ⟨arguments.val, trivial⟩
  ((integerMatrixWiden rows columns width (width + 1) (2 * width + 1) (by ring)).compute sizes
      ⟨(fun _ => pair.1), trivial⟩,
    (integerMatrixWiden rows rows width (width + 1) (2 * width + 1) (by ring)).compute sizes
      ⟨(fun _ => pair.2), trivial⟩)

private noncomputable def preparedValues (rows columns width length : MvPolynomial Parameter ℕ)
    (name : Bool ⊕ Bool) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width length name).Carrier sizes //
      allowed rows columns width length sizes arguments}) :
    ((remainderSweepController rows columns width length).inputDomains name).Carrier sizes :=
  match name with
  | .inl false => arguments.val 0
  | .inl true => arguments.val 1
  | .inr false => prepared rows columns width length sizes arguments
  | .inr true => arguments.val 4

private theorem prepared_valid (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width length name).Carrier sizes //
      allowed rows columns width length sizes arguments}) :
    (remainderSweepController rows columns width length).precondition sizes
      (fun name => preparedValues rows columns width length name sizes arguments) := by
  rw [remainderSweepController_precondition]
  refine ⟨arguments.property.1, arguments.property.2.1, ?_, ?_, ?_⟩
  · change 0 < (IntegerMatrix.positivePivotWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val).1
      (arguments.val 0) (arguments.val 1)
    rw [IntegerMatrix.positivePivotWithLeft_entry]
    exact abs_pos.mpr arguments.property.2.2
  · exact (IntegerMatrix.positivePivotWithLeft_bound (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width)
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
      (arguments.val 2).property (arguments.val 3).property).1
  · exact (IntegerMatrix.positivePivotWithLeft_bound (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width)
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
      (arguments.val 2).property (arguments.val 3).property).2

/-- Normalize a nonzero new pivot and reduce all supplied old rows against it. -/
noncomputable def integerHermiteExtendPivot (rows columns width length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  (remainderSweepController rows columns width length).onResults (inputs rows columns width length)
    (allowed rows columns width length) (preparedValues rows columns width length) (prepared_valid rows columns width length)

/-- Sign normalization and old-row reduction use existing certified components. -/
theorem integerHermiteExtendPivot_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteExtendPivot rows columns width length).Realizable := by
  let host := inputs rows columns width length
  let valid := allowed rows columns width length
  have signReady := ((integerPositivePivotWithLeft_realizable rows columns width).withArguments host
    (Fin.castLEEmb (by decide : 4 ≤ 5)) (by intro name; fin_cases name <;> rfl)).withPrecondition valid (by intros; trivial)
  have first := (signReady.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)).followedBy
    (integerMatrixWiden_realizable rows columns width (width + 1) (2 * width + 1) (by ring)) rfl (by intros; trivial)
  have second := (signReady.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)).followedBy
    (integerMatrixWiden_realizable rows rows width (width + 1) (2 * width + 1) (by ring)) rfl (by intros; trivial)
  have pair := Realizable.pairOutputs host _ _ valid _ _ first second
  apply (remainderSweepController_realizable rows columns width length).onResults host valid
    (preparedValues rows columns width length) (prepared_valid rows columns width length)
  intro name
  rcases name with original | choice
  · cases original
    · exact Realizable.argument host 0 valid
    · exact Realizable.argument host 1 valid
  · cases choice
    · exact pair
    · exact Realizable.argument host 4 valid

/-- The returned matrices are the exact sign-normalized mathematical remainder sweep. -/
theorem integerHermiteExtendPivot_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteExtendPivot rows columns width length).Arguments sizes //
      (integerHermiteExtendPivot rows columns width length).precondition sizes arguments}) :
    let result := (integerHermiteExtendPivot rows columns width length).compute sizes arguments
    let normalized := IntegerMatrix.positivePivotWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2).val (arguments.val 3).val
    (result.1.val, result.2.val) = IntegerMatrix.rowRemainderSweep
      (Row := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1)
      (List.ofFn (arguments.val 4)) normalized.1 normalized.2 :=
  remainderSweepController_correct rows columns width length sizes
    ⟨(fun name => preparedValues rows columns width length name sizes arguments), prepared_valid rows columns width length sizes arguments⟩

/-- An embedded old-row selection gives exactly the shared mathematical pivot-extension operation. -/
theorem integerHermiteExtendPivot_embedding (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteExtendPivot rows columns width length).Arguments sizes //
      (integerHermiteExtendPivot rows columns width length).precondition sizes arguments})
    (activeRows : Fin (MvPolynomial.eval sizes length) ↪ Fin (MvPolynomial.eval sizes rows))
    (selected : arguments.val 4 = (fun index => activeRows index)) :
    let result := (integerHermiteExtendPivot rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteExtendPivot activeRows (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val := by
  have actual := integerHermiteExtendPivot_correct rows columns width length sizes arguments
  have rowList : List.ofFn (arguments.val 4) = (List.finRange (MvPolynomial.eval sizes length)).map activeRows := by
    rw [selected, List.ofFn_eq_map]
  exact actual.trans (congrArg (fun targets => IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval sizes rows)) (arguments.val 0) (arguments.val 1) targets
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val).1
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val).2) rowList)

/-- Pivot extension preserves the full accumulated presentation and unimodular left basis. -/
theorem integerHermiteExtendPivot_preserves (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteExtendPivot rows columns width length).Arguments sizes //
      (integerHermiteExtendPivot rows columns width length).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 3).val * original * right = (arguments.val 2).val)
    (unit : IsUnit (arguments.val 3).val.det) :
    let result := (integerHermiteExtendPivot rows columns width length).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det := by
  have signedPreserves := IntegerMatrix.positivePivotWithLeft_preserves
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    (arguments.val 0) (arguments.val 1) (arguments.val 2).val original (arguments.val 3).val right equation unit
  have swept := IntegerMatrix.rowRemainderSweep_preserves
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    (arguments.val 0) (arguments.val 1) (List.ofFn (arguments.val 4)) arguments.property.2.1
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val).1 original
    (IntegerMatrix.positivePivotWithLeft (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
      (arguments.val 2).val (arguments.val 3).val).2 right signedPreserves.1 signedPreserves.2
  have transfer := congrArg (fun matrices => matrices.2 * original * right = matrices.1 ∧ IsUnit matrices.2.det)
    (integerHermiteExtendPivot_correct rows columns width length sizes arguments)
  exact transfer.mpr swept

end Polytime2.Computation
