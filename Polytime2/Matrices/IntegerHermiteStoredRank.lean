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

import Polytime2.Matrices.IntegerHermiteInsertAtSize
import Polytime2.Computation.ComputedHost

/-! # Automatic insertion at the stored Hermite rank

Read the rank from the pivot selection and retain the host matrix dimensions.
The computed-size call uses the complete named-rank insertion callee. Its
result returns the host matrices and optional new column directly.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def fields (rows columns width : MvPolynomial Parameter ℕ) : Fin 3 → EncodedDomain Parameter
  | 0 => (hermitePivotSelection rows columns).prod (boundedIndex rows)
  | 1 => integerMatrices rows columns width
  | 2 => integerMatrices rows rows width

private noncomputable def unpack (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : (Parameter ⊕ Unit) → ℕ)
    (value : ((record 3 (fields rows columns width)).renameParameters Sum.inl).Carrier sizes) :
    (integerHermiteInsertAtSizeOriginal rows columns width Sum.inl (.inr ())).Arguments sizes :=
  fun name => match name with
    | 0 => value 0
    | 1 => value 1
    | 2 => value 2

private noncomputable def callee (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerHermiteInsertAtSizeOriginal rows columns width Sum.inl (.inr ())).withRenamedRecordArgument
    (fields rows columns width) Sum.inl (by intro name; fin_cases name <;> rfl)

private theorem callee_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (callee rows columns width).Realizable :=
  (integerHermiteInsertAtSizeOriginal_realizable rows columns width Sum.inl (.inr ())).withRenamedRecordArgument
    (fields rows columns width) Sum.inl (by intro name; fin_cases name <;> rfl)

private noncomputable def bounds (rows : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ := fun _ => rows

private noncomputable def counts (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (record 3 (fields rows columns width)).Carrier sizes) : (computedSizeDomain (bounds rows)).Carrier sizes :=
  fun _ => (hermitePivotSelectionRank rows columns).compute sizes ⟨fun _ => (value 0).1, trivial⟩

private noncomputable def frame (rows columns width : MvPolynomial Parameter ℕ) :=
  computedHostFrame (bounds rows) (record 3 (fields rows columns width)) (counts rows columns width)

private theorem readers_realizable (rows columns width : MvPolynomial Parameter ℕ) (name : Unit) :
    (unaryMap (record 3 (fields rows columns width)) (boundedUnary (bounds rows name)) (fun _ _ => True)
      (fun sizes value => counts rows columns width sizes value.val name)).Realizable := by
  have selected := (recordProjection_realizable 3 (fields rows columns width) 0).fst
  exact selected.followedBy (hermitePivotSelectionRank_realizable rows columns) rfl (by intros; trivial)

private noncomputable def call (rows columns width : MvPolynomial Parameter ℕ) :=
  (callee rows columns width).atComputedHostSizes (bounds rows)
    (record 3 (fields rows columns width)) (hermiteInsertionResult rows columns (hermiteInsertOutputWidth width rows))
    (counts rows columns width) rfl rfl

/-- Insert using the rank decoded from metadata; no caller-supplied rank size is needed. -/
private noncomputable def implementation (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  call rows columns width

/-- An excluded incoming row and a positive upper pivot block permit the stored-rank call. -/
private theorem implementation_permitted (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (implementation rows columns width).Arguments sizes)
    (excluded : (arguments () 0).2 ∉ Set.range (arguments () 0).1.2.1)
    (positive : ∀ index, 0 < (arguments () 1).val
      ((arguments () 0).1.2.1 index) ((arguments () 0).1.2.2 index))
    (upper : ∀ row column, column < row → (arguments () 1).val
      ((arguments () 0).1.2.1 row) ((arguments () 0).1.2.2 column) = 0) :
    (implementation rows columns width).precondition sizes arguments := by
  dsimp only [implementation, call, Computation.atComputedHostSizes, Computation.atComputedHostInput, callee, Computation.onResults]
  apply integerHermiteInsertAtSize_permitted
  · rfl
  · exact excluded
  · exact positive
  · exact upper

/-- Insert at the decoded rank. The incoming row is excluded from the old selection,
whose pivot block has positive diagonal and zeros below it. -/
noncomputable def integerHermiteInsertHost (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (implementation rows columns width).withPrecondition
    (fun _ arguments => (arguments () 0).2 ∉ Set.range (arguments () 0).1.2.1 ∧
      (∀ index, 0 < (arguments () 1).val ((arguments () 0).1.2.1 index) ((arguments () 0).1.2.2 index)) ∧
      (∀ row column, column < row → (arguments () 1).val
        ((arguments () 0).1.2.1 row) ((arguments () 0).1.2.2 column) = 0))
    (by
      intro sizes arguments valid
      exact implementation_permitted rows columns width sizes arguments valid.1 valid.2.1 valid.2.2)

/-- Rank extraction, frame preparation, and the full computed-size call are certified. -/
theorem integerHermiteInsertHost_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteInsertHost rows columns width).Realizable := by
  have ready : (implementation rows columns width).Realizable :=
    (callee_realizable rows columns width).atComputedHostSizes (bounds rows)
      (record 3 (fields rows columns width)) (hermiteInsertionResult rows columns (hermiteInsertOutputWidth width rows))
      (counts rows columns width) rfl rfl
      (readers_realizable rows columns width)
  exact ready.withPrecondition _ (by
    intro sizes arguments valid
    exact implementation_permitted rows columns width sizes arguments valid.1 valid.2.1 valid.2.2)

/-- In the host dimensions, the stored-rank values are exactly mathematical insertion. -/
theorem integerHermiteInsertHost_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteInsertHost rows columns width).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) =
      IntegerMatrix.hermiteInsertRow (Fin.Embedding.snoc (arguments.val () 0).1.2.1 arguments.property.1)
        (arguments.val () 0).1.2.2 (arguments.val () 1).val (arguments.val () 2).val := by
  simp only [integerHermiteInsertHost, implementation, call, Computation.withPrecondition, atComputedHostSizes_compute]
  let framed := (frame rows columns width).compute sizes ⟨arguments.val, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds rows)) sizes framed.1
  let values := unpack rows columns width actual framed.2
  have valid : (integerHermiteInsertAtSizeOriginal rows columns width Sum.inl (.inr ())).precondition actual values :=
    implementation_permitted rows columns width sizes arguments.val
      arguments.property.1 arguments.property.2.1 arguments.property.2.2
  exact integerHermiteInsertAtSizeOriginal_correct rows columns width Sum.inl (.inr ()) actual
    ⟨values, valid⟩ rfl arguments.property.1

/-- Host output retains the accumulated presentation and unimodular left basis. -/
theorem integerHermiteInsertHost_preserves (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val () 2).val * original * right = (arguments.val () 1).val)
    (unit : IsUnit (arguments.val () 2).val.det) :
    let result := (integerHermiteInsertHost rows columns width).compute sizes arguments
    result.1.2.val * original * right = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have preserved := IntegerMatrix.hermiteInsertRow_preserves
    (Row := Fin (MvPolynomial.eval sizes rows))
    (Fin.Embedding.snoc (arguments.val () 0).1.2.1 arguments.property.1)
    (arguments.val () 0).1.2.2 (arguments.val () 1).val original (arguments.val () 2).val
    right equation unit
  rw [← integerHermiteInsertHost_correct rows columns width sizes arguments] at preserved
  exact preserved

/-- Any returned new column is excluded from the old pivot embedding. -/
theorem integerHermiteInsertHost_newColumn (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments})
    (column : Fin (MvPolynomial.eval sizes columns))
    (found : ((integerHermiteInsertHost rows columns width).compute sizes arguments).2 = some column) :
    column ∉ Set.range (arguments.val () 0).1.2.2 := by
  have exactPivot := congrArg Prod.snd (integerHermiteInsertHost_correct rows columns width sizes arguments)
  exact (IntegerMatrix.hermiteInsertRow_normalized_some
    (Row := Fin (MvPolynomial.eval sizes rows))
    (Fin.Embedding.snoc (arguments.val () 0).1.2.1 arguments.property.1)
    (arguments.val () 0).1.2.2 (arguments.val () 1).val (arguments.val () 2).val
    (by simpa only [Fin.Embedding.snoc_castSucc] using arguments.property.2.1)
    (by intro row column below; simpa only [Fin.Embedding.snoc_castSucc] using arguments.property.2.2 row column below)
    column (exactPivot.symm.trans found)).1

end Polytime2.Computation
