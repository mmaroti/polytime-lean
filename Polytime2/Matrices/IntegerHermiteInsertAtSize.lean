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

import Polytime2.Matrices.HermitePivotRead
import Polytime2.Matrices.IntegerRename
import Polytime2.Matrices.IntegerResize
import Polytime2.Matrices.HermiteInsertionResult
import Polytime2.Matrices.IntegerHermiteInsertRow

/-! # Hermite row insertion at a named runtime rank

Prepare live pivot coordinates and view the original matrices at renamed
polynomial dimensions. Invoke the existing insertion algorithm at the named
rank. The caller must supply the actual rank and an admissible pivot block.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

private noncomputable def insertion (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  integerHermiteInsertRow (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width) (MvPolynomial.X rankName)

private noncomputable def inputs (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Fin 3 → EncodedDomain Parameter
  | 0 => ((hermitePivotSelection rows columns).prod (boundedIndex rows)).renameParameters names
  | 1 => (integerMatrices rows columns width).renameParameters names
  | 2 => (integerMatrices rows rows width).renameParameters names

private noncomputable def coordinates (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  (hermitePivotInsertionCoordinates rows columns names rankName).withArguments
    (inputs rows columns width names) (MultiTape.oneTape 0) (by intros; rfl)

private noncomputable def preparedValues (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (name : Fin 4) (sizes : Parameter → ℕ)
    (arguments : {arguments : (coordinates rows columns width names rankName).Arguments sizes //
      (coordinates rows columns width names rankName).precondition sizes arguments}) :
    ((insertion rows columns width names rankName).inputDomains name).Carrier sizes :=
  match name with
  | 0 => ((coordinates rows columns width names rankName).compute sizes arguments).1
  | 1 => ((coordinates rows columns width names rankName).compute sizes arguments).2
  | 2 => integerMatricesRenameValues rows columns width names sizes (arguments.val 1)
  | 3 => integerMatricesRenameValues rows rows width names sizes (arguments.val 2)

private def allowed (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : (coordinates rows columns width names rankName).Arguments sizes) : Prop :=
  ∃ valid : (coordinates rows columns width names rankName).precondition sizes arguments,
    (insertion rows columns width names rankName).precondition sizes
      (fun name => preparedValues rows columns width names rankName name sizes ⟨arguments, valid⟩)

/-- Invoke certified row insertion using the stored rank and its admissible pivot block. -/
noncomputable def integerHermiteInsertAtSize (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter (Fin 3) :=
  (insertion rows columns width names rankName).onResults (inputs rows columns width names)
    (allowed rows columns width names rankName)
    (fun name sizes arguments => preparedValues rows columns width names rankName name sizes
      ⟨arguments.val, arguments.property.choose⟩)
    (by intro sizes arguments; exact arguments.property.choose_spec)

/-- Exact rank, an excluded incoming row, and a positive upper pivot block permit insertion. -/
theorem integerHermiteInsertAtSize_permitted (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteInsertAtSize rows columns width names rankName).Arguments sizes)
    (rank : (arguments 0).1.1 = sizes rankName)
    (excluded : (arguments 0).2 ∉ Set.range (arguments 0).1.2.1)
    (positive : ∀ index, 0 < (arguments 1).val ((arguments 0).1.2.1 index) ((arguments 0).1.2.2 index))
    (upper : ∀ row column, column < row →
      (arguments 1).val ((arguments 0).1.2.1 row) ((arguments 0).1.2.2 column) = 0) :
    (integerHermiteInsertAtSize rows columns width names rankName).precondition sizes arguments := by
  have distinct := hermitePivotInsertionCoordinates_injective rows columns names rankName sizes
    ⟨(fun _ => arguments 0), rank⟩ excluded
  refine ⟨rank, distinct.1, distinct.2, ?_, ?_⟩
  · intro index
    let old : Fin (arguments 0).1.1 := ⟨index.val, by rw [rank]; simpa using index.isLt⟩
    dsimp only [preparedValues, coordinates, Computation.withArguments,
      hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, integerMatricesRenameValues,
      successorValues, snocValues]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_castSucc]
    exact positive old
  · intro row column before
    let oldRow : Fin (arguments 0).1.1 := ⟨row.val, by rw [rank]; simpa using row.isLt⟩
    let oldColumn : Fin (arguments 0).1.1 := ⟨column.val, by rw [rank]; simpa using column.isLt⟩
    dsimp only [preparedValues, coordinates, Computation.withArguments,
      hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, integerMatricesRenameValues,
      successorValues, snocValues]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_castSucc]
    exact upper oldRow oldColumn (by simpa only [Fin.lt_def] using before)

/-- All preparation and the complete insertion are composed through certified operations. -/
theorem integerHermiteInsertAtSize_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerHermiteInsertAtSize rows columns width names rankName).Realizable := by
  have ready := (hermitePivotInsertionCoordinates_realizable rows columns names rankName).withArguments
    (inputs rows columns width names) (MultiTape.oneTape 0) (by intros; rfl)
  have prepared := ready.withPrecondition (allowed rows columns width names rankName)
    (by intro sizes arguments valid; exact valid.choose)
  apply (integerHermiteInsertRow_realizable (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width) (MvPolynomial.X rankName)).onResults
    (inputs rows columns width names) (allowed rows columns width names rankName)
    (fun name sizes arguments => preparedValues rows columns width names rankName name sizes
      ⟨arguments.val, arguments.property.choose⟩)
    (by intro sizes arguments; exact arguments.property.choose_spec)
  intro name
  fin_cases name
  · exact prepared.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  · exact prepared.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  · exact ((integerMatrixRenamedView_realizable rows columns width names).withArguments
      (inputs rows columns width names) (MultiTape.oneTape 1) (by intros; rfl)).withPrecondition
      (allowed rows columns width names rankName) (by intros; trivial)
  · exact ((integerMatrixRenamedView_realizable rows rows width names).withArguments
      (inputs rows columns width names) (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition
      (allowed rows columns width names rankName) (by intros; trivial)

/-- The returned matrices and optional pivot agree with mathematical insertion
for any embeddings with the supplied old coordinates and incoming last row. -/
theorem integerHermiteInsertAtSize_correct (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSize rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSize rows columns width names rankName).precondition sizes arguments})
    (rank : (arguments.val 0).1.1 = sizes rankName)
    (selectedRows : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName) + 1) ↪
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)))
    (pivotColumns : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) →
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns)))
    (oldRows : ∀ index : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)), (selectedRows index.castSucc).val =
      ((arguments.val 0).1.2.1 ⟨index.val, by rw [rank]; simpa using index.isLt⟩).val)
    (incomingRow : (selectedRows (Fin.last (MvPolynomial.eval sizes (MvPolynomial.X rankName)))).val =
      (arguments.val 0).2.val)
    (columnsEqual : ∀ index : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)), (pivotColumns index).val =
      ((arguments.val 0).1.2.2 ⟨index.val, by rw [rank]; simpa using index.isLt⟩).val) :
    let result := (integerHermiteInsertAtSize rows columns width names rankName).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) = IntegerMatrix.hermiteInsertRow selectedRows pivotColumns
      (integerMatricesRenameValues rows columns width names sizes (arguments.val 1)).val
      (integerMatricesRenameValues rows rows width names sizes (arguments.val 2)).val := by
  let prepared := fun name => preparedValues rows columns width names rankName name sizes
    ⟨arguments.val, arguments.property.choose⟩
  let actualRows : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName) + 1) ↪
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)) :=
    ⟨successorValues (MvPolynomial.X rankName) sizes (prepared 0), arguments.property.choose_spec.1⟩
  have rowsEqual : actualRows = selectedRows := by
    apply Function.Embedding.ext
    intro index
    refine Fin.lastCases ?_ ?_ index
    · apply Fin.ext
      change (successorValues (MvPolynomial.X rankName) sizes (prepared 0)
        (Fin.last (MvPolynomial.eval sizes (MvPolynomial.X rankName)))).val = _
      dsimp only [actualRows, prepared, preparedValues, coordinates, Computation.withArguments,
        hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, successorValues, snocValues]
      simp only [Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_last]
      exact incomingRow.symm
    · intro old
      apply Fin.ext
      change (successorValues (MvPolynomial.X rankName) sizes (prepared 0) old.castSucc).val = _
      dsimp only [actualRows, prepared, preparedValues, coordinates, Computation.withArguments,
        hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, successorValues, snocValues]
      simp only [Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_castSucc]
      exact (oldRows old).symm
  have columnsSame : prepared 1 = pivotColumns := by
    funext index
    apply Fin.ext
    exact (columnsEqual index).symm
  have actual := integerHermiteInsertRow_correct (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width) (MvPolynomial.X rankName) sizes
    ⟨prepared, arguments.property.choose_spec⟩
  change _ = IntegerMatrix.hermiteInsertRow actualRows (prepared 1) _ _ at actual
  rw [rowsEqual, columnsSame] at actual
  exact actual

/-- Ignoring equal finite-dimension casts, insertion returns exactly the host
mathematical result on the original matrix, basis, and snoc embedding. -/
theorem integerHermiteInsertAtSize_correct_host (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSize rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSize rows columns width names rankName).precondition sizes arguments})
    (rank : (arguments.val 0).1.1 = sizes rankName)
    (excluded : (arguments.val 0).2 ∉ Set.range (arguments.val 0).1.2.1) :
    let result := (integerHermiteInsertAtSize rows columns width names rankName).compute sizes arguments
    HEq ((result.1.1.val, result.1.2.val), result.2)
      (IntegerMatrix.hermiteInsertRow (Fin.Embedding.snoc (arguments.val 0).1.2.1 excluded)
        (arguments.val 0).1.2.2 (arguments.val 1).val (arguments.val 2).val) := by
  let prepared := fun name => preparedValues rows columns width names rankName name sizes
    ⟨arguments.val, arguments.property.choose⟩
  let actualRows : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName) + 1) ↪
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)) :=
    ⟨successorValues (MvPolynomial.X rankName) sizes (prepared 0), arguments.property.choose_spec.1⟩
  have actual := integerHermiteInsertRow_correct (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width) (MvPolynomial.X rankName) sizes
    ⟨prepared, arguments.property.choose_spec⟩
  change _ = IntegerMatrix.hermiteInsertRow actualRows (prepared 1) _ _ at actual
  apply (heq_of_eq actual).trans
  have pivotsEqual : MvPolynomial.eval sizes (MvPolynomial.X rankName) = (arguments.val 0).1.1 :=
    (MvPolynomial.eval_X rankName).trans rank.symm
  apply IntegerMatrix.hermiteInsertRow_congr (MvPolynomial.eval_rename names sizes rows)
    (MvPolynomial.eval_rename names sizes columns) pivotsEqual
  · intro first
    refine Fin.lastCases ?_ ?_ first
    · intro second same
      have lastEqual : second = Fin.last (arguments.val 0).1.1 := by
        apply Fin.ext
        simpa only [Fin.val_last, pivotsEqual] using same.symm
      rw [lastEqual, Fin.Embedding.snoc_last]
      change (successorValues (MvPolynomial.X rankName) sizes (prepared 0)
        (Fin.last (MvPolynomial.eval sizes (MvPolynomial.X rankName)))).val = _
      dsimp only [prepared, preparedValues, coordinates, Computation.withArguments,
        hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, successorValues, snocValues]
      simp only [Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_last]
      rfl
    · intro old second same
      have below : second.val < (arguments.val 0).1.1 := by
        have bound := old.isLt
        simp only [Fin.val_castSucc] at same
        omega
      let oldSecond : Fin (arguments.val 0).1.1 := ⟨second.val, below⟩
      have secondEqual : second = oldSecond.castSucc := Fin.ext rfl
      rw [secondEqual, Fin.Embedding.snoc_castSucc]
      change (successorValues (MvPolynomial.X rankName) sizes (prepared 0) old.castSucc).val = _
      dsimp only [prepared, preparedValues, coordinates, Computation.withArguments,
        hermitePivotInsertionCoordinates, hermitePivotIncomingAtSize, successorValues, snocValues]
      simp only [Fin.val_cast, Fin.cast_cast, Fin.cast_refl, id_eq, Fin.snoc_castSucc]
      apply congrArg (fun index => ((arguments.val 0).1.2.1 index).val)
      exact Fin.ext same
  · intro first second same
    change (prepared 1 first).val = _
    apply congrArg (fun index => ((arguments.val 0).1.2.2 index).val)
    exact Fin.ext same
  · intro firstRow secondRow firstColumn secondColumn rowValues columnValues
    exact congrArg₂ (arguments.val 1).val (Fin.ext rowValues) (Fin.ext columnValues)
  · intro firstRow secondRow firstColumn secondColumn rowValues columnValues
    exact congrArg₂ (arguments.val 2).val (Fin.ext rowValues) (Fin.ext columnValues)

/-- The named-rank call retains the actual presentation and unimodular left basis. -/
theorem integerHermiteInsertAtSize_preserves (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSize rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSize rows columns width names rankName).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)))
      (Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns))) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns)))
      (Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns))) ℤ)
    (equation : (integerMatricesRenameValues rows rows width names sizes (arguments.val 2)).val * original * right =
      (integerMatricesRenameValues rows columns width names sizes (arguments.val 1)).val)
    (unit : IsUnit (integerMatricesRenameValues rows rows width names sizes (arguments.val 2)).val.det) :
    let result := (integerHermiteInsertAtSize rows columns width names rankName).compute sizes arguments
    result.1.2.val * original * right = result.1.1.val ∧ IsUnit result.1.2.val.det :=
  integerHermiteInsertRow_preserves (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width) (MvPolynomial.X rankName) sizes
    ⟨(fun name => preparedValues rows columns width names rankName name sizes
      ⟨arguments.val, arguments.property.choose⟩), arguments.property.choose_spec⟩ original right equation unit

/-- Insertion output capacity derived from original width and row count. -/
noncomputable def hermiteInsertOutputWidth (width rows : MvPolynomial HostParameter ℕ) :=
  2 * hermiteIncomingWorkspace width rows + 1

private theorem insertionWidth_le (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSize rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSize rows columns width names rankName).precondition sizes arguments}) :
    MvPolynomial.eval sizes (2 * hermiteIncomingWorkspace (MvPolynomial.rename names width) (MvPolynomial.X rankName) + 1) ≤
      MvPolynomial.eval sizes (MvPolynomial.rename names (hermiteInsertOutputWidth width rows)) := by
  have rank := arguments.property.choose
  have countBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) rows := by
    rw [← rank]
    simpa using Fintype.card_le_of_injective (arguments.val 0).1.2.1 (arguments.val 0).1.2.1.injective
  simp only [hermiteInsertOutputWidth, hermiteIncomingWorkspace, hermiteIncomingWorkspaceExtra,
    map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  gcongr

/-- Return insertion at a width derived from host dimensions, independent of decoded rank. -/
noncomputable def integerHermiteInsertAtSizeBounded (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter (Fin 3) where
  inputDomains := (integerHermiteInsertAtSize rows columns width names rankName).inputDomains
  outputDomain := hermiteInsertionResult (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names (hermiteInsertOutputWidth width rows))
  precondition := (integerHermiteInsertAtSize rows columns width names rankName).precondition
  compute sizes arguments :=
    let result := (integerHermiteInsertAtSize rows columns width names rankName).compute sizes arguments
    let growth := pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) (insertionWidth_le rows columns width names rankName sizes arguments)
    ((⟨result.1.1.val, fun row column => (result.1.1.property row column).trans_le growth⟩,
      ⟨result.1.2.val, fun row column => (result.1.2.property row column).trans_le growth⟩), result.2)

/-- Widen and narrow through a common width; all output preparation is certified. -/
theorem integerHermiteInsertAtSizeBounded_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerHermiteInsertAtSizeBounded rows columns width names rankName).Realizable := by
  let computation := integerHermiteInsertAtSizeBounded rows columns width names rankName
  let r := MvPolynomial.rename names rows
  let c := MvPolynomial.rename names columns
  let sourceWidth := 2 * hermiteIncomingWorkspace (MvPolynomial.rename names width) (MvPolynomial.X rankName) + 1
  let targetWidth := MvPolynomial.rename names (hermiteInsertOutputWidth width rows)
  let matrix := integerMatrices r c targetWidth
  let basis := integerMatrices r r targetWidth
  have actual := integerHermiteInsertAtSize_realizable rows columns width names rankName
  have pair := actual.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldMatrix := pair.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldBasis := pair.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have pivot := actual.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have matrixReady := oldMatrix.followedBy (integerMatrixResize_realizable r c sourceWidth targetWidth) rfl (by
    intro sizes arguments valid
    exact ((computation.compute sizes ⟨arguments, valid⟩).1.1).property)
  have basisReady := oldBasis.followedBy (integerMatrixResize_realizable r r sourceWidth targetWidth) rfl (by
    intro sizes arguments valid
    exact ((computation.compute sizes ⟨arguments, valid⟩).1.2).property)
  have matrices := Realizable.pairOutputs computation.inputDomains matrix basis computation.precondition
    _ _ matrixReady basisReady
  have result := Realizable.pairOutputs computation.inputDomains (matrix.prod basis) (arraySearchResult c)
    computation.precondition _ _ matrices pivot
  exact result.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- Rank-independent output resizing preserves both matrices and the optional pivot. -/
theorem integerHermiteInsertAtSizeBounded_values (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSizeBounded rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSizeBounded rows columns width names rankName).precondition sizes arguments}) :
    let result := (integerHermiteInsertAtSizeBounded rows columns width names rankName).compute sizes arguments
    let original := (integerHermiteInsertAtSize rows columns width names rankName).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) = ((original.1.1.val, original.1.2.val), original.2) := rfl

/-- The bounded insertion callee returns the original host result codec. -/
noncomputable def integerHermiteInsertAtSizeOriginal (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter (Fin 3) :=
  (integerHermiteInsertAtSizeBounded rows columns width names rankName).followedBy
    (hermiteInsertionResultOriginalView rows columns (hermiteInsertOutputWidth width rows) names) rfl (by intros; trivial)

/-- Insertion, fixed output widths, and host-codec reconstruction are certified by composition. -/
theorem integerHermiteInsertAtSizeOriginal_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerHermiteInsertAtSizeOriginal rows columns width names rankName).Realizable :=
  (integerHermiteInsertAtSizeBounded_realizable rows columns width names rankName).followedBy
    (hermiteInsertionResultOriginalView_realizable rows columns (hermiteInsertOutputWidth width rows) names) rfl
    (by intros; trivial)

/-- Host-codec reconstruction yields ordinary equality to insertion on the original inputs. -/
theorem integerHermiteInsertAtSizeOriginal_correct (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertAtSizeOriginal rows columns width names rankName).Arguments sizes //
      (integerHermiteInsertAtSizeOriginal rows columns width names rankName).precondition sizes arguments})
    (rank : (arguments.val 0).1.1 = sizes rankName)
    (excluded : (arguments.val 0).2 ∉ Set.range (arguments.val 0).1.2.1) :
    let result := (integerHermiteInsertAtSizeOriginal rows columns width names rankName).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) =
      IntegerMatrix.hermiteInsertRow (Fin.Embedding.snoc (arguments.val 0).1.2.1 excluded)
        (arguments.val 0).1.2.2 (arguments.val 1).val (arguments.val 2).val :=
  IntegerMatrix.hermiteInsertResult_cast (MvPolynomial.eval_rename names sizes rows)
    (MvPolynomial.eval_rename names sizes columns) _ _
    (integerHermiteInsertAtSize_correct_host rows columns width names rankName sizes arguments rank excluded)

end Polytime2.Computation
