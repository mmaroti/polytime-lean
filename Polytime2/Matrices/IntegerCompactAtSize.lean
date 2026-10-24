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

import Polytime2.Matrices.IntegerCompactSelected
import Polytime2.Matrices.HermitePivotRead
import Polytime2.Matrices.IntegerRename

/-! # Compaction at a named Hermite rank

Read the live embeddings from pivot metadata at the named rank, then apply
selected-pivot compaction. The only precondition is equality of the metadata
rank and the named size. Matrix and basis widths remain independent.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

private noncomputable def compactAtSizeInputs
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Fin 4 → EncodedDomain Parameter
  | 0 => (hermitePivotSelection rows columns).renameParameters names
  | 1 => (integerMatrices rows columns matrixWidth).renameParameters names
  | 2 => (integerMatrices rows rows leftWidth).renameParameters names
  | 3 => (integerMatrices columns columns rightWidth).renameParameters names

private noncomputable def compactAtSizeCoordinates
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  (hermitePivotCoordinatesAtSize rows columns names rankName).withArguments
    (compactAtSizeInputs rows columns matrixWidth leftWidth rightWidth names)
    (MultiTape.oneTape 0) (by intros; rfl)

private noncomputable def compactAtSizeCallee
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  integerCompactSelected (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names matrixWidth)
    (MvPolynomial.rename names leftWidth) (MvPolynomial.rename names rightWidth)

private noncomputable def compactAtSizeValues
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (name : Fin 5) (sizes : Parameter → ℕ)
    (arguments : {arguments :
      (compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).Arguments sizes //
      (compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).precondition sizes arguments}) :
    ((compactAtSizeCallee rows columns matrixWidth leftWidth rightWidth names rankName).inputDomains name).Carrier sizes :=
  match name with
  | 0 => ((compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments).1
  | 1 => ((compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments).2
  | 2 => integerMatricesRenameValues rows columns matrixWidth names sizes (arguments.val 1)
  | 3 => integerMatricesRenameValues rows rows leftWidth names sizes (arguments.val 2)
  | 4 => integerMatricesRenameValues columns columns rightWidth names sizes (arguments.val 3)

/-- Compact using metadata whose rank is the named size. -/
noncomputable def integerCompactAtSize
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter (Fin 4) :=
  (compactAtSizeCallee rows columns matrixWidth leftWidth rightWidth names rankName).onResults
    (compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).inputDomains
    (compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName).precondition
    (compactAtSizeValues rows columns matrixWidth leftWidth rightWidth names rankName)
    (by
      intro sizes arguments
      exact hermitePivotCoordinatesAtSize_injective rows columns names rankName sizes
        ⟨fun _ => arguments.val 0, arguments.property⟩)

/-- Metadata reading and matrix views compose with selected-pivot compaction. -/
theorem integerCompactAtSize_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).Realizable := by
  let coordinates := compactAtSizeCoordinates rows columns matrixWidth leftWidth rightWidth names rankName
  have ready := (hermitePivotCoordinatesAtSize_realizable rows columns names rankName).withArguments
    coordinates.inputDomains (MultiTape.oneTape 0) (by intros; rfl)
  apply (integerCompactSelected_realizable (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names matrixWidth)
    (MvPolynomial.rename names leftWidth) (MvPolynomial.rename names rightWidth)).onResults
    coordinates.inputDomains coordinates.precondition
    (compactAtSizeValues rows columns matrixWidth leftWidth rightWidth names rankName) _
  intro name
  fin_cases name
  · exact ready.fst
  · exact ready.snd
  · exact ((integerMatrixRenamedView_realizable rows columns matrixWidth names).withArguments
      coordinates.inputDomains (MultiTape.oneTape 1) (by intros; rfl)).withPrecondition _ (by intros; trivial)
  · exact ((integerMatrixRenamedView_realizable rows rows leftWidth names).withArguments
      coordinates.inputDomains (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition _ (by intros; trivial)
  · exact ((integerMatrixRenamedView_realizable columns columns rightWidth names).withArguments
      coordinates.inputDomains (MultiTape.oneTape 3) (by intros; rfl)).withPrecondition _ (by intros; trivial)

/-- Equality with the named rank is the complete input requirement. -/
theorem integerCompactAtSize_permitted
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).Arguments sizes)
    (rank : (arguments 0).1 = sizes rankName) :
    (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).precondition sizes arguments := rank

/-- Named-rank compaction is exactly the canonical mathematical permutation action. -/
theorem integerCompactAtSize_correct
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments :
      (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).Arguments sizes //
      (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).precondition sizes arguments}) :
    let ready := (hermitePivotCoordinatesAtSize rows columns names rankName).compute sizes
      ⟨fun _ => arguments.val 0, arguments.property⟩
    let distinct := hermitePivotCoordinatesAtSize_injective rows columns names rankName sizes
      ⟨fun _ => arguments.val 0, arguments.property⟩
    let selectedRows : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) ↪
        Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)) :=
      ⟨ready.1, distinct.1⟩
    let selectedColumns : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) ↪
        Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns)) :=
      ⟨ready.2, distinct.2⟩
    let result := (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.permuteWithBases (IntegerMatrix.pivotPermutation selectedRows)
        (IntegerMatrix.pivotPermutation selectedColumns)
        (integerMatricesRenameValues rows columns matrixWidth names sizes (arguments.val 1)).val
        (integerMatricesRenameValues rows rows leftWidth names sizes (arguments.val 2)).val
        (integerMatricesRenameValues columns columns rightWidth names sizes (arguments.val 3)).val := by
  exact integerCompactSelected_correct (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names matrixWidth)
    (MvPolynomial.rename names leftWidth) (MvPolynomial.rename names rightWidth) sizes
    ⟨fun name => compactAtSizeValues rows columns matrixWidth leftWidth rightWidth names rankName name sizes arguments,
      hermitePivotCoordinatesAtSize_injective rows columns names rankName sizes
        ⟨fun _ => arguments.val 0, arguments.property⟩⟩

/-- Compaction returns the host result codec, independent of the named rank. -/
noncomputable def integerCompactAtSizeOriginal
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter (Fin 4) :=
  (integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).followedBy
    (integerMatrixPresentationOriginalView rows columns matrixWidth leftWidth rightWidth names) rfl (by intros; trivial)

/-- Compaction and the host result view are certified by composition. -/
theorem integerCompactAtSizeOriginal_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth names rankName).Realizable :=
  (integerCompactAtSize_realizable rows columns matrixWidth leftWidth rightWidth names rankName).followedBy
    (integerMatrixPresentationOriginalView_realizable rows columns matrixWidth leftWidth rightWidth names)
    rfl (by intros; trivial)

/-- Returning to host dimensions gives exactly the host pivot-permutation action. -/
theorem integerCompactAtSizeOriginal_correct
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments :
      (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth names rankName).Arguments sizes //
      (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth names rankName).precondition sizes arguments}) :
    let result := (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.permuteWithBases (IntegerMatrix.pivotPermutation (arguments.val 0).2.1)
        (IntegerMatrix.pivotPermutation (arguments.val 0).2.2)
        (arguments.val 1).val (arguments.val 2).val (arguments.val 3).val := by
  let ready := (hermitePivotCoordinatesAtSize rows columns names rankName).compute sizes
    ⟨fun _ => arguments.val 0, arguments.property⟩
  have distinct := hermitePivotCoordinatesAtSize_injective rows columns names rankName sizes
    ⟨fun _ => arguments.val 0, arguments.property⟩
  let selectedRows : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) ↪
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)) := ⟨ready.1, distinct.1⟩
  let selectedColumns : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) ↪
      Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns)) := ⟨ready.2, distinct.2⟩
  have rankEqual : MvPolynomial.eval sizes (MvPolynomial.X rankName) = (arguments.val 0).1 :=
    (MvPolynomial.eval_X rankName).trans arguments.property.symm
  have rowSame (first : Fin (MvPolynomial.eval sizes (MvPolynomial.rename names rows)))
      (second : Fin (MvPolynomial.eval (sizes ∘ names) rows)) (same : first.val = second.val) :
      (IntegerMatrix.pivotPermutation selectedRows first).val =
        (IntegerMatrix.pivotPermutation (arguments.val 0).2.1 second).val := by
    apply IntegerMatrix.pivotPermutation_congr rankEqual (MvPolynomial.eval_rename names sizes rows)
      selectedRows (arguments.val 0).2.1 _ first second same
    intro first second same
    change ((arguments.val 0).2.1 _).val = _
    exact congrArg (fun index => ((arguments.val 0).2.1 index).val) (Fin.ext same)
  have columnSame (first : Fin (MvPolynomial.eval sizes (MvPolynomial.rename names columns)))
      (second : Fin (MvPolynomial.eval (sizes ∘ names) columns)) (same : first.val = second.val) :
      (IntegerMatrix.pivotPermutation selectedColumns first).val =
        (IntegerMatrix.pivotPermutation (arguments.val 0).2.2 second).val := by
    apply IntegerMatrix.pivotPermutation_congr rankEqual (MvPolynomial.eval_rename names sizes columns)
      selectedColumns (arguments.val 0).2.2 _ first second same
    intro first second same
    change ((arguments.val 0).2.2 _).val = _
    exact congrArg (fun index => ((arguments.val 0).2.2 index).val) (Fin.ext same)
  have actual := integerCompactAtSize_correct rows columns matrixWidth leftWidth rightWidth names rankName sizes arguments
  change _ = IntegerMatrix.permuteWithBases (IntegerMatrix.pivotPermutation selectedRows)
    (IntegerMatrix.pivotPermutation selectedColumns) _ _ _ at actual
  apply Prod.ext
  · funext row column
    have entry := congrArg (fun result => result.1
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)) actual
    change _ = (arguments.val 1).val _ _ at entry
    change ((integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments).1.val
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column) = _
    refine entry.trans ?_
    apply congrArg₂ (arguments.val 1).val
    · apply Fin.ext
      exact rowSame (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row) row rfl
    · apply Fin.ext
      exact columnSame (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column) column rfl
  · apply Prod.ext
    · funext row column
      have entry := congrArg (fun result => result.2.1
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm column)) actual
      change _ = (arguments.val 2).val _ _ at entry
      change ((integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments).2.1.val
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm column) = _
      refine entry.trans ?_
      apply congrArg (fun index => (arguments.val 2).val index column)
      apply Fin.ext
      exact rowSame (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row) row rfl
    · funext row column
      have entry := congrArg (fun result => result.2.2
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)) actual
      change _ = (arguments.val 3).val _ _ at entry
      change ((integerCompactAtSize rows columns matrixWidth leftWidth rightWidth names rankName).compute sizes arguments).2.2.val
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column) = _
      refine entry.trans ?_
      apply congrArg ((arguments.val 3).val row)
      apply Fin.ext
      exact columnSame (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column) column rfl

end Polytime2.Computation
