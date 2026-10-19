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

import Polytime2.GaussJordan.PivotRows

/-! # Complete execution proof for the standard pivot controller -/

namespace Polytime2.StandardGaussJordanPivot

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- The complete pivot controller computes swap-normalize-clear on ordinary
matrices, accepting arbitrary initial result and scratch contents. -/
theorem runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate pivot column : Fin (2 ^ sizes 0))
      (candidateValid : candidate.val < sizes 1) (pivotValid : pivot.val < sizes 1)
      (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (algorithm enumeration)
          ticks (entry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (exit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.pivotStep (Scalar := Scalar) matrix
            ⟨pivot.val, pivotValid⟩ ⟨candidate.val, candidateValid⟩ ⟨column.val, columnValid⟩) := by
  obtain ⟨lookupBound, executeLookup⟩ := lookup_runs enumeration
  obtain ⟨swapBound, executeSwap⟩ := row_runs true enumeration (MatrixRowField.swap (Scalar := Scalar))
  obtain ⟨normalizeBound, executeNormalize⟩ := row_runs false enumeration (MatrixRowField.normalize (Scalar := Scalar))
  obtain ⟨clearBound, executeClear⟩ := clear_runs enumeration
  let matrixBound := (matrixDomain (FieldRow.scalarDomain enumeration)).widthPolynomial
  refine ⟨lookupBound + swapBound + normalizeBound + clearBound + 6 * matrixBound + 12, ?_⟩
  intro sizes initial candidate pivot column candidateValid pivotValid columnValid matrix
    rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  let matrixCode := encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix
  let prepared := Function.update initial workingTape matrixCode
  have originalCode : encoded (domains enumeration originalTape) sizes (matrixEquiv sizes matrix) = matrixCode := rfl
  have inputWidth : (domains enumeration originalTape).width sizes =
      (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes := rfl
  have originalEq : initial originalTape =
      encoded (domains enumeration originalTape) sizes (matrixEquiv sizes matrix) := matrixEq
  have prepareTrace := prepareMatrix_runs enumeration sizes (matrixEquiv sizes matrix) initial
    originalEq (regions workingTape)
  rw [originalCode] at prepareTrace
  have preparedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (prepared name) :=
    fun name => prepareTrace.region name (regions name)
  have preparePreserves (name : TapeName) (readonly : readOnly name = true) :
      prepared name = initial name := prepareTrace.readOnly_tape name readonly
  have within := StandardMatrixEntry.index_lt sizes candidate.val column.val candidateValid columnValid
  obtain ⟨lookupTicks, loaded, lookupCost, lookupTrace, loadedValue, lookupOutside, lookupImmutable⟩ :=
    executeLookup sizes prepared candidate column (matrixEquiv sizes matrix) within columnsFit candidateValid
      columnValid capacity ((preparePreserves candidateTape rfl).trans candidateEq)
      ((preparePreserves columnTape rfl).trans columnEq) (Function.update_self _ _ _)
      (fun parameter => (preparePreserves (sizeTape parameter) rfl).trans (headers parameter)) preparedRegions
  let candidateRow : Fin (sizes 1) := ⟨candidate.val, candidateValid⟩
  let pivotRow : Fin (sizes 1) := ⟨pivot.val, pivotValid⟩
  let pivotColumn : Fin (sizes 2) := ⟨column.val, columnValid⟩
  let coefficient : Scalar := matrix candidateRow pivotColumn
  have coefficientValue : matrixEquiv sizes matrix ⟨candidate.val * sizes 2 + column.val, within⟩ = coefficient := by
    rw [← matrixIndex_eq sizes candidateRow pivotColumn]
    exact matrixEquiv_apply sizes matrix candidateRow pivotColumn
  have coefficientEq : loaded (dataTape 3) =
      encoded (FieldRow.scalarDomain enumeration) Empty.elim coefficient :=
    loadedValue.trans (congrArg (encoded (FieldRow.scalarDomain enumeration) Empty.elim) coefficientValue)
  have loadedMatrix : loaded workingTape = matrixCode :=
    (lookupImmutable (.inr false) rfl).trans (Function.update_self _ _ _)
  have loadedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (loaded name) :=
    fun name => lookupTrace.region name (preparedRegions name)
  have loadedPreserves (name : TapeName) (readonly : readOnly name = true) : loaded name = initial name :=
    (lookupTrace.readOnly_tape name readonly).trans (preparePreserves name readonly)
  obtain ⟨swapTicks, swapped, swapCost, swapTrace, swappedResult, swapOutside, swapImmutable⟩ :=
    executeSwap sizes loaded candidate pivot candidateValid pivotValid coefficient matrix columnsFit capacity
      ((loadedPreserves candidateTape rfl).trans candidateEq)
      ((loadedPreserves pivotTape rfl).trans pivotEq) coefficientEq loadedMatrix
      (fun parameter => (loadedPreserves (sizeTape parameter) rfl).trans (headers parameter)) loadedRegions
  let swappedMatrix := MatrixOperations.swapRows matrix pivotRow candidateRow
  have swapComm : MatrixOperations.swapRows matrix candidateRow pivotRow = swappedMatrix := by
    ext row other
    simp [swappedMatrix, MatrixOperations.swapRows, Equiv.swap_comm]
  have swapResult : swapped (dataTape 5) =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes swappedMatrix :=
    swappedResult.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes)
      ((MatrixRowField.swap_transform coefficient matrix candidateRow pivotRow).trans swapComm))
  have swappedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (swapped name) :=
    fun name => swapTrace.region name (loadedRegions name)
  have firstCommitTrace := commit_runs enumeration sizes swappedMatrix swapped swapResult (swappedRegions workingTape)
  let committed := Function.update swapped workingTape
    (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes swappedMatrix)
  have committedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (committed name) :=
    fun name => firstCommitTrace.region name (swappedRegions name)
  have committedPreserves (name : TapeName) (readonly : readOnly name = true) : committed name = initial name :=
    (firstCommitTrace.readOnly_tape name readonly).trans
      ((swapTrace.readOnly_tape name readonly).trans (loadedPreserves name readonly))
  have savedCoefficient : committed (dataTape 3) =
      encoded (FieldRow.scalarDomain enumeration) Empty.elim coefficient :=
    (Function.update_of_ne (by decide) _ _).trans
      ((swapImmutable (StandardMatrixRows.dataTape 3) rfl).trans coefficientEq)
  obtain ⟨normalizeTicks, normalized, normalizeCost, normalizeTrace, normalizedResult,
      normalizeOutside, normalizeImmutable⟩ :=
    executeNormalize sizes committed candidate pivot candidateValid pivotValid coefficient swappedMatrix
      columnsFit capacity ((committedPreserves candidateTape rfl).trans candidateEq)
      ((committedPreserves pivotTape rfl).trans pivotEq) savedCoefficient (Function.update_self _ _ _)
      (fun parameter => (committedPreserves (sizeTape parameter) rfl).trans (headers parameter)) committedRegions
  let normalizedMatrix := MatrixOperations.scaleRow (Scalar := Scalar) swappedMatrix pivotRow coefficient⁻¹
  have normalizeResult : normalized (dataTape 5) =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes normalizedMatrix :=
    normalizedResult.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes)
      (MatrixRowField.normalize_transform coefficient swappedMatrix candidateRow pivotRow))
  have normalizedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (normalized name) :=
    fun name => normalizeTrace.region name (committedRegions name)
  have secondCommitTrace := commit_runs enumeration sizes normalizedMatrix normalized normalizeResult
    (normalizedRegions workingTape)
  let ready := Function.update normalized workingTape
    (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes normalizedMatrix)
  have readyRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (ready name) :=
    fun name => secondCommitTrace.region name (normalizedRegions name)
  have readyPreserves (name : TapeName) (readonly : readOnly name = true) : ready name = initial name :=
    (secondCommitTrace.readOnly_tape name readonly).trans
      ((normalizeTrace.readOnly_tape name readonly).trans (committedPreserves name readonly))
  obtain ⟨clearTicks, final, clearCost, clearTrace, finalMatrix, clearOutside, clearImmutable⟩ :=
    executeClear sizes ready pivot column pivotValid columnValid normalizedMatrix rowsFit columnsFit capacity
      ((readyPreserves pivotTape rfl).trans pivotEq) ((readyPreserves columnTape rfl).trans columnEq)
      (Function.update_self _ _ _)
      (fun parameter => (readyPreserves (sizeTape parameter) rfl).trans (headers parameter)) readyRegions
  have commitHalt : ∀ symbols, commit 2 symbols = none := by intro symbols; rfl
  have rowHalt : ∀ writeSource operation (symbols : Symbols Alphabet),
      MultiTape.wire rowWiring (StandardMatrixRows.machine writeSource (FieldRow.scalarDomain enumeration) operation)
        (StandardMatrixRows.exit ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
    intro writeSource operation symbols
    simp [MultiTape.wire, StandardMatrixRows.halt]
  let clearEntry := StandardGaussJordanClear.algorithmEntry
    ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let rowEntry := StandardMatrixRows.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let lookupEntry := StandardMatrixEntry.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)
  have tail := secondCommitTrace.sequence (clearColumn enumeration) clearEntry commitHalt clearTrace
  have normalizeTail := normalizeTrace.sequence _ (Sum.inl 0) (rowHalt false _) tail
  have firstCommitTail := firstCommitTrace.sequence _ (Sum.inl rowEntry) commitHalt normalizeTail
  have swapTail := swapTrace.sequence _ (Sum.inl 0) (rowHalt true _) firstCommitTail
  have lookupTail := lookupTrace.sequence _ (Sum.inl rowEntry)
    (by intro symbols; simp [lookup, MultiTape.wire, StandardMatrixEntry.halt]) swapTail
  have complete := prepareTrace.sequence _ (Sum.inl lookupEntry) (by intro symbols; rfl) lookupTail
  let copyCost := 2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2
  let total := (2 * (domains enumeration originalTape).width sizes + 2) +
    (lookupTicks + (swapTicks + (copyCost + (normalizeTicks + (copyCost + clearTicks + 1) + 1) + 1) + 1) + 1) + 1
  have fullTrace : Runs (fun name => (domains enumeration name).width sizes) readOnly
      (algorithm enumeration) total (entry
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
      (exit
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final := by
    simpa only [algorithm, entry, exit, prepareMatrix, commit, swapRows, normalizeRow,
      clearEntry, rowEntry, lookupEntry, total, copyCost] using complete
  refine ⟨total, final, ?_, fullTrace, ?_⟩
  · dsimp only [total, copyCost]
    simp only [matrixBound, map_add, map_mul, map_ofNat]
    rw [inputWidth]
    simp only [EncodedDomain.width]
    omega
  · exact finalMatrix
def sizeTapes : Fin 3 ↪ TapeName := StandardGaussJordanClear.sizeTapes.trans clearWiring

end Polytime2.StandardGaussJordanPivot
