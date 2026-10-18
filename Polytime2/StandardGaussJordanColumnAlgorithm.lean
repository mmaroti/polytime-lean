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

import Polytime2.StandardGaussJordanColumnInit

/-! # Complete standard-convention Gauss–Jordan column -/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

theorem runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow column : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      (pivotBound : pivotRow.val ≤ sizes 1) → (columnBound : column.val < sizes 2) →
      (rowsFit : sizes 1 < 2 ^ sizes 0) → (columnsFit : sizes 2 < 2 ^ sizes 0) →
      (capacity : sizes 1 * sizes 2 ≤ 2 ^ sizes 0) →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (algorithm enumeration) ticks
          (algorithmEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (algorithmExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.columnStep matrix pivotRow.val ⟨column.val, columnBound⟩).1 ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨(GaussJordan.columnStep matrix pivotRow.val ⟨column.val, columnBound⟩).2,
            Nat.lt_of_le_of_lt (GaussJordan.columnStep_row_bound matrix pivotRow.val
              ⟨column.val, columnBound⟩ pivotBound).2 rowsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨initBound, executeInit⟩ := initialization_runs enumeration
  obtain ⟨searchBound, executeSearch⟩ := search_runs enumeration
  obtain ⟨foundBound, executeFound⟩ := found_runs enumeration
  refine ⟨initBound + searchBound + foundBound + 8, ?_⟩
  intro sizes initial pivotRow column matrix pivotBound columnBound rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  obtain ⟨initTicks, initialized, initCost, initTrace, initialResult, initialNext⟩ :=
    executeInit sizes initial pivotRow matrix pivotEq matrixEq headers regions
  have initializedRegions : ∀ name,
      Region ((domains enumeration name).width sizes) 0 (initialized name) :=
    fun name => initTrace.region name (regions name)
  have initializedPivot : initialized pivotTape = encoded (EncodedDomain.binaryNaturals 0)
      sizes pivotRow := initTrace.readOnly_tape pivotTape rfl |>.trans pivotEq
  have initializedColumn : initialized columnTape = encoded (EncodedDomain.binaryNaturals 0)
      sizes column := (initTrace.readOnly_tape columnTape rfl).trans columnEq
  have initializedMatrix : initialized originalTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    (initTrace.readOnly_tape originalTape rfl).trans matrixEq
  have initializedHeaders : ∀ parameter, initialized (sizeTape parameter) = unary (sizes parameter) :=
    fun parameter => (initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)
  obtain ⟨searchTicks, searched, searchCost, searchTrace,
      searchResult, searchOutside, searchImmutable⟩ :=
    executeSearch sizes initialized pivotRow column matrix pivotBound columnBound
      rowsFit columnsFit capacity initializedPivot initializedColumn initializedMatrix
      initializedHeaders initializedRegions
  obtain ⟨candidate, candidateBounds, candidateEq, foundEquation, foundFlag⟩ := searchResult
  have searchedRegions : ∀ name,
      Region ((domains enumeration name).width sizes) 0 (searched name) :=
    fun name => searchTrace.region name (initializedRegions name)
  have searchedHeaders : ∀ parameter, searched (sizeTape parameter) = unary (sizes parameter) :=
    fun parameter => (searchTrace.readOnly_tape (sizeTape parameter) rfl).trans
      (initializedHeaders parameter)
  have searchedResult : searched resultTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix := by
    change searched (.inl StandardGaussJordanPivot.resultTape) = _
    rw [search_preserves_pivot initialized searched searchOutside searchImmutable]
    · exact initialResult
    · decide
  have searchedNext : searched nextRowTape =
      encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow := by
    have outside : nextRowTape ∉ Set.range searchWiring := by
      rintro ⟨name, equal⟩
      fin_cases name <;> cases equal
    exact (searchOutside nextRowTape outside).trans initialNext
  by_cases candidateActive : candidate.val < sizes 1
  · have candidateValid : candidate.val < sizes 1 := candidateActive
    have pivotValid : pivotRow.val < sizes 1 := by omega
    have foundTraceData := executeFound sizes searched candidate pivotRow column
      candidateValid pivotValid columnBound matrix rowsFit columnsFit capacity candidateEq
      ((searchTrace.readOnly_tape pivotTape rfl).trans initializedPivot)
      ((searchTrace.readOnly_tape columnTape rfl).trans initializedColumn)
      ((searchTrace.readOnly_tape originalTape rfl).trans initializedMatrix)
      searchedHeaders searchedRegions
    obtain ⟨foundTicks, foundFinal, foundCost, foundTrace, resultEq, nextEq⟩ :=
      foundTraceData
    have flagEq : searched (searchWiring StandardPivotSearch.foundTape) =
        encoded EncodedDomain.booleans sizes true := by
      rw [foundFlag]
      simp [candidateActive]
    have selected := select_found enumeration sizes searched foundFinal foundTicks flagEq foundTrace
    have complete := searchTrace.sequence (select enumeration) (selectEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (by intro symbols; rfl) selected
    have whole := initTrace.sequence
      (MultiTape.sequence (search enumeration) (select enumeration)
        (selectEntry
          ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (.inl (StandardPivotSearch.algorithmEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :
        Sum (StandardPivotSearch.AlgorithmState
          ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (SelectState
            ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (by intro symbols; rfl) complete
    have mathEq : (GaussJordan.columnStep matrix pivotRow.val
        ⟨column.val, columnBound⟩).1 =
        MatrixOperations.pivotStep matrix ⟨pivotRow.val, pivotValid⟩
          ⟨candidate.val, candidateValid⟩ ⟨column.val, columnBound⟩ := by
      simp [GaussJordan.columnStep, pivotValid, foundEquation, candidateActive]
    have nextValue : (GaussJordan.columnStep matrix pivotRow.val
        ⟨column.val, columnBound⟩).2 = pivotRow.val + 1 := by
      simp [GaussJordan.columnStep, pivotValid, foundEquation, candidateActive]
    refine ⟨initTicks + searchTicks + foundTicks + 4, foundFinal, ?_, ?_, ?_, ?_⟩
    · simp only [map_add, map_ofNat]
      have foundNonnegative : 0 ≤ MvPolynomial.eval sizes foundBound := Nat.zero_le _
      omega
    · simpa [algorithm, algorithmEntry, algorithmExit, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using whole
    · rw [resultEq, mathEq]
    · rw [nextEq]
      apply congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes)
      apply Fin.ext
      exact nextValue.symm
  · have unchanged : GaussJordan.columnStep matrix pivotRow.val
        ⟨column.val, columnBound⟩ = (matrix, pivotRow.val) := by
      by_cases pivotValid : pivotRow.val < sizes 1
      · simp [GaussJordan.columnStep, pivotValid, foundEquation, candidateActive]
      · simp [GaussJordan.columnStep, pivotValid]
    have flagEq : searched (searchWiring StandardPivotSearch.foundTape) =
        encoded EncodedDomain.booleans sizes false := by
      rw [foundFlag]
      simp [candidateActive]
    have selected := select_missing enumeration sizes searched flagEq
    have complete := searchTrace.sequence (select enumeration) (selectEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (by intro symbols; rfl) selected
    have whole := initTrace.sequence
      (MultiTape.sequence (search enumeration) (select enumeration)
        (selectEntry
          ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (.inl (StandardPivotSearch.algorithmEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :
        Sum (StandardPivotSearch.AlgorithmState
          ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (SelectState
            ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (by intro symbols; rfl) complete
    refine ⟨initTicks + searchTicks + 4, searched, ?_, ?_, ?_, ?_⟩
    · simp only [map_add, map_ofNat]
      have foundNonnegative : 0 ≤ MvPolynomial.eval sizes foundBound := Nat.zero_le _
      omega
    · simpa [algorithm, algorithmEntry, algorithmExit, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using whole
    · rw [searchedResult, unchanged]
    · rw [searchedNext]
      apply congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes)
      apply Fin.ext
      exact (congrArg Prod.snd unchanged).symm

def sizeTapes : Fin 3 ↪ TapeName :=
  StandardGaussJordanPivot.sizeTapes.trans pivotWiring

end Polytime2.StandardGaussJordanColumn
