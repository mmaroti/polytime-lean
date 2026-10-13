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
          (algorithmEntry (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (algorithmExit (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.columnStep matrix pivotRow.val ⟨column.val, columnBound⟩).1 ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨(GaussJordan.columnStep matrix pivotRow.val ⟨column.val, columnBound⟩).2,
            Nat.lt_of_le_of_lt (GaussJordan.columnStep_row_bound matrix pivotRow.val
              ⟨column.val, columnBound⟩ pivotBound).2 rowsFit⟩ : Fin (2 ^ sizes 0)) ∧
        (∀ name, readOnly name = false →
          ∃ value : (domains enumeration name).Carrier sizes,
            final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨initBound, executeInit⟩ := initialization_runs enumeration
  obtain ⟨searchBound, executeSearch⟩ := search_runs enumeration
  obtain ⟨foundBound, executeFound⟩ := found_runs enumeration
  refine ⟨initBound + searchBound + foundBound + 8, ?_⟩
  intro sizes initial pivotRow column matrix pivotBound columnBound rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  obtain ⟨initTicks, initialized, initCost, initTrace, initialResult, initialNext,
      initCanonical⟩ :=
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
      searchResult, searchCanonical, searchOutside, searchImmutable⟩ :=
    executeSearch sizes initialized pivotRow column matrix pivotBound columnBound
      rowsFit columnsFit capacity initializedPivot initializedColumn initializedMatrix
      initializedHeaders initializedRegions
  obtain ⟨candidate, candidateBounds, candidateEq, foundEquation, foundFlag⟩ := searchResult
  have transportCanonical : ∀ {first second : TapeName} (equality : first = second)
      (value : (domains enumeration first).Carrier sizes),
      searched first = encoded (domains enumeration first) sizes value →
      searched second = encoded (domains enumeration second) sizes
        (Eq.mp (congrArg (fun name => (domains enumeration name).Carrier sizes) equality) value) := by
    intro first second equality value canonical
    cases equality
    exact canonical
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
  have searchedCanonical : ∀ name, readOnly name = false →
      ∃ value : (domains enumeration name).Carrier sizes,
        searched name = encoded (domains enumeration name) sizes value := by
    intro name writable
    cases name with
    | inl localName =>
      by_cases candidateName : localName = StandardGaussJordanPivot.candidateTape
      · subst localName
        refine ⟨candidate, ?_⟩
        simpa [domains, candidateTape, StandardGaussJordanPivot.domains,
          StandardGaussJordanPivot.candidateTape] using candidateEq
      · have pivotWritable : StandardGaussJordanPivot.readOnly localName = false := by
          simpa only [readOnly, candidateName, ↓reduceIte] using writable
        obtain ⟨value, valueEq⟩ := initCanonical localName pivotWritable
        have unchanged := search_preserves_pivot initialized searched searchOutside searchImmutable
          localName candidateName
        exact ⟨value, unchanged.trans valueEq⟩
    | inr rest =>
      cases rest with
      | inl scratch =>
        cases scratch with
        | mk localName properties =>
          obtain ⟨value, valueEq⟩ := searchCanonical localName properties.1
          let targetName : TapeName := .inr (.inl ⟨localName, properties⟩)
          have locationEq : searchWiring localName = targetName :=
            searchWiring_scratch (⟨localName, properties⟩ : SearchScratch)
          exact ⟨Eq.mp (congrArg (fun tapeName => (domains enumeration tapeName).Carrier sizes)
              locationEq) value,
            transportCanonical locationEq value valueEq⟩
      | inr extra =>
        refine ⟨pivotRow, ?_⟩
        exact searchedNext
  by_cases candidateActive : candidate.val < sizes 1
  · have candidateValid : candidate.val < sizes 1 := candidateActive
    have pivotValid : pivotRow.val < sizes 1 := by omega
    have foundTraceData := executeFound sizes searched candidate pivotRow column
      candidateValid pivotValid columnBound matrix rowsFit columnsFit capacity candidateEq
      ((searchTrace.readOnly_tape pivotTape rfl).trans initializedPivot)
      ((searchTrace.readOnly_tape columnTape rfl).trans initializedColumn)
      ((searchTrace.readOnly_tape originalTape rfl).trans initializedMatrix)
      searchedHeaders searchedRegions
      (by
        intro name
        obtain ⟨value, valueEq⟩ := searchedCanonical (.inr (.inl name)) rfl
        exact ⟨value, valueEq⟩)
    obtain ⟨foundTicks, foundFinal, foundCost, foundTrace, resultEq, nextEq, foundCanonical⟩ :=
      foundTraceData
    have flagEq : searched (searchWiring StandardPivotSearch.foundTape) =
        encoded EncodedDomain.booleans sizes true := by
      rw [foundFlag]
      simp [candidateActive]
    have selected := select_found enumeration sizes searched foundFinal foundTicks flagEq foundTrace
    have complete := searchTrace.sequence (select enumeration) (selectEntry
      (StandardGaussJordanClear.zeroBits enumeration).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (by intro symbols; rfl) selected
    have whole := initTrace.sequence
      (MultiTape.sequence (search enumeration) (select enumeration)
        (selectEntry (StandardGaussJordanClear.zeroBits enumeration).length
          ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (.inl (StandardPivotSearch.algorithmEntry
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :
        Sum (StandardPivotSearch.AlgorithmState
          (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
          ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (SelectState (StandardGaussJordanClear.zeroBits enumeration).length
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
    refine ⟨initTicks + searchTicks + foundTicks + 4, foundFinal, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro name writable
      exact foundCanonical name writable
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
      (StandardGaussJordanClear.zeroBits enumeration).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (by intro symbols; rfl) selected
    have whole := initTrace.sequence
      (MultiTape.sequence (search enumeration) (select enumeration)
        (selectEntry (StandardGaussJordanClear.zeroBits enumeration).length
          ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (.inl (StandardPivotSearch.algorithmEntry
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :
        Sum (StandardPivotSearch.AlgorithmState
          (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
          ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (SelectState (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)))
      (by intro symbols; rfl) complete
    refine ⟨initTicks + searchTicks + 4, searched, ?_, ?_, ?_, ?_, ?_⟩
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
    · exact searchedCanonical

def sizeTapes : Fin 3 ↪ TapeName :=
  StandardGaussJordanPivot.sizeTapes.trans pivotWiring

/-- The public routine searches a column and returns both the changed matrix
and the next pivot row. -/
theorem contract [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    CallingConvention.Realizes (domains enumeration) readOnly sizeTapes (algorithm enumeration)
      (algorithmEntry (StandardGaussJordanClear.zeroBits enumeration).length
        (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (algorithmExit (StandardGaussJordanClear.zeroBits enumeration).length
        (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun sizes input =>
        (input ⟨pivotTape, rfl⟩ : Fin (2 ^ sizes 0)).val ≤ sizes 1 ∧
        (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 2 ∧
        sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧
        sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output =>
        let matrix := (matrixEquiv (Carrier := Scalar) sizes).symm (input ⟨originalTape, rfl⟩)
        ∃ columnValid : (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 2,
            (matrixEquiv (Carrier := Scalar) sizes).symm (output ⟨resultTape, by decide⟩) =
              (GaussJordan.columnStep matrix (input ⟨pivotTape, rfl⟩).val
                ⟨(input ⟨columnTape, rfl⟩).val, columnValid⟩).1 ∧
            (output ⟨nextRowTape, by decide⟩).val =
              (GaussJordan.columnStep matrix (input ⟨pivotTape, rfl⟩).val
                ⟨(input ⟨columnTape, rfl⟩).val, columnValid⟩).2) := by
  classical
  refine ⟨by intro parameter; rfl, algorithm_halt enumeration, ?_⟩
  obtain ⟨bound, execute⟩ := runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes input initial valid represented headers
  let matrix := (matrixEquiv (Carrier := Scalar) sizes).symm (input ⟨originalTape, rfl⟩)
  let pivot := input ⟨pivotTape, rfl⟩
  let column := input ⟨columnTape, rfl⟩
  have matrixEq : initial originalTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix := by
    change initial originalTape = encoded (domains enumeration originalTape) sizes
      (matrixEquiv sizes matrix)
    exact (represented.1 originalTape rfl).trans
      (congrArg (encoded (domains enumeration originalTape) sizes)
        ((matrixEquiv (Carrier := Scalar) sizes).apply_symm_apply
          (input ⟨originalTape, rfl⟩))).symm
  obtain ⟨ticks, final, cost, trace, resultEq, nextEq, canonical⟩ :=
    execute sizes initial pivot column matrix valid.1 valid.2.1
      valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2
      (represented.1 pivotTape rfl) (represented.1 columnTape rfl) matrixEq headers represented.region
  have columnValid : column.val < sizes 2 := valid.2.1
  let outputMatrix := (GaussJordan.columnStep matrix pivot.val
    ⟨column.val, columnValid⟩).1
  let outputRow := (GaussJordan.columnStep matrix pivot.val
    ⟨column.val, columnValid⟩).2
  have outputRowBound : outputRow < 2 ^ sizes 0 := by
    exact Nat.lt_of_le_of_lt (GaussJordan.columnStep_row_bound matrix pivot.val
      ⟨column.val, columnValid⟩ valid.1).2 valid.2.2.1
  let outputRowFin : Fin (2 ^ sizes 0) := ⟨outputRow, outputRowBound⟩
  have nextWritable : readOnly nextRowTape = false := rfl
  let output : Outputs (domains enumeration) readOnly sizes := fun name => by
    rcases name with ⟨name, writable⟩
    by_cases isResult : name = resultTape
    · subst name
      exact matrixEquiv sizes outputMatrix
    · by_cases isNext : name = nextRowTape
      · subst name
        exact outputRowFin
      · exact Classical.choose (canonical name writable)
  refine ⟨ticks, output, final, cost, trace, ?_, ?_⟩
  · refine ⟨columnValid, ?_, ?_⟩
    · exact Equiv.symm_apply_apply (matrixEquiv sizes) outputMatrix
    · change (output ⟨nextRowTape, nextWritable⟩).val = outputRowFin.val
      simp [output, resultTape, nextRowTape]
  · intro name writable
    by_cases isResult : name = resultTape
    · subst name
      exact resultEq
    · by_cases isNext : name = nextRowTape
      · subst name
        exact nextEq
      · simpa only [output, isResult, isNext, ↓reduceDIte] using
          Classical.choose_spec (canonical name writable)

end Polytime2.StandardGaussJordanColumn
