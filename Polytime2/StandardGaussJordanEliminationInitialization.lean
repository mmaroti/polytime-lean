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

import Polytime2.StandardGaussJordanEliminationInitCalls

/-! # Complete initialization from arbitrary writable contents -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev InitializationState (initWidth searchWidth : ℕ) :=
  Sum (Pipeline.State SeedStageState)
    (Sum (StandardGaussJordanColumn.WorkspaceState initWidth searchWidth) StandardSizeRead.State)

instance initializationStatesFinite (initWidth searchWidth : ℕ) :
    Fintype (InitializationState initWidth searchWidth) := by
  letI : Fintype (StandardGaussJordanColumn.WorkspaceState initWidth searchWidth) := inferInstance
  dsimp only [InitializationState]
  infer_instance

noncomputable def initialization (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (InitializationState (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) :=
  MultiTape.sequence seed
    (MultiTape.sequence (prepareWorkspace enumeration) readColumns StandardSizeRead.entry)
    (.inl (StandardGaussJordanColumn.workspaceEntry (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length))

def initializationEntry (initWidth searchWidth : ℕ) : InitializationState initWidth searchWidth :=
  .inl (Pipeline.position seedEntry 0)

def initializationExit (initWidth searchWidth : ℕ) : InitializationState initWidth searchWidth :=
  .inr (.inr StandardSizeRead.exit)

@[simp] theorem initialization_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    initialization enumeration (initializationExit (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) symbols = none := rfl

/-- Startup copies the immutable input, prepares every private tape, and reads
the column limit. It works for empty matrices and arbitrary scratch contents. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (columnsFit : sizes 2 < 2 ^ sizes 0),
      initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (initialization enumeration) ticks
          (initializationEntry (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) initial
          (initializationExit (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨seedBound, executeSeed⟩ := seed_runs enumeration
  obtain ⟨workspaceBound, executeWorkspace⟩ := prepareWorkspace_runs enumeration
  obtain ⟨readBound, executeRead⟩ := readColumns_runs enumeration
  refine ⟨seedBound + workspaceBound + readBound + 2, ?_⟩
  intro sizes initial matrix columnsFit matrixEq headers regions
  let zero : Fin (2 ^ sizes 0) := ⟨0, by positivity⟩
  have sizeReadOnly (parameter : Fin 3) : readOnly (sizeTape parameter) = true := by
    fin_cases parameter <;> decide
  obtain ⟨seedTicks, seeded, seedCost, seedTrace, seedOutputs⟩ :=
    executeSeed sizes initial matrix matrixEq (headers 0) regions
  have seedMatrix : seeded workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    seedOutputs 0
  have seedPivot : seeded pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero := seedOutputs 1
  have seedColumn : seeded columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero := seedOutputs 2
  obtain ⟨workspaceTicks, prepared, workspaceCost, workspaceTrace, preparedResult,
      preparedNextRow, workspaceCanonical, workspaceOutside, workspaceImmutable⟩ :=
    executeWorkspace sizes seeded zero matrix seedPivot seedMatrix
      (fun parameter => (seedTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
        (headers parameter))
      (fun name => seedTrace.region name (regions name))
  have preparedMatrix : prepared workingTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    (workspaceImmutable StandardGaussJordanColumn.originalTape rfl).trans seedMatrix
  have preparedPivot : prepared pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero :=
    (workspaceImmutable StandardGaussJordanColumn.pivotTape rfl).trans seedPivot
  have preparedColumn : prepared columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero :=
    (workspaceImmutable StandardGaussJordanColumn.columnTape rfl).trans seedColumn
  have outsideExtra (name : Fin 5) : prepared (.inr name) = seeded (.inr name) :=
    workspaceOutside (.inr name) (by rintro ⟨localName, equal⟩; cases equal)
  have preparedCanonical : ∀ name, readOnly name = false → name ≠ limitTape →
      ∃ value : (domains enumeration name).Carrier sizes,
        prepared name = encoded (domains enumeration name) sizes value := by
    intro name writable notLimit
    cases name with
    | inl name =>
      cases localReadonly : StandardGaussJordanColumn.readOnly name with
      | false => exact workspaceCanonical name localReadonly
      | true =>
        have owned : name = StandardGaussJordanColumn.pivotTape ∨
            name = StandardGaussJordanColumn.columnTape ∨ name = StandardGaussJordanColumn.originalTape := by
          by_contra notOwned
          change (if name = StandardGaussJordanColumn.pivotTape ∨
            name = StandardGaussJordanColumn.columnTape ∨ name = StandardGaussJordanColumn.originalTape then false
            else StandardGaussJordanColumn.readOnly name) = false at writable
          simp only [notOwned, ↓reduceIte, localReadonly] at writable
          cases writable
        rcases owned with isPivot | isColumn | isMatrix
        · subst name
          exact ⟨zero, preparedPivot⟩
        · subst name
          exact ⟨zero, preparedColumn⟩
        · subst name
          exact ⟨matrixEquiv sizes matrix, preparedMatrix⟩
    | inr name =>
      fin_cases name
      · cases writable
      · exact False.elim (notLimit rfl)
      · exact ⟨zero, (outsideExtra 2).trans (seedOutputs 4)⟩
      · exact ⟨false, (outsideExtra 3).trans (seedOutputs 5)⟩
      · exact ⟨zero, (outsideExtra 4).trans (seedOutputs 3)⟩
  have preparedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (prepared name) :=
    fun name => workspaceTrace.region name (seedTrace.region name (regions name))
  obtain ⟨readTicks, final, readCost, readTrace, limitEq, difference, readOutside⟩ :=
    executeRead sizes prepared columnsFit
      (fun parameter => (workspaceTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
        ((seedTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans (headers parameter)))
      (by simpa only [show (domains enumeration limitTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using preparedRegions limitTape) (by simpa only [show (domains enumeration differenceTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using preparedRegions differenceTape)
  have tail := workspaceTrace.sequence readColumns StandardSizeRead.entry
    (by intro symbols; rfl) readTrace
  have complete := seedTrace.sequence
    (MultiTape.sequence (prepareWorkspace enumeration) readColumns StandardSizeRead.entry)
    (.inl (StandardGaussJordanColumn.workspaceEntry (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length))
    (by intro symbols; rfl) tail
  refine ⟨seedTicks + (workspaceTicks + readTicks + 1) + 1, final, ?_, ?_,
    (readOutside workingTape (by decide) (by decide)).trans preparedMatrix,
    (readOutside pivotTape (by decide) (by decide)).trans preparedPivot,
    (readOutside columnTape (by decide) (by decide)).trans preparedColumn, limitEq, ?_⟩
  · simp only [map_add, map_ofNat]
    omega
  · simpa only [initialization, initializationEntry, initializationExit] using complete
  · intro name writable
    by_cases isLimit : name = limitTape
    · subst name
      exact ⟨⟨sizes 2, columnsFit⟩, limitEq⟩
    · by_cases isDifference : name = differenceTape
      · subst name
        exact difference
      · obtain ⟨value, valueEq⟩ := preparedCanonical name writable isLimit
        exact ⟨value, (readOutside name isLimit isDifference).trans valueEq⟩

end Polytime2.StandardGaussJordanElimination
