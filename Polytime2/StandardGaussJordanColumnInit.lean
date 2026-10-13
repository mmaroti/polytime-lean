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

import Polytime2.StandardGaussJordanColumnFound

/-! # Preparing both outcomes of a Gauss–Jordan column

The result initially represents the original matrix, and the separate next-row
output initially represents the unchanged pivot. The shared pivot workspace is
canonical before search, so the no-pivot branch can return without cleanup.
-/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

def workingTape : TapeName := .inl StandardGaussJordanPivot.workingTape

noncomputable def prepareNextRow : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy pivotTape nextRowTape (by decide)

noncomputable def prepareMatrix : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy originalTape workingTape (by decide)

def workspaceWiring : StandardGaussJordanClear.TapeName ↪ TapeName :=
  StandardGaussJordanPivot.clearWiring.trans pivotWiring

@[simp] theorem workspaceWiring_apply (name : StandardGaussJordanClear.TapeName) :
    workspaceWiring name = .inl (.inl name) := rfl

noncomputable def prepareWorkspace (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanClear.InitializationState
      (StandardGaussJordanClear.zeroBits enumeration).length) :=
  MultiTape.wire workspaceWiring (StandardGaussJordanClear.initialization enumeration)

abbrev InitializationState (width : ℕ) :=
  Sum (Fin 3) (Sum (Fin 3) (StandardGaussJordanClear.InitializationState width))

instance initializationStateFinite (width : ℕ) : Fintype (InitializationState width) := by
  letI : Fintype (StandardGaussJordanClear.InitializationState width) := inferInstance
  dsimp only [InitializationState]
  infer_instance

noncomputable def initialization (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (InitializationState (StandardGaussJordanClear.zeroBits enumeration).length) :=
  MultiTape.sequence prepareNextRow
    (MultiTape.sequence prepareMatrix (prepareWorkspace enumeration)
      (StandardGaussJordanClear.initializationEntry (StandardGaussJordanClear.zeroBits enumeration).length))
    (.inl 0)

def initializationEntry (width : ℕ) : InitializationState width := .inl 0
def initializationExit (width : ℕ) : InitializationState width :=
  .inr (.inr (StandardGaussJordanClear.initializationExit width))

@[simp] theorem initialization_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    initialization enumeration (initializationExit (StandardGaussJordanClear.zeroBits enumeration).length)
      symbols = none := by
  simp [initialization, initializationExit, MultiTape.sequence, prepareWorkspace, MultiTape.wire,
    StandardGaussJordanClear.initialization_halt]

/-- Initialize the result, next-row output, and complete pivot scratch from
arbitrary old writable contents. Search will initialize its own private scratch
and the selected-candidate tape afterwards. No shape hypotheses are needed. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (initialization enumeration) ticks
          (initializationEntry (StandardGaussJordanClear.zeroBits enumeration).length) (fun _ => 0) initial
          (initializationExit (StandardGaussJordanClear.zeroBits enumeration).length) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow ∧
        (∀ name, StandardGaussJordanPivot.readOnly name = false →
          ∃ value : (domains enumeration (.inl name)).Carrier sizes,
            final (.inl name) = encoded (domains enumeration (.inl name)) sizes value) := by
  obtain ⟨workspaceBound, executeWorkspace⟩ := StandardGaussJordanClear.initialization_runs enumeration
  obtain ⟨matrixBound, matrixWidthBound⟩ := (matrixDomain (FieldRow.scalarDomain enumeration)).polynomial_width
  refine ⟨workspaceBound + 2 * matrixBound + 2 * MvPolynomial.X 0 + 6, ?_⟩
  intro sizes initial pivotRow matrix pivotEq matrixEq headers regions
  have nextTrace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
    sizes pivotRow pivotTape nextRowTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl
    initial pivotEq (regions nextRowTape)
  let afterNext := Function.update initial nextRowTape (encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow)
  have afterNextRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (afterNext name) :=
    fun name => nextTrace.region name (regions name)
  have originalEq : afterNext originalTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    (Function.update_of_ne (by decide) _ _).trans matrixEq
  have matrixTrace := StandardTapeCommands.copy_encoded_runs (matrixDomain (FieldRow.scalarDomain enumeration))
    sizes matrix originalTape workingTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl
    afterNext originalEq (afterNextRegions workingTape)
  let copied := Function.update afterNext workingTape
    (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)
  have copiedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (copied name) :=
    fun name => matrixTrace.region name (afterNextRegions name)
  obtain ⟨workspaceTicks, localFinal, workspaceCost, localTrace, workspaceMatrix,
      workspaceCounter, workspaceLimit, canonical⟩ :=
    executeWorkspace sizes (fun name => copied (workspaceWiring name)) pivotRow
      (matrixEquiv sizes matrix)
      ((matrixTrace.readOnly_tape pivotTape rfl).trans ((nextTrace.readOnly_tape pivotTape rfl).trans pivotEq))
      (Function.update_self _ _ _)
      (fun parameter => (matrixTrace.readOnly_tape (sizeTape parameter) rfl).trans
        ((nextTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      (fun name => copiedRegions (workspaceWiring name))
  have workspaceTrace := localTrace.wire workspaceWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
    copied (fun _ => 0)
  have start : install workspaceWiring (fun name => copied (workspaceWiring name)) copied = copied :=
    install_self workspaceWiring copied
  have positions : install workspaceWiring (fun _ : StandardGaussJordanClear.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self workspaceWiring _
  rw [start, positions] at workspaceTrace
  let final := install workspaceWiring localFinal copied
  have finalNext : final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow :=
    (install_outside workspaceWiring localFinal copied nextRowTape (by
      rintro ⟨name, equal⟩
      cases equal)).trans ((Function.update_of_ne (by decide) _ _).trans (Function.update_self _ _ _))
  have tail := matrixTrace.sequence (prepareWorkspace enumeration)
    (StandardGaussJordanClear.initializationEntry (StandardGaussJordanClear.zeroBits enumeration).length)
    (by intro symbols; rfl) workspaceTrace
  have complete := nextTrace.sequence _ (Sum.inl 0) (by intro symbols; rfl) tail
  refine ⟨(2 * sizes 0 + 2) +
    ((2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2) + workspaceTicks + 1) + 1,
    final, ?_, ?_, ?_, finalNext, ?_⟩
  · have widthBound := matrixWidthBound sizes
    simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · simpa only [initialization, initializationEntry, initializationExit, prepareNextRow,
      prepareMatrix, final, EncodedDomain.binaryNaturals] using complete
  · exact (install_at workspaceWiring localFinal copied StandardGaussJordanClear.workingTape).trans workspaceMatrix
  · intro name writable
    cases name with
    | inr extra => cases writable
    | inl name =>
      by_cases isWorking : name = StandardGaussJordanClear.originalTape
      · subst name
        refine ⟨matrixEquiv sizes matrix, ?_⟩
        exact (install_at workspaceWiring localFinal copied _).trans
          ((localTrace.readOnly_tape StandardGaussJordanClear.originalTape rfl).trans (Function.update_self _ _ _))
      · have localWritable : StandardGaussJordanClear.readOnly name = false := by
          simpa only [StandardGaussJordanPivot.readOnly, isWorking, ↓reduceIte] using writable
        obtain ⟨value, encodedValue⟩ := canonical name localWritable
        exact ⟨value, (install_at workspaceWiring localFinal copied name).trans encodedValue⟩

abbrev AlgorithmState (initWidth searchWidth scalarWidth : ℕ) :=
  Sum (InitializationState initWidth)
    (Sum (StandardPivotSearch.AlgorithmState searchWidth scalarWidth) (SelectState initWidth scalarWidth))

instance algorithmStateFinite (initWidth searchWidth scalarWidth : ℕ) :
    Fintype (AlgorithmState initWidth searchWidth scalarWidth) := by
  letI : Fintype (InitializationState initWidth) := inferInstance
  letI : Fintype (StandardPivotSearch.AlgorithmState searchWidth scalarWidth) := inferInstance
  letI : Fintype (SelectState initWidth scalarWidth) := inferInstance
  dsimp only [AlgorithmState]
  infer_instance

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    let scalar := FieldRow.scalarDomain enumeration
    Machine Alphabet (AlgorithmState (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits scalar (0 : Scalar)).length (scalar.width Empty.elim)) :=
  let scalar := FieldRow.scalarDomain enumeration
  MultiTape.sequence (initialization enumeration)
    (MultiTape.sequence (search enumeration) (select enumeration)
      (selectEntry (StandardGaussJordanClear.zeroBits enumeration).length (scalar.width Empty.elim)))
    (.inl (StandardPivotSearch.algorithmEntry (StandardPivotSearch.defaultBits scalar (0 : Scalar)).length
      (scalar.width Empty.elim)))

def algorithmEntry (initWidth searchWidth scalarWidth : ℕ) : AlgorithmState initWidth searchWidth scalarWidth :=
  .inl (initializationEntry initWidth)

def algorithmExit (initWidth searchWidth scalarWidth : ℕ) : AlgorithmState initWidth searchWidth scalarWidth :=
  .inr (.inr (selectExit initWidth scalarWidth))

@[simp] theorem algorithm_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    let scalar := FieldRow.scalarDomain enumeration
    algorithm enumeration (algorithmExit (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits scalar (0 : Scalar)).length (scalar.width Empty.elim)) symbols = none := by
  simp [algorithm, algorithmExit, MultiTape.sequence, select_halt]

/-- Each private search tape has exactly one physical place in the column
workspace; proof fields in the subtype do not change that place. -/
theorem searchWiring_scratch (name : SearchScratch) :
    searchWiring name.val = .inr (.inl name) := by
  rcases name with ⟨name, writable, notCandidate⟩
  fin_cases name <;> solve | rfl | cases writable | exact False.elim (notCandidate rfl)

/-- Search only writes its private tapes and the candidate field. Every other
pivot-workspace tape retains its initialized value, including the matrix result. -/
theorem search_preserves_pivot (initial final : Tapes Alphabet)
    (outside : ∀ name, name ∉ Set.range searchWiring → final name = initial name)
    (immutable : ∀ name, StandardPivotSearch.readOnly name = true →
      final (searchWiring name) = initial (searchWiring name))
    (name : StandardGaussJordanPivot.TapeName)
    (notCandidate : name ≠ StandardGaussJordanPivot.candidateTape) :
    final (.inl name) = initial (.inl name) := by
  apply preserved_of_wiring searchWiring StandardPivotSearch.readOnly initial final outside immutable
  intro localName equal
  fin_cases localName <;> solve
    | rfl
    | cases equal
    | exact False.elim (notCandidate (Sum.inl.inj equal).symm)

end Polytime2.StandardGaussJordanColumn

