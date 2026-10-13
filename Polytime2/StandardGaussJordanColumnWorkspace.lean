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

import Polytime2.StandardGaussJordanColumnAlgorithm

/-! # Preparing column scratch without executing a column

Outer elimination needs valid scratch even when the matrix has no columns.
Preparation uses no matrix lookup and imposes no dimension hypotheses.
-/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev WorkspaceState (initWidth searchWidth : ℕ) :=
  Sum (InitializationState initWidth)
    (Pipeline.State (StandardPivotSearch.InitStageState searchWidth))

instance workspaceStatesFinite (initWidth searchWidth : ℕ) : Fintype (WorkspaceState initWidth searchWidth) := by
  letI : Fintype (InitializationState initWidth) := inferInstance
  dsimp only [WorkspaceState]
  infer_instance

noncomputable def searchInitialization (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (Pipeline.State (StandardPivotSearch.InitStageState
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)) :=
  MultiTape.wire searchWiring (StandardPivotSearch.initialization (FieldRow.scalarDomain enumeration) (0 : Scalar))

noncomputable def workspace (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (WorkspaceState (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) :=
  MultiTape.sequence (initialization enumeration) (searchInitialization enumeration)
    (Pipeline.position (StandardPivotSearch.initEntry
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) 0)

def workspaceEntry (initWidth searchWidth : ℕ) : WorkspaceState initWidth searchWidth :=
  .inl (initializationEntry initWidth)

def workspaceExit (initWidth searchWidth : ℕ) : WorkspaceState initWidth searchWidth := .inr none

@[simp] theorem workspace_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    workspace enumeration (workspaceExit (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) symbols = none := rfl

theorem workspace_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (workspace enumeration) ticks
          (workspaceEntry (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) initial
          (workspaceExit (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨initBound, executeInit⟩ := initialization_runs enumeration
  let scalar := FieldRow.scalarDomain enumeration
  refine ⟨initBound + 15 * (2 * MvPolynomial.C (scalar.width Empty.elim) +
    2 * MvPolynomial.X 0 + 3) + 1, ?_⟩
  intro sizes initial pivotRow matrix pivotEq matrixEq headers regions
  obtain ⟨initTicks, prepared, initCost, initTrace, initialResult, initialNext, initCanonical⟩ :=
    executeInit sizes initial pivotRow matrix pivotEq matrixEq headers regions
  have sameDomain : ∀ name, domains enumeration (searchWiring name) = StandardPivotSearch.domains scalar name := by
    intro name
    fin_cases name <;> rfl
  obtain ⟨searchTicks, localFinal, searchCost, localTrace, candidateEq,
      elementEq, continueEq, searchCanonical⟩ :=
    StandardPivotSearch.initialization_runs scalar sizes (0 : Scalar) pivotRow
      (fun name => prepared (searchWiring name))
      ((initTrace.readOnly_tape pivotTape rfl).trans pivotEq)
      ((initTrace.readOnly_tape (sizeTape 0) rfl).trans (headers 0))
      (by
        intro name
        rw [← sameDomain name]
        exact initTrace.region (searchWiring name) (regions (searchWiring name)))
  have searchTrace := localTrace.wire searchWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (by intro name; rw [sameDomain name])
    (by intro name; fin_cases name <;> decide) prepared (fun _ => 0)
  have start : install searchWiring (fun name => prepared (searchWiring name)) prepared = prepared :=
    install_self searchWiring prepared
  have positions : install searchWiring (fun _ : StandardPivotSearch.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self searchWiring _
  rw [start, positions] at searchTrace
  let final := install searchWiring localFinal prepared
  have outside (name : TapeName) (notMapped : name ∉ Set.range searchWiring) : final name = prepared name :=
    install_outside searchWiring localFinal prepared name notMapped
  have immutable (name : StandardPivotSearch.TapeName) (readonly : StandardPivotSearch.readOnly name = true) :
      final (searchWiring name) = prepared (searchWiring name) :=
    (install_at searchWiring localFinal prepared name).trans (localTrace.readOnly_tape name readonly)
  have complete := initTrace.sequence (searchInitialization enumeration)
    (Pipeline.position (StandardPivotSearch.initEntry (StandardPivotSearch.defaultBits scalar (0 : Scalar)).length) 0)
    (initialization_halt enumeration) searchTrace
  refine ⟨initTicks + searchTicks + 1, final, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_C, MvPolynomial.eval_X]
    omega
  · simpa only [workspace, workspaceEntry, workspaceExit, searchInitialization, scalar, final] using complete
  · exact (search_preserves_pivot prepared final outside immutable StandardGaussJordanPivot.resultTape
      (by decide)).trans initialResult
  · exact (outside nextRowTape (by rintro ⟨name, equal⟩; fin_cases name <;> cases equal)).trans initialNext
  · have canonicalSearch (name : StandardPivotSearch.TapeName) (writable : StandardPivotSearch.readOnly name = false) :
        ∃ value : (domains enumeration (searchWiring name)).Carrier sizes,
          final (searchWiring name) = encoded (domains enumeration (searchWiring name)) sizes value := by
      rw [sameDomain name]
      obtain ⟨value, valueEq⟩ := searchCanonical name writable
      exact ⟨value, (install_at searchWiring localFinal prepared name).trans valueEq⟩
    have transportCanonical : ∀ {first second : TapeName} (equality : first = second)
        (value : (domains enumeration first).Carrier sizes),
        final first = encoded (domains enumeration first) sizes value →
        final second = encoded (domains enumeration second) sizes
          (Eq.mp (congrArg (fun name => (domains enumeration name).Carrier sizes) equality) value) := by
      intro first second equality value canonical
      cases equality
      exact canonical
    intro name writable
    cases name with
    | inl localName =>
      by_cases isCandidate : localName = StandardGaussJordanPivot.candidateTape
      · subst localName
        refine ⟨pivotRow, ?_⟩
        exact (install_at searchWiring localFinal prepared (StandardPivotSearch.counterTape 1)).trans candidateEq
      · have localWritable : StandardGaussJordanPivot.readOnly localName = false := by
          simpa only [readOnly, isCandidate, ↓reduceIte] using writable
        obtain ⟨value, valueEq⟩ := initCanonical localName localWritable
        exact ⟨value, (search_preserves_pivot prepared final outside immutable localName isCandidate).trans valueEq⟩
    | inr extra => cases extra with
      | inl scratch =>
        obtain ⟨value, valueEq⟩ := canonicalSearch scratch.val scratch.property.1
        have locationEq := searchWiring_scratch scratch
        exact ⟨Eq.mp (congrArg (fun tapeName => (domains enumeration tapeName).Carrier sizes) locationEq) value,
          transportCanonical locationEq value valueEq⟩
      | inr extra =>
        refine ⟨pivotRow, ?_⟩
        exact (outside nextRowTape (by rintro ⟨name, equal⟩; fin_cases name <;> cases equal)).trans initialNext

end Polytime2.StandardGaussJordanColumn
