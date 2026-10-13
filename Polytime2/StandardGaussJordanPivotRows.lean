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

import Polytime2.StandardGaussJordanPivot

/-! # Shared pivot-workspace calls for swapping and normalization -/

namespace Polytime2.StandardGaussJordanPivot

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

omit [Field Scalar] in
/-- Both pivot row operations use the same wiring. Their immutable local
arguments include the saved coefficient and private matrix, while every result
and scratch tape may start arbitrary. The result is an ordinary matrix. -/
theorem row_runs (writeSource : Bool) (enumeration : Scalar ≃ Fin cardinality)
    (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate pivot : Fin (2 ^ sizes 0))
      (candidateValid : candidate.val < sizes 1) (pivotValid : pivot.val < sizes 1)
      (coefficient : Scalar) (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim coefficient →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (MultiTape.wire rowWiring (StandardMatrixRows.machine writeSource
            (FieldRow.scalarDomain enumeration) (fun _ => operation))) ticks
          (StandardMatrixRows.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardMatrixRows.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final (dataTape 5) = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixRows.transform writeSource operation coefficient matrix
            ⟨candidate.val, candidateValid⟩ ⟨pivot.val, pivotValid⟩) ∧
        (∀ name, StandardMatrixRows.readOnly name = false →
          ∃ value : (domains enumeration (rowWiring name)).Carrier sizes,
            final (rowWiring name) = encoded (domains enumeration (rowWiring name)) sizes value) ∧
        (∀ name, name ∉ Set.range rowWiring → final name = initial name) ∧
        (∀ name, StandardMatrixRows.readOnly name = true →
          final (rowWiring name) = initial (rowWiring name)) := by
  let scalar := FieldRow.scalarDomain enumeration
  obtain ⟨bound, execute⟩ := StandardMatrixRows.runs writeSource scalar (fun _ => operation)
  refine ⟨bound, ?_⟩
  intro sizes initial candidate pivot candidateValid pivotValid coefficient matrix
    columnsFit capacity candidateEq pivotEq coefficientEq matrixEq headers regions
  have sameDomain : ∀ name, domains enumeration (rowWiring name) =
      StandardMatrixRows.domains scalar name := by
    intro name
    fin_cases name <;> rfl
  change initial workingTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length)
    sizes (matrixEquiv (Carrier := Scalar) sizes matrix) at matrixEq
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, canonical⟩ :=
    execute sizes (fun name => initial (rowWiring name)) candidate pivot candidateValid pivotValid
      coefficient (matrixEquiv sizes matrix) columnsFit capacity candidateEq pivotEq coefficientEq
      matrixEq headers (by
        intro name
        simpa only [← sameDomain name] using regions (rowWiring name))
  have computed := processed_eq_matrix writeSource scalar (fun _ => operation) sizes candidate pivot
    candidateValid pivotValid coefficient matrix (sizes 2) (le_refl _)
  have complete := MatrixRows.processedColumns_complete writeSource operation coefficient matrix
    (⟨candidate.val, candidateValid⟩ : Fin (sizes 1)) (⟨pivot.val, pivotValid⟩ : Fin (sizes 1))
  have localResult : localFinal (StandardMatrixRows.dataTape 5) = encoded (matrixDomain scalar) sizes
      (MatrixRows.transform writeSource operation coefficient matrix
        ⟨candidate.val, candidateValid⟩ ⟨pivot.val, pivotValid⟩) := by
    exact resultEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes)
      (computed.trans (congrArg (matrixEquiv sizes) complete)))
  have trace := localTrace.wire rowWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (by intro name; rw [sameDomain name])
    (by intro name; fin_cases name <;> decide) initial (fun _ => 0)
  have start : install rowWiring (fun name => initial (rowWiring name)) initial = initial :=
    install_self rowWiring initial
  have positions : install rowWiring (fun _ : StandardMatrixRows.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self rowWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install rowWiring localFinal initial, cost, trace,
    (install_at rowWiring localFinal initial (StandardMatrixRows.dataTape 5)).trans localResult,
    ?_, ?_, ?_⟩
  · intro name writable
    obtain ⟨value, encodedValue⟩ := canonical name writable
    rw [sameDomain name]
    exact ⟨value, (install_at rowWiring localFinal initial name).trans encodedValue⟩
  · intro name outside
    exact install_outside rowWiring localFinal initial name outside
  · intro name immutable
    rw [install_at]
    exact localTrace.readOnly_tape name immutable

omit [Field Scalar] in
/-- Commit a separate row-operation result to the caller's private matrix.
The saved coefficient and every other tape are left unchanged. -/
theorem commit_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (initial : Tapes Alphabet)
    (matrixEq : initial (dataTape 5) = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)
    (region : Region ((domains enumeration workingTape).width sizes) 0 (initial workingTape)) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly commit
      (2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2)
      0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial workingTape
        (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)) := by
  exact StandardTapeCommands.copy_encoded_runs (matrixDomain (FieldRow.scalarDomain enumeration))
    sizes matrix (dataTape 5) workingTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl initial matrixEq region

/-- The complete column-clear routine consumes the normalized private matrix
immutably and writes its separate result, canonicalizing the shared scratch. -/
theorem clear_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot column : Fin (2 ^ sizes 0))
      (pivotValid : pivot.val < sizes 1) (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_rowsFit : sizes 1 < 2 ^ sizes 0),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (clearColumn enumeration) ticks
          (StandardGaussJordanClear.algorithmEntry (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardGaussJordanClear.algorithmExit (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.clearColumn (Scalar := Scalar) matrix
            ⟨pivot.val, pivotValid⟩ ⟨column.val, columnValid⟩) ∧
        (∀ name, StandardGaussJordanClear.readOnly name = false →
          ∃ value : (domains enumeration (clearWiring name)).Carrier sizes,
            final (clearWiring name) = encoded (domains enumeration (clearWiring name)) sizes value) ∧
        (∀ name, name ∉ Set.range clearWiring → final name = initial name) ∧
        (∀ name, StandardGaussJordanClear.readOnly name = true →
          final (clearWiring name) = initial (clearWiring name)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanClear.runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial pivot column pivotValid columnValid matrix rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, canonical⟩ :=
    execute sizes (fun name => initial (.inl name)) pivot column pivotValid columnValid matrix
      rowsFit columnsFit capacity pivotEq columnEq matrixEq headers (fun name => regions (.inl name))
  have trace := localTrace.wire clearWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanClear.originalTape then false
        else StandardGaussJordanClear.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => 0)
  have startEq : install clearWiring (fun name => initial (.inl name)) initial = initial :=
    install_self clearWiring initial
  have positions : install clearWiring (fun _ : StandardGaussJordanClear.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self clearWiring _
  rw [startEq, positions] at trace
  refine ⟨ticks, install clearWiring localFinal initial, cost, trace,
    (install_at clearWiring localFinal initial _).trans resultEq, ?_, ?_, ?_⟩
  · intro name writable
    obtain ⟨value, encodedValue⟩ := canonical name writable
    exact ⟨value, (install_at clearWiring localFinal initial name).trans encodedValue⟩
  · intro name outside
    exact install_outside clearWiring localFinal initial name outside
  · intro name immutable
    rw [install_at]
    exact localTrace.readOnly_tape name immutable

end Polytime2.StandardGaussJordanPivot

