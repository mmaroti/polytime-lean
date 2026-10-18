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

import Polytime2.StandardGaussJordanColumn

/-! # The successful branch of a standard Gauss–Jordan column -/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- Call the complete pivot routine in the column workspace. Search scratch
and the separate next-row output are outside its tape wiring and stay intact. -/
theorem pivot_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate pivotRow column : Fin (2 ^ sizes 0))
      (candidateValid : candidate.val < sizes 1) (pivotValid : pivotRow.val < sizes 1)
      (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (pivot enumeration) ticks
          (StandardGaussJordanPivot.entry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (StandardGaussJordanPivot.exit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.pivotStep (Scalar := Scalar) matrix ⟨pivotRow.val, pivotValid⟩
            ⟨candidate.val, candidateValid⟩ ⟨column.val, columnValid⟩) ∧
        (∀ name, name ∉ Set.range pivotWiring → final name = initial name) ∧
        (∀ name, StandardGaussJordanPivot.readOnly name = true →
          final (pivotWiring name) = initial (pivotWiring name)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanPivot.runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix
    rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq⟩ :=
    execute sizes (fun name => initial (.inl name)) candidate pivotRow column candidateValid pivotValid
      columnValid matrix rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers
      (fun name => regions (.inl name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring pivotWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanPivot.candidateTape then false
        else StandardGaussJordanPivot.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace,
    (located _).trans resultEq, ?_, ?_⟩
  · intro name absent
    exact outside name absent
  · intro name fixed
    exact immutable name fixed

/-- On a found candidate, execute the mathematical pivot step and advance the
pivot without overflow. Search scratch has no encoding requirement. -/
theorem found_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate pivotRow column : Fin (2 ^ sizes 0))
      (candidateValid : candidate.val < sizes 1) (pivotValid : pivotRow.val < sizes 1)
      (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (rowsFit : sizes 1 < 2 ^ sizes 0),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (foundMachine enumeration) ticks
          (.inl (StandardGaussJordanPivot.entry
            ((FieldRow.scalarDomain enumeration).width Empty.elim))) (fun _ => 0) initial
          (.inr (.inr ())) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.pivotStep (Scalar := Scalar) matrix ⟨pivotRow.val, pivotValid⟩
            ⟨candidate.val, candidateValid⟩ ⟨column.val, columnValid⟩) ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨pivotRow.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt pivotValid) rowsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨pivotBound, executePivot⟩ := pivot_runs enumeration
  obtain ⟨incrementBound, executeIncrement⟩ := advancePivot_runs enumeration
  refine ⟨pivotBound + incrementBound + 1, ?_⟩
  intro sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix rowsFit
    columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  obtain ⟨pivotTicks, pivoted, pivotCost, pivotTrace, resultEq, outside, immutable⟩ :=
    executePivot sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix
      rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  obtain ⟨incrementTicks, final, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes pivoted pivotRow ((pivotTrace.readOnly_tape pivotTape rfl).trans pivotEq)
      (fun parameter => (pivotTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (by
        have region := pivotTrace.region nextRowTape (regions nextRowTape)
        change Region ((EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes) 0 (pivoted nextRowTape) at region
        simpa only [EncodedDomain.binaryNaturals_width] using region)
  have nextFits : pivotRow.val + 1 < 2 ^ sizes 0 := lt_of_le_of_lt (Nat.succ_le_of_lt pivotValid) rowsFit
  have nextValue : StandardBinaryIncrement.next 0 sizes pivotRow =
      (⟨pivotRow.val + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt nextFits
  rw [nextValue] at nextEq
  have complete := pivotTrace.sequence advancePivot (.inl (.inl true))
    (by intro symbols; simp [pivot, MultiTape.wire, StandardGaussJordanPivot.halt]) incrementTrace
  refine ⟨pivotTicks + incrementTicks + 1, final, ?_, ?_,
    (incrementOutside resultTape (by decide)).trans resultEq, nextEq⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [foundMachine] using complete
@[simp] theorem found_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    foundMachine enumeration (.inr (.inr ())) symbols = none := rfl

/-- A certified true found flag dispatches to the complete successful branch.
Dispatch and the common return add two stationary transitions. -/
theorem select_found (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (initial final : Tapes Alphabet) (ticks : ℕ)
    (flag : initial (searchWiring StandardPivotSearch.foundTape) =
      encoded EncodedDomain.booleans sizes true)
    (trace : Runs (fun name => (domains enumeration name).width sizes) readOnly
      (foundMachine enumeration) ticks
      (.inl (StandardGaussJordanPivot.entry
        ((FieldRow.scalarDomain enumeration).width Empty.elim))) (fun _ => 0) initial
      (.inr (.inr ())) (fun _ => 0) final) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly (select enumeration)
      (ticks + 2) (selectEntry
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
      (selectExit
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final := by
  have selected : found (MultiTape.read initial) = true := by
    unfold found MultiTape.read
    rw [flag, encoded_booleans]
    rfl
  simpa only [select, selectEntry, selectExit] using
    Runs.branch_true found idle () selected trace (found_halt enumeration)

/-- The sentinel branch performs no computation on any tape. Initialized
matrix, next-row output, and scratch are returned unchanged. -/
theorem select_missing (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (initial : Tapes Alphabet)
    (flag : initial (searchWiring StandardPivotSearch.foundTape) =
      encoded EncodedDomain.booleans sizes false) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly (select enumeration)
      2 (selectEntry
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
      (selectExit
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial := by
  have selected : found (MultiTape.read initial) = false := by
    unfold found MultiTape.read
    rw [flag, encoded_booleans]
    rfl
  have trace : Runs (fun name => (domains enumeration name).width sizes) readOnly idle
      0 () (fun _ => 0) initial () (fun _ => 0) initial := Runs.zero _ _ _
  simpa only [select, selectEntry, selectExit, Nat.zero_add] using
    Runs.branch_false found (foundMachine enumeration)
      (.inl (StandardGaussJordanPivot.entry
        ((FieldRow.scalarDomain enumeration).width Empty.elim))) selected trace (by intro symbols; rfl)

end Polytime2.StandardGaussJordanColumn

