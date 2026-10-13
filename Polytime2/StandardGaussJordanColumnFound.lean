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
          (StandardGaussJordanPivot.entry (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (StandardGaussJordanPivot.exit (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.pivotStep (Scalar := Scalar) matrix ⟨pivotRow.val, pivotValid⟩
            ⟨candidate.val, candidateValid⟩ ⟨column.val, columnValid⟩) ∧
        (∀ name, StandardGaussJordanPivot.readOnly name = false →
          ∃ value : (domains enumeration (.inl name)).Carrier sizes,
            final (.inl name) = encoded (domains enumeration (.inl name)) sizes value) ∧
        (∀ name, name ∉ Set.range pivotWiring → final name = initial name) ∧
        (∀ name, StandardGaussJordanPivot.readOnly name = true →
          final (pivotWiring name) = initial (pivotWiring name)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanPivot.runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix
    rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, canonical⟩ :=
    execute sizes (fun name => initial (.inl name)) candidate pivotRow column candidateValid pivotValid
      columnValid matrix rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers
      (fun name => regions (.inl name))
  have trace := localTrace.wire pivotWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanPivot.candidateTape then false
        else StandardGaussJordanPivot.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => 0)
  have start : install pivotWiring (fun name => initial (.inl name)) initial = initial :=
    install_self pivotWiring initial
  have positions : install pivotWiring (fun _ : StandardGaussJordanPivot.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self pivotWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install pivotWiring localFinal initial, cost, trace,
    (install_at pivotWiring localFinal initial _).trans resultEq, ?_, ?_, ?_⟩
  · intro name writable
    obtain ⟨value, encodedValue⟩ := canonical name writable
    exact ⟨value, (install_at pivotWiring localFinal initial name).trans encodedValue⟩
  · intro name outside
    exact install_outside pivotWiring localFinal initial name outside
  · intro name immutable
    rw [install_at]
    exact localTrace.readOnly_tape name immutable

/-- On a found candidate, execute the mathematical pivot step and advance the
pivot without overflow. The search scratch supplied by the preceding search
stays valid, and every other writable tape is canonicalized by this branch. -/
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
      (∀ name : SearchScratch, ∃ value : (domains enumeration (.inr (.inl name))).Carrier sizes,
        initial (.inr (.inl name)) = encoded (domains enumeration (.inr (.inl name))) sizes value) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (foundMachine enumeration) ticks
          (.inl (StandardGaussJordanPivot.entry (StandardGaussJordanClear.zeroBits enumeration).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim))) (fun _ => 0) initial
          (.inr (.inr ())) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.pivotStep (Scalar := Scalar) matrix ⟨pivotRow.val, pivotValid⟩
            ⟨candidate.val, candidateValid⟩ ⟨column.val, columnValid⟩) ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨pivotRow.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt pivotValid) rowsFit⟩ : Fin (2 ^ sizes 0)) ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨pivotBound, executePivot⟩ := pivot_runs enumeration
  obtain ⟨incrementBound, executeIncrement⟩ := advancePivot_runs enumeration
  refine ⟨pivotBound + incrementBound + 1, ?_⟩
  intro sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix rowsFit
    columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions scratch
  obtain ⟨pivotTicks, pivoted, pivotCost, pivotTrace, resultEq, canonical, outside, immutable⟩ :=
    executePivot sizes initial candidate pivotRow column candidateValid pivotValid columnValid matrix
      rowsFit columnsFit capacity candidateEq pivotEq columnEq matrixEq headers regions
  obtain ⟨incrementTicks, final, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes pivoted pivotRow ((pivotTrace.readOnly_tape pivotTape rfl).trans pivotEq)
      (fun parameter => (pivotTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (pivotTrace.region nextRowTape (regions nextRowTape))
  have nextFits : pivotRow.val + 1 < 2 ^ sizes 0 := lt_of_le_of_lt (Nat.succ_le_of_lt pivotValid) rowsFit
  have nextValue : StandardBinaryIncrement.next 0 sizes pivotRow =
      (⟨pivotRow.val + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt nextFits
  rw [nextValue] at nextEq
  have complete := pivotTrace.sequence advancePivot (.inl (.inl true))
    (by intro symbols; simp [pivot, MultiTape.wire, StandardGaussJordanPivot.halt]) incrementTrace
  refine ⟨pivotTicks + incrementTicks + 1, final, ?_, ?_,
    (incrementOutside resultTape (by decide)).trans resultEq, nextEq, ?_⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [foundMachine] using complete
  · intro name writable
    cases name with
    | inl name =>
      by_cases isCandidate : name = StandardGaussJordanPivot.candidateTape
      · subst name
        exact ⟨candidate, (incrementOutside candidateTape (by decide)).trans
          ((immutable StandardGaussJordanPivot.candidateTape rfl).trans candidateEq)⟩
      · have localWritable : StandardGaussJordanPivot.readOnly name = false := by
          simpa only [readOnly, isCandidate, ↓reduceIte] using writable
        obtain ⟨value, encodedValue⟩ := canonical name localWritable
        exact ⟨value, (incrementOutside (.inl name) (by intro equal; cases equal)).trans encodedValue⟩
    | inr name => cases name with
      | inl name =>
        obtain ⟨value, encodedValue⟩ := scratch name
        exact ⟨value, (incrementOutside (.inr (.inl name)) (by intro equal; cases equal)).trans
          ((outside (.inr (.inl name)) (by rintro ⟨localName, equal⟩; cases equal)).trans encodedValue)⟩
      | inr extra =>
        exact ⟨⟨pivotRow.val + 1, nextFits⟩, nextEq⟩

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
      (.inl (StandardGaussJordanPivot.entry (StandardGaussJordanClear.zeroBits enumeration).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim))) (fun _ => 0) initial
      (.inr (.inr ())) (fun _ => 0) final) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly (select enumeration)
      (ticks + 2) (selectEntry (StandardGaussJordanClear.zeroBits enumeration).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
      (selectExit (StandardGaussJordanClear.zeroBits enumeration).length
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
      2 (selectEntry (StandardGaussJordanClear.zeroBits enumeration).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
      (selectExit (StandardGaussJordanClear.zeroBits enumeration).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial := by
  have selected : found (MultiTape.read initial) = false := by
    unfold found MultiTape.read
    rw [flag, encoded_booleans]
    rfl
  have trace : Runs (fun name => (domains enumeration name).width sizes) readOnly idle
      0 () (fun _ => 0) initial () (fun _ => 0) initial := Runs.zero _ _ _
  simpa only [select, selectEntry, selectExit, Nat.zero_add] using
    Runs.branch_false found (foundMachine enumeration)
      (.inl (StandardGaussJordanPivot.entry (StandardGaussJordanClear.zeroBits enumeration).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim))) selected trace (by intro symbols; rfl)

end Polytime2.StandardGaussJordanColumn

