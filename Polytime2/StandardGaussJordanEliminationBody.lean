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

import Polytime2.StandardGaussJordanEliminationCalls

/-! # One complete outer elimination iteration -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- Commit a mathematical column step and advance the column without overflow.
Only the live matrix and counters need mathematical encodings. -/
theorem body_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow columnIndex : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_pivotBound : pivotRow.val ≤ sizes 1) (columnValid : columnIndex.val < sizes 2),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ∃ nextRow nextColumn : Fin (2 ^ sizes 0),
        ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (body enumeration) ticks
          (bodyEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (bodyExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).1 ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes nextRow ∧
        nextRow.val = (GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).2 ∧
        nextRow.val ≤ sizes 1 ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes nextColumn ∧
        nextColumn.val = columnIndex.val + 1 ∧
        (∀ name : Fin 5, name ≠ 4 → final (.inr name) = initial (.inr name)) := by
  obtain ⟨columnBound, executeColumn⟩ := column_runs enumeration
  obtain ⟨incrementBound, executeIncrement⟩ := increment_runs enumeration
  let matrixBound := (matrixDomain (FieldRow.scalarDomain enumeration)).widthPolynomial
  refine ⟨columnBound + incrementBound + 2 * matrixBound + 4 * MvPolynomial.X 0 + 10, ?_⟩
  intro sizes initial pivotRow columnIndex matrix pivotBound columnValid rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  obtain ⟨columnTicks, columnFinal, nextRow, columnCost, columnTrace, resultEq,
      nextRowValue, nextRowBound, rowEq, columnOutside, columnImmutable⟩ :=
    executeColumn sizes initial pivotRow columnIndex matrix pivotBound columnValid rowsFit columnsFit
      capacity pivotEq columnEq matrixEq headers regions
  have columnRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (columnFinal name) :=
    fun name => columnTrace.region name (regions name)
  let nextMatrix := (GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).1
  let matrixCommitted := Function.update columnFinal workingTape
    (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes nextMatrix)
  have matrixTrace := commitMatrix_runs enumeration sizes nextMatrix columnFinal resultEq
    (columnRegions workingTape)
  have matrixRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (matrixCommitted name) :=
    fun name => matrixTrace.region name (columnRegions name)
  have savedRow : matrixCommitted nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes nextRow :=
    (Function.update_of_ne (by decide) _ _).trans rowEq
  let rowCommitted := Function.update matrixCommitted pivotTape
    (encoded (EncodedDomain.binaryNaturals 0) sizes nextRow)
  have rowTrace := commitRow_runs enumeration sizes nextRow matrixCommitted savedRow
    (by simpa only [show (domains enumeration pivotTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using matrixRegions pivotTape)
  have rowRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (rowCommitted name) :=
    fun name => rowTrace.region name (matrixRegions name)
  have savedColumn : rowCommitted columnTape =
      encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex :=
    (Function.update_of_ne (by decide) _ _).trans
      ((Function.update_of_ne (by decide) _ _).trans
        ((columnImmutable StandardGaussJordanColumn.columnTape rfl).trans columnEq))
  have sizeReadOnly (parameter : Fin 3) : readOnly (sizeTape parameter) = true := by
    fin_cases parameter <;> decide
  have rowHeaders : ∀ parameter, rowCommitted (sizeTape parameter) = unary (sizes parameter) :=
    fun parameter => (rowTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
      ((matrixTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
        ((columnTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans (headers parameter)))
  obtain ⟨incrementTicks, incremented, incrementCost, incrementTrace, incrementEq, incrementOutside⟩ :=
    executeIncrement sizes rowCommitted columnIndex savedColumn rowHeaders (by simpa only [show (domains enumeration nextColumnTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using rowRegions nextColumnTape)
  have nextColumnFits : columnIndex.val + 1 < 2 ^ sizes 0 :=
    lt_of_le_of_lt (Nat.succ_le_of_lt columnValid) columnsFit
  let nextColumn : Fin (2 ^ sizes 0) := ⟨columnIndex.val + 1, nextColumnFits⟩
  have nextColumnValue : StandardBinaryIncrement.next 0 sizes columnIndex = nextColumn := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt nextColumnFits
  rw [nextColumnValue] at incrementEq
  have incrementRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (incremented name) :=
    fun name => incrementTrace.region name (rowRegions name)
  let final := Function.update incremented columnTape
    (encoded (EncodedDomain.binaryNaturals 0) sizes nextColumn)
  have advanceTrace := commitColumn_runs enumeration sizes nextColumn incremented incrementEq
    (by simpa only [show (domains enumeration columnTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using incrementRegions columnTape)
  have advanceTail := incrementTrace.sequence commitColumn 0 (by intro symbols; rfl) advanceTrace
  have rowTail := rowTrace.sequence (MultiTape.sequence increment commitColumn 0)
    (.inl (.inl (.inl true))) (by intro symbols; rfl) advanceTail
  have matrixTail := matrixTrace.sequence
    (MultiTape.sequence commitRow (MultiTape.sequence increment commitColumn 0) (.inl (.inl (.inl true))))
    (.inl 0) (by intro symbols; rfl) rowTail
  have whole := columnTrace.sequence
    (MultiTape.sequence commitMatrix
      (MultiTape.sequence commitRow (MultiTape.sequence increment commitColumn 0) (.inl (.inl (.inl true))))
      (.inl 0)) (.inl 0) (column_halt enumeration) matrixTail
  let matrixCost := 2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2
  let counterCost := 2 * sizes 0 + 2
  let total := columnTicks + (matrixCost + (counterCost + (incrementTicks + counterCost + 1) + 1) + 1) + 1
  refine ⟨total, final, nextRow, nextColumn, ?_, ?_, ?_, ?_, nextRowValue, nextRowBound,
    Function.update_self _ _ _, rfl, ?_⟩
  · dsimp only [total, matrixCost, counterCost]
    simp only [matrixBound, EncodedDomain.width, map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · simpa only [body, bodyEntry, bodyExit, total, matrixCost, counterCost, final] using whole
  · exact (Function.update_of_ne (by decide) _ _).trans
      ((incrementOutside workingTape (by decide)).trans
        ((Function.update_of_ne (by decide) _ _).trans (Function.update_self _ _ _)))
  · exact (Function.update_of_ne (by decide) _ _).trans
      ((incrementOutside pivotTape (by decide)).trans (Function.update_self _ _ _))
  · intro name notNext
    have unaffected : (.inr name : TapeName) ≠ nextColumnTape := by
      intro equal
      exact notNext (Sum.inr.inj equal)
    exact (Function.update_of_ne (by intro equal; cases equal) _ _).trans
      ((incrementOutside (.inr name) unaffected).trans
        ((Function.update_of_ne (by intro equal; cases equal) _ _).trans
          ((Function.update_of_ne (by intro equal; cases equal) _ _).trans
            (columnOutside (.inr name) (by rintro ⟨localName, equal⟩; cases equal)))))

end Polytime2.StandardGaussJordanElimination
