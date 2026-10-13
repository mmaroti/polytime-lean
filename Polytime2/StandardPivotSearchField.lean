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

import Polytime2.StandardPivotSearchAlgorithm
import Polytime2.StandardMatrixRowsPresentation
import Polytime2.FieldRow
import Polytime2.GaussJordan

/-! # Finite-field pivot search agrees with mathematical first-nonzero search -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- Equality with zero is compiled into the specialization's finite table. -/
noncomputable def fieldIsZero (enumeration : Scalar ≃ Fin cardinality) :
    ∀ assignment, (FieldRow.scalarDomain enumeration).Carrier assignment → Bool := by
  classical
  exact fun _ value => decide ((value : Scalar) = (0 : Scalar))

theorem field_zeroAt_iff (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
    (column : Fin (2 ^ sizes 0)) (columnValid : column.val < sizes 2) (row : Fin (sizes 1)) :
    zeroAt (FieldRow.scalarDomain enumeration) (fieldIsZero enumeration) sizes
      (matrixEquiv sizes matrix) column columnValid row = true ↔
      matrix row ⟨column.val, columnValid⟩ = 0 := by
  classical
  have entryEq : matrixEquiv (Carrier := Scalar) sizes matrix
      ⟨row.val * sizes 2 + column.val,
        StandardMatrixEntry.index_lt sizes row.val column.val row.isLt columnValid⟩ =
      matrix row ⟨column.val, columnValid⟩ := by
    rw [← matrixIndex_eq sizes row (⟨column.val, columnValid⟩ : Fin (sizes 2))]
    exact matrixEquiv_apply sizes matrix row ⟨column.val, columnValid⟩
  have bitEq : zeroAt (FieldRow.scalarDomain enumeration) (fieldIsZero enumeration) sizes
      (matrixEquiv sizes matrix) column columnValid row =
      fieldIsZero enumeration Empty.elim (matrix row ⟨column.val, columnValid⟩) :=
    congrArg (fun value : Scalar => fieldIsZero enumeration Empty.elim value) entryEq
  rw [bitEq]
  change decide (matrix row ⟨column.val, columnValid⟩ = (0 : Scalar)) = true ↔
    matrix row ⟨column.val, columnValid⟩ = (0 : Scalar)
  simp only [decide_eq_true_eq]

/-- The returned bounded counter denotes exactly `findPivot`, including its
row-count sentinel. Inputs stay immutable; all writable tapes return valid. -/
theorem field_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    let scalar := FieldRow.scalarDomain enumeration
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (start column : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_startValid : start.val ≤ sizes 1) (columnValid : column.val < sizes 2),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial startTape = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial matrixTape = encoded (matrixDomain scalar) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly
          (algorithm scalar (fieldIsZero enumeration) (0 : Scalar)) ticks
          (algorithmEntry (defaultBits scalar (0 : Scalar)).length (scalar.width Empty.elim))
          (fun _ => 0) initial
          (algorithmExit (defaultBits scalar (0 : Scalar)).length (scalar.width Empty.elim))
          (fun _ => 0) final ∧
        ∃ candidate : Fin (2 ^ sizes 0),
          (start.val ≤ candidate.val ∧ candidate.val ≤ sizes 1) ∧
          final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate ∧
          GaussJordan.findPivot (Scalar := Scalar) matrix start.val ⟨column.val, columnValid⟩ =
            (if valid : candidate.val < sizes 1 then some ⟨candidate.val, valid⟩ else none) ∧
          final foundTape = encoded EncodedDomain.booleans sizes (decide (candidate.val < sizes 1)) ∧
          (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
            final name = encoded (domains scalar name) sizes value) := by
  classical
  intro scalar
  obtain ⟨bound, execute⟩ := runs scalar (fieldIsZero enumeration) (0 : Scalar)
  refine ⟨bound, ?_⟩
  intro sizes initial start column matrix startValid columnValid rowsFit columnsFit capacity
    startEq columnEq matrixEq headers regions
  change initial matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length)
    sizes (matrixEquiv sizes matrix) at matrixEq
  obtain ⟨ticks, final, cost, trace, candidate, bounds, candidateEq, skipped, stop, foundEq, flagEq, canonical⟩ :=
    execute sizes initial start column (matrixEquiv sizes matrix) startValid columnValid rowsFit
      columnsFit capacity startEq columnEq matrixEq headers regions
  refine ⟨ticks, final, cost, trace, candidate, bounds, candidateEq, ?_, foundEq, canonical⟩
  apply GaussJordan.findPivot_eq_of_minimal matrix start.val candidate.val
    (⟨column.val, columnValid⟩ : Fin (sizes 2)) bounds.1 bounds.2
  · intro row lower upper
    exact (field_zeroAt_iff enumeration sizes matrix column columnValid row).mp (skipped row lower upper)
  · intro valid zero
    rcases stop with sentinel | ⟨row, rowValue, nonzero⟩
    · omega
    · have rowEq : row = ⟨candidate.val, valid⟩ := Fin.ext rowValue
      have zeroAtRow : matrix row ⟨column.val, columnValid⟩ = 0 := by
        simpa only [rowEq] using zero
      have isZero := (field_zeroAt_iff enumeration sizes matrix column columnValid row).mpr zeroAtRow
      rw [isZero] at nonzero
      contradiction

end Polytime2.StandardPivotSearch

