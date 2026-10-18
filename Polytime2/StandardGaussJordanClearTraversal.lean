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

import Polytime2.StandardGaussJordanClear

/-! # Two-interval execution of pivot-column clearing -/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- An interval call preserves its private limit even though the enclosing
caller may change that limit between calls. Scratch needs only bounded regions. -/
theorem interval_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow column start limit : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      limit.val ≤ sizes 1 → start.val ≤ limit.val →
      (limit.val ≤ sourceRow.val ∨ sourceRow.val < start.val) →
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (interval enumeration) ticks
          (StandardGaussJordanClearInterval.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardGaussJordanClearInterval.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (StandardGaussJordanClearInterval.clearedInterval (Scalar := Scalar) matrix
            ⟨sourceRow.val, sourceValid⟩ ⟨column.val, columnValid⟩ start.val limit.val) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes limit := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanClearInterval.mathematical_loop_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow column start limit sourceValid columnValid matrix
    limitWithin startWithin separated columnsFit capacity sourceEq counterEq columnEq matrixEq
    limitEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, finalCounter⟩ :=
    execute sizes (fun name => initial (.inl name)) sourceRow column start limit sourceValid
      columnValid matrix limitWithin startWithin separated columnsFit capacity sourceEq counterEq
      columnEq matrixEq limitEq headers (fun name => regions (.inl name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring intervalWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanClearInterval.limitTape then false
        else StandardGaussJordanClearInterval.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace,
    (located _).trans resultEq,
    (located _).trans finalCounter⟩

abbrev TraversalState (width : ℕ) := Sum (StandardGaussJordanClearInterval.State width)
  (Sum HandoverState (StandardGaussJordanClearInterval.State width))

noncomputable instance traversalStateFinite (width : ℕ) : Fintype (TraversalState width) := by
  letI : Fintype (StandardGaussJordanClearInterval.State width) := inferInstance
  dsimp only [TraversalState, HandoverState, SkipState]
  infer_instance

noncomputable def traversal (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (TraversalState ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence (interval enumeration)
    (MultiTape.sequence handover (interval enumeration)
      (StandardGaussJordanClearInterval.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)))
    (.inl handoverEntry)

def traversalEntry (width : ℕ) : TraversalState width :=
  .inl (StandardGaussJordanClearInterval.entry width)

def traversalExit (width : ℕ) : TraversalState width :=
  .inr (.inr (StandardGaussJordanClearInterval.exit width))

@[simp] theorem interval_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    interval enumeration
      (StandardGaussJordanClearInterval.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      symbols = none := by
  simp [interval, MultiTape.wire, StandardGaussJordanClearInterval.halt]

@[simp] theorem traversal_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    traversal enumeration (traversalExit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      symbols = none := by
  simp [traversal, traversalExit, MultiTape.sequence, interval_halt]

/-- The two intervals and their handover compute complete pivot-column
clearing. The caller has initialized only the live working values;
the original matrix tape stays immutable throughout all three stages. -/
theorem traversal_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot column : Fin (2 ^ sizes 0))
      (pivotValid : pivot.val < sizes 1) (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (rowsFit : sizes 1 < 2 ^ sizes 0),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (traversal enumeration) ticks
          (traversalEntry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (traversalExit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.clearColumn (Scalar := Scalar) matrix
            ⟨pivot.val, pivotValid⟩ ⟨column.val, columnValid⟩) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowsFit⟩ := by
  obtain ⟨intervalBound, executeInterval⟩ := interval_runs enumeration
  obtain ⟨handoverBound, executeHandover⟩ := handover_runs enumeration
  refine ⟨2 * intervalBound + handoverBound + 2, ?_⟩
  intro sizes initial pivot column pivotValid columnValid matrix rowsFit columnsFit capacity
    pivotEq targetEq columnEq matrixEq limitEq headers regions
  obtain ⟨firstTicks, below, firstCost, firstTrace, belowMatrix, belowTarget⟩ :=
    executeInterval sizes initial pivot column ⟨0, by positivity⟩ pivot pivotValid columnValid
      matrix pivotValid.le (Nat.zero_le _) (Or.inl (le_refl _)) columnsFit capacity pivotEq
      targetEq columnEq matrixEq limitEq headers regions
  have belowRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (below name) :=
    fun name => firstTrace.region name (regions name)
  obtain ⟨handoverTicks, prepared, handoverCost, handoverTrace, nextTarget, nextValue, rowLimit,
      difference, handoverOutside⟩ := executeHandover sizes below pivot rowsFit belowTarget
        (fun parameter => (firstTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
        belowRegions
  have nextFits : pivot.val + 1 < 2 ^ sizes 0 := by omega
  let nextPivot : Fin (2 ^ sizes 0) := ⟨pivot.val + 1, nextFits⟩
  have nextPivotEq : StandardBinaryIncrement.next 0 sizes pivot = nextPivot := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt nextFits
  rw [nextPivotEq] at nextTarget nextValue
  let belowMatrixValue := StandardGaussJordanClearInterval.clearedInterval (Scalar := Scalar)
    matrix ⟨pivot.val, pivotValid⟩ ⟨column.val, columnValid⟩ 0 pivot.val
  have preparedMatrix : prepared workingTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes belowMatrixValue :=
    (handoverOutside workingTape (by decide) (by decide) (by decide) (by decide)).trans belowMatrix
  obtain ⟨secondTicks, final, secondCost, secondTrace, finalMatrix, finalTarget⟩ :=
    executeInterval sizes prepared pivot column nextPivot ⟨sizes 1, rowsFit⟩ pivotValid columnValid
      belowMatrixValue (le_refl _) (by dsimp [nextPivot]; omega)
      (Or.inr (by dsimp [nextPivot]; omega)) columnsFit capacity
      ((handoverTrace.readOnly_tape (dataTape 0) rfl).trans
        ((firstTrace.readOnly_tape (dataTape 0) rfl).trans pivotEq)) nextTarget
      ((handoverTrace.readOnly_tape columnTape rfl).trans
        ((firstTrace.readOnly_tape columnTape rfl).trans columnEq)) preparedMatrix rowLimit
      (fun parameter => (handoverTrace.readOnly_tape (sizeTape parameter) rfl).trans
        ((firstTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      (fun name => handoverTrace.region name (belowRegions name))
  have joined := StandardGaussJordanClearInterval.clearedInterval_join matrix
    (⟨pivot.val, pivotValid⟩ : Fin (sizes 1)) (⟨column.val, columnValid⟩ : Fin (sizes 2))
  have tail := handoverTrace.sequence (interval enumeration)
    (StandardGaussJordanClearInterval.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
    handover_halt secondTrace
  have complete := firstTrace.sequence _ (Sum.inl handoverEntry) (interval_halt enumeration) tail
  refine ⟨firstTicks + (handoverTicks + secondTicks + 1) + 1, final, ?_, ?_, ?_, finalTarget⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · simpa only [traversal, traversalEntry, traversalExit] using complete
  · exact finalMatrix.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes) joined)

end Polytime2.StandardGaussJordanClear

