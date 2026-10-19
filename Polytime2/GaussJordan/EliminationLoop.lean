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

import Polytime2.GaussJordan.EliminationBody
import Polytime2.Arithmetic.TraversalLoop

/-! # Polynomial execution of the outer elimination loop -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- The outer loop realizes any mathematical sequence of column steps. The
column counter stops at the dimension, including an empty column interval. -/
theorem loop_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (start : Fin (2 ^ sizes 0)) (_startWithin : start.val ≤ sizes 2)
      (_rowsFit : sizes 1 < 2 ^ sizes 0) (columnsFit : sizes 2 < 2 ^ sizes 0)
      (matrices : ℕ → Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (pivots : ℕ → Fin (2 ^ sizes 0)),
      (∀ count, (pivots count).val ≤ sizes 1) →
      (∀ count (before : count < sizes 2),
        GaussJordan.columnStep (matrices count) (pivots count).val ⟨count, before⟩ =
          (matrices (count + 1), (pivots (count + 1)).val)) →
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots start.val) →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
        (matrices start.val) →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (loop enumeration) ticks
          (loopEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (loopExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (matrices (sizes 2)) ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (sizes 2)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs enumeration
  obtain ⟨bodyBound, executeBody⟩ := body_runs enumeration
  refine ⟨(MvPolynomial.X 2 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial start startWithin rowsFit columnsFit matrices pivots pivotBounds updateLaw
    capacity pivotEq counterEq matrixEq limitEq headers regions
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  let limit : Fin (2 ^ sizes 0) := ⟨sizes 2, columnsFit⟩
  let invariant (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    tapes (pivotTape) = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots count) ∧
    tapes (workingTape) = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices count)
  obtain ⟨ticks, final, cost, trace, finalValues, finalCounter⟩ :=
    BinaryTraversal.range_runs 0 sizes width readOnly guardWiring guardBound bodyBound
      (MvPolynomial.X 2) (executeGuard sizes)
      (by change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = sizes 0; simp)
      (by change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = 1
          norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
      sizeTape rfl (by intro parameter; fin_cases parameter <;> decide)
      (body enumeration) (bodyEntry ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (bodyExit ((FieldRow.scalarDomain enumeration).width Empty.elim)) (body_halt enumeration)
      invariant (by
        intro count tapes final preserved represented
        obtain ⟨pivotEq, matrixEq⟩ := represented
        exact ⟨(preserved (pivotTape) (by decide) (by decide)).trans pivotEq,
          (preserved (workingTape) (by decide) (by decide)).trans matrixEq⟩)
      start limit startWithin (by simp [limit])
      (by
        intro count counterFits lower before nextFits nextValue tapes represented counterEq limitEq headers regions
        obtain ⟨pivotEq, matrixEq⟩ := represented
        obtain ⟨bodyTicks, advanced, nextRow, nextColumn, bodyCost, bodyTrace, nextMatrixEq,
            nextRowEq, nextRowValue, nextRowBound, nextCounterEq, nextCounterValue,
            bodyOutside⟩ :=
          executeBody sizes tapes (pivots count) ⟨count, counterFits⟩ (matrices count)
            (pivotBounds count) before rowsFit columnsFit capacity
            pivotEq counterEq matrixEq headers regions
        have sameCounter : nextColumn = (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) :=
          Fin.ext nextCounterValue
        have sameRow : nextRow = pivots (count + 1) :=
          Fin.ext (nextRowValue.trans (congrArg Prod.snd (updateLaw count before)))
        have nextMatrix : advanced workingTape =
            encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices (count + 1)) :=
          nextMatrixEq.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes)
            (congrArg Prod.fst (updateLaw count before)))
        have nextPivot : advanced pivotTape =
            encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (count + 1)) :=
          nextRowEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameRow)
        refine ⟨bodyTicks, advanced, bodyCost, bodyTrace, ?_, ?_, bodyOutside 1 (by decide)⟩
        · exact ⟨nextPivot, nextMatrix⟩
        · exact nextCounterEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameCounter))
      initial ⟨pivotEq, matrixEq⟩ counterEq limitEq headers regions
  exact ⟨ticks, final, cost, trace, finalValues.2, finalValues.1, finalCounter⟩

end Polytime2.StandardGaussJordanElimination
