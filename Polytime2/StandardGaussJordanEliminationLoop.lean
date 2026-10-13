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

import Polytime2.StandardGaussJordanEliminationBody

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
      (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
        initial name = encoded (domains enumeration name) sizes value) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (loop enumeration) ticks
          (loopEntry (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (loopExit (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (matrices (sizes 2)) ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (sizes 2)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs enumeration
  obtain ⟨bodyBound, executeBody⟩ := body_runs enumeration
  refine ⟨(MvPolynomial.X 2 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial start startWithin rowsFit columnsFit matrices pivots pivotBounds updateLaw
    capacity pivotEq counterEq matrixEq limitEq headers regions canonical
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  let bodyStart := bodyEntry (StandardGaussJordanClear.zeroBits enumeration).length
    (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
    ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let bodyStop := bodyExit (StandardGaussJordanClear.zeroBits enumeration).length
    (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
    ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let controller := MultiTape.whileMachine guard (body enumeration)
    BinarySubtraction.entry bodyStart continues
  let allowance := MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2
  let limit : Fin (2 ^ sizes 0) := ⟨sizes 2, columnsFit⟩
  have sizeReadOnly (parameter : Fin 3) : readOnly (sizeTape parameter) = true := by
    fin_cases parameter <;> decide
  have traverse : ∀ remaining (count : ℕ), sizes 2 - count = remaining →
      ∀ (upper : count ≤ sizes 2) (counterFits : count < 2 ^ sizes 0) (tapes : Tapes Alphabet),
      tapes pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots count) →
      tapes columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ →
      tapes workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices count) →
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region (width name) 0 (tapes name)) →
      (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
        tapes name = encoded (domains enumeration name) sizes value) →
      ∃ ticks final, ticks ≤ (remaining + 1) * allowance ∧
        Runs width readOnly controller ticks (.inl BinarySubtraction.entry) (fun _ => 0) tapes
          (.inl BinarySubtraction.exit) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices (sizes 2)) ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (sizes 2)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) ∧
        continues (MultiTape.read final) = false := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining inductionHypothesis =>
      intro count ranking upper counterFits tapes pivotEq counterEq matrixEq limitEq headers regions canonical
      obtain ⟨guardTicks, guarded, guardCost, guardTrace, flagEq, difference, guardOutside⟩ :=
        executeGuard sizes tapes ⟨count, counterFits⟩ limit (headers 0) counterEq limitEq
          (regions differenceTape) (regions guardTape)
      have guardedRegions : ∀ name, Region (width name) 0 (guarded name) :=
        fun name => guardTrace.region name (regions name)
      have guardedCanonical : ∀ name, readOnly name = false →
          ∃ value : (domains enumeration name).Carrier sizes,
            guarded name = encoded (domains enumeration name) sizes value := by
        intro name writable
        by_cases isFlag : name = guardTape
        · subst name
          exact ⟨decide (count < limit.val), flagEq⟩
        · by_cases isDifference : name = differenceTape
          · subst name
            exact difference
          · obtain ⟨value, valueEq⟩ := canonical name writable
            exact ⟨value, (guardOutside name isDifference isFlag).trans valueEq⟩
      have tested : continues (MultiTape.read guarded) = decide (count < sizes 2) := by
        unfold continues MultiTape.read
        rw [flagEq, encoded_booleans]
        cases decide (count < sizes 2) <;> rfl
      have liftedGuard := guardTrace.rename Sum.inl (target := controller)
        (by intro state symbols next actions instruction; simp [controller, MultiTape.whileMachine, instruction])
      by_cases before : count < sizes 2
      · obtain ⟨bodyTicks, advanced, nextRow, nextColumn, bodyCost, bodyTrace, nextMatrixEq,
            nextRowEq, nextRowValue, nextRowBound, nextCounterEq, nextCounterValue,
            bodyCanonical, bodyOutside⟩ :=
          executeBody sizes guarded (pivots count) ⟨count, counterFits⟩ (matrices count)
            (pivotBounds count) before rowsFit columnsFit capacity
            ((guardOutside pivotTape (by decide) (by decide)).trans pivotEq)
            ((guardOutside columnTape (by decide) (by decide)).trans counterEq)
            ((guardOutside workingTape (by decide) (by decide)).trans matrixEq)
            (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
              (headers parameter)) guardedRegions guardedCanonical
        have nextFits : count + 1 < 2 ^ sizes 0 :=
          lt_of_le_of_lt (Nat.succ_le_of_lt before) columnsFit
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
        have nextCounter : advanced columnTape =
            encoded (EncodedDomain.binaryNaturals 0) sizes (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) :=
          nextCounterEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameCounter)
        obtain ⟨restTicks, final, restCost, restTrace, finalMatrix, finalPivot,
            finalCounter, finalCanonical, stopped⟩ :=
          inductionHypothesis (sizes 2 - (count + 1)) (by omega) (count + 1) rfl
            (by omega) nextFits advanced nextPivot nextCounter nextMatrix
            ((bodyOutside 1 (by decide)).trans ((guardOutside limitTape (by decide) (by decide)).trans limitEq))
            (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
              ((guardTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans (headers parameter)))
            (fun name => bodyTrace.region name (guardedRegions name)) bodyCanonical
        have liftedBody := bodyTrace.rename Sum.inr (target := controller)
          (by intro state symbols next actions instruction; simp [controller, MultiTape.whileMachine, instruction])
        have toBody : Runs width readOnly controller 1 (.inl BinarySubtraction.exit) (fun _ => 0) guarded
            (.inr bodyStart) (fun _ => 0) guarded := by
          apply Runs.next (nextState := Sum.inr bodyStart)
            (actions := stationary (MultiTape.read guarded))
            (by simp [controller, MultiTape.whileMachine, guard_halt, tested, before])
            (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := controller) (Sum.inr bodyStart) (fun _ => 0) guarded
        have toGuard : Runs width readOnly controller 1 (.inr bodyStop) (fun _ => 0) advanced
            (.inl BinarySubtraction.entry) (fun _ => 0) advanced := by
          apply Runs.next (nextState := Sum.inl BinarySubtraction.entry)
            (actions := stationary (MultiTape.read advanced))
            (by simp [controller, MultiTape.whileMachine, bodyStop, body_halt])
            (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := controller) (Sum.inl BinarySubtraction.entry) (fun _ => 0) advanced
        refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, ?_,
          liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace))),
          finalMatrix, finalPivot, finalCounter, finalCanonical, stopped⟩
        have split : remaining + 1 = (sizes 2 - (count + 1) + 1) + 1 := by omega
        rw [split, Nat.add_mul, one_mul]
        dsimp only [allowance] at restCost ⊢
        omega
      · have finished : count = sizes 2 := by omega
        have sameCounter : (⟨count, counterFits⟩ : Fin (2 ^ sizes 0)) = limit := Fin.ext finished
        refine ⟨guardTicks, guarded, ?_, liftedGuard, ?_, ?_, ?_, guardedCanonical, ?_⟩
        · have dominates := Nat.mul_le_mul_right allowance (show 1 ≤ remaining + 1 by omega)
          simp only [one_mul] at dominates
          dsimp only [allowance] at dominates ⊢
          omega
        · rw [finished] at matrixEq
          exact (guardOutside workingTape (by decide) (by decide)).trans matrixEq
        · rw [finished] at pivotEq
          exact (guardOutside pivotTape (by decide) (by decide)).trans pivotEq
        · exact (guardOutside columnTape (by decide) (by decide)).trans
            (counterEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameCounter))
        · simpa only [before, decide_false] using tested
  obtain ⟨ticks, final, cost, trace, finalMatrix, finalPivot, finalCounter, finalCanonical, stopped⟩ :=
    traverse (sizes 2 - start.val) start.val rfl startWithin start.isLt initial
      pivotEq counterEq matrixEq limitEq headers regions canonical
  refine ⟨ticks + 1, final, ?_, ?_, finalMatrix, finalPivot, finalCounter, finalCanonical⟩
  · have remainingBound : sizes 2 - start.val + 1 ≤ sizes 2 + 1 := by omega
    have boundedCost := cost.trans (Nat.mul_le_mul_right allowance remainingBound)
    simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using
      Nat.add_le_add_right boundedCost 1
  · exact trace.withExit_at (by simp [controller, MultiTape.whileMachine, guard_halt, stopped])

end Polytime2.StandardGaussJordanElimination
