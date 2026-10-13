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

import Polytime2.StandardGaussJordanClearInterval

/-! # Polynomial execution of a complete row-clear interval -/

namespace Polytime2.StandardGaussJordanClearInterval

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- A mathematical sequence of row updates is realized by the guarded
interval traversal. The limit fits the fixed counter capacity, so the target
advances without wrapping. An empty interval only evaluates the guard. -/
theorem loop_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow column start limit : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (columnValid : column.val < sizes 2)
      (limitWithin : limit.val ≤ sizes 1) (_startWithin : start.val ≤ limit.val)
      (current : ℕ → ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      (∀ count (before : count < limit.val), start.val ≤ count →
        StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
          (StandardGaussJordanClearTarget.additionOperation enumeration)
          sizes sourceRow ⟨count, lt_trans before limit.isLt⟩ sourceValid
          (lt_of_lt_of_le before limitWithin)
          (Neg.neg (α := Scalar) (current count
            ⟨count * sizes 2 + column.val, StandardMatrixEntry.index_lt sizes count
              column.val (lt_of_lt_of_le before limitWithin) columnValid⟩))
          (current count) (sizes 2) = current (count + 1)) →
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (domains enumeration workingTape) sizes (current start.val) →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
        initial name = encoded (domains enumeration name) sizes value) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (machine enumeration) ticks (entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial (exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes (current limit.val) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs enumeration
  obtain ⟨bodyBound, executeBody⟩ := body_runs enumeration
  refine ⟨(MvPolynomial.X 1 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial sourceRow column start limit sourceValid columnValid limitWithin startWithin
    current updateLaw columnsFit capacity sourceEq counterEq columnEq matrixEq limitEq headers regions canonical
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  let controller := MultiTape.whileMachine guard (body enumeration) BinarySubtraction.entry
    (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)) result
  let allowance := MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2
  have traverse : ∀ remaining (count : ℕ), limit.val - count = remaining →
      ∀ (lower : start.val ≤ count) (upper : count ≤ limit.val)
        (counterFits : count < 2 ^ sizes 0) (tapes : Tapes Alphabet),
      tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      tapes (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ →
      tapes columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      tapes workingTape = encoded (domains enumeration workingTape) sizes (current count) →
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region (width name) 0 (tapes name)) →
      (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
        tapes name = encoded (domains enumeration name) sizes value) →
      ∃ ticks final, ticks ≤ (remaining + 1) * allowance ∧
        Runs width readOnly controller ticks (.inl BinarySubtraction.entry) (fun _ => 0) tapes
          (.inl BinarySubtraction.exit) (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes (current limit.val) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) ∧
        result (MultiTape.read final) = false := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining inductionHypothesis =>
      intro count ranking lower upper counterFits tapes sourceEq counterEq columnEq matrixEq
        limitEq headers regions canonical
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
          · obtain ⟨value, encodedValue⟩ := canonical name writable
            exact ⟨value, (guardOutside name isDifference isFlag).trans encodedValue⟩
      have tested : result (MultiTape.read guarded) = decide (count < limit.val) := by
        unfold result MultiTape.read
        rw [flagEq, encoded_booleans]
        cases decide (count < limit.val) <;> rfl
      have liftedGuard := guardTrace.rename Sum.inl (target := controller)
        (by intro state symbols next actions instruction; simp [controller, MultiTape.whileMachine, instruction])
      by_cases before : count < limit.val
      · have targetValid : count < sizes 1 := lt_of_lt_of_le before limitWithin
        obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, ⟨within, nextMatrixEq⟩,
            nextCounterEq, bodyCanonical, bodyOutside⟩ :=
          executeBody sizes guarded sourceRow ⟨count, counterFits⟩ column sourceValid targetValid
            (current count) columnsFit columnValid capacity
            ((guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq)
            ((guardOutside (dataTape 1) (by decide) (by decide)).trans counterEq)
            ((guardTrace.readOnly_tape columnTape rfl).trans columnEq)
            ((guardOutside workingTape (by decide) (by decide)).trans matrixEq)
            (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
            guardedRegions
        have nextFits : count + 1 < 2 ^ sizes 0 := by have fits := limit.isLt; omega
        have nextValue : StandardBinaryIncrement.next 0 sizes ⟨count, counterFits⟩ =
            (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt nextFits
        rw [nextValue] at nextCounterEq
        have nextMatrix : advanced workingTape = encoded (domains enumeration workingTape) sizes
            (current (count + 1)) :=
          nextMatrixEq.trans (congrArg (encoded (domains enumeration workingTape) sizes)
            (updateLaw count before lower))
        have advancedCanonical : ∀ name, readOnly name = false →
            ∃ value : (domains enumeration name).Carrier sizes,
              advanced name = encoded (domains enumeration name) sizes value := by
          intro name writable
          cases name with
          | inl name => exact bodyCanonical name writable
          | inr slot =>
            obtain ⟨value, encodedValue⟩ := guardedCanonical (.inr slot) writable
            exact ⟨value, (bodyOutside slot).trans encodedValue⟩
        obtain ⟨restTicks, final, restCost, restTrace, finalMatrix, finalCounter, finalCanonical, stopped⟩ :=
          inductionHypothesis (limit.val - (count + 1)) (by omega) (count + 1) rfl
            (by omega) (by omega) nextFits advanced
            ((bodyTrace.readOnly_tape (dataTape 0) rfl).trans
              ((guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq))
            nextCounterEq
            ((bodyTrace.readOnly_tape columnTape rfl).trans
              ((guardTrace.readOnly_tape columnTape rfl).trans columnEq)) nextMatrix
            ((bodyOutside 0).trans ((guardOutside limitTape (by decide) (by decide)).trans limitEq))
            (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) rfl).trans
              ((guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
            (fun name => bodyTrace.region name (guardedRegions name)) advancedCanonical
        have liftedBody := bodyTrace.rename Sum.inr (target := controller)
          (by intro state symbols next actions instruction; simp [controller, MultiTape.whileMachine, instruction])
        have toBody : Runs width readOnly controller 1 (.inl BinarySubtraction.exit) (fun _ => 0) guarded
            (.inr (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)))
            (fun _ => 0) guarded := by
          apply Runs.next
            (nextState := Sum.inr (StandardGaussJordanClearStep.entry
              ((FieldRow.scalarDomain enumeration).width Empty.elim)))
            (actions := stationary (MultiTape.read guarded))
            (by simp [controller, MultiTape.whileMachine, guard_halt, tested, before])
            (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := controller)
              (Sum.inr (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)))
              (fun _ => 0) guarded
        have toGuard : Runs width readOnly controller 1
            (.inr (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim)))
            (fun _ => 0) advanced (.inl BinarySubtraction.entry) (fun _ => 0) advanced := by
          apply Runs.next (nextState := Sum.inl BinarySubtraction.entry)
            (actions := stationary (MultiTape.read advanced))
            (by simp [controller, MultiTape.whileMachine, body_halt]) (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := controller) (Sum.inl BinarySubtraction.entry) (fun _ => 0) advanced
        refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, ?_,
          liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace))),
          finalMatrix, finalCounter, finalCanonical, stopped⟩
        have split : remaining + 1 = (limit.val - (count + 1) + 1) + 1 := by omega
        rw [split, Nat.add_mul, one_mul]
        dsimp only [allowance] at restCost ⊢
        omega
      · have finished : count = limit.val := by omega
        have sameCounter : (⟨count, counterFits⟩ : Fin (2 ^ sizes 0)) = limit := Fin.ext finished
        refine ⟨guardTicks, guarded, ?_, liftedGuard, ?_, ?_, guardedCanonical, ?_⟩
        · have dominates := Nat.mul_le_mul_right allowance (show 1 ≤ remaining + 1 by omega)
          simp only [one_mul] at dominates
          dsimp only [allowance] at dominates ⊢
          omega
        · rw [finished] at matrixEq
          exact (guardOutside workingTape (by decide) (by decide)).trans matrixEq
        · exact (guardOutside (dataTape 1) (by decide) (by decide)).trans
            (counterEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameCounter))
        · simpa only [before, decide_false] using tested
  obtain ⟨ticks, final, cost, trace, resultEq, finalCounter, finalCanonical, stopped⟩ :=
    traverse (limit.val - start.val) start.val rfl (le_refl _) startWithin start.isLt initial
      sourceEq counterEq columnEq matrixEq limitEq headers regions canonical
  refine ⟨ticks + 1, final, ?_, ?_, resultEq, finalCounter, finalCanonical⟩
  · have remainingBound : limit.val - start.val + 1 ≤ sizes 1 + 1 := by omega
    have boundedCost := cost.trans (Nat.mul_le_mul_right allowance remainingBound)
    simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using
      Nat.add_le_add_right boundedCost 1
  · exact trace.withExit_at (by simp [controller, MultiTape.whileMachine, guard_halt, stopped])

end Polytime2.StandardGaussJordanClearInterval

