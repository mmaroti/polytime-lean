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

import Polytime2.StandardPivotSearchAdvance
import Polytime2.StandardPivotSearchGuard

set_option maxHeartbeats 600000

/-! # Bounded first-nonzero-row search -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention
open StandardMatrixEntry (index_lt)
open Binary (word)

private theorem continue_result {sizes : Fin 3 → ℕ} (tapes : Tapes Alphabet) (bit : Bool)
    (encodedFlag : tapes continueTape = encoded EncodedDomain.booleans sizes bit) :
    continues (MultiTape.read tapes) = bit := by
  unfold continues MultiTape.read
  rw [encodedFlag, encoded_booleans]
  cases bit <;> rfl

def zeroAt (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) (sizes : Fin 3 → ℕ)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (column : Fin (2 ^ sizes 0)) (columnValid : column.val < sizes 2)
    (row : Fin (sizes 1)) : Bool :=
  isZero Empty.elim (array ⟨row.val * sizes 2 + column.val,
    index_lt sizes row.val column.val row.isLt columnValid⟩)

private theorem loopBody_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate : Fin (2 ^ sizes 0)) (candidateValue : candidate.val + 1 < 2 ^ sizes 0),
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false →
        ∃ value : (domains scalar name).Carrier sizes,
          initial name = encoded (domains scalar name) sizes value) →
      initial continueTape = encoded EncodedDomain.booleans sizes true →
      ∃ ticks final,
      ticks ≤ MvPolynomial.eval sizes bound ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly loopBody ticks
        loopBodyEntry (fun _ => 0) initial loopBodyExit (fun _ => 0) final ∧
      final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
        ⟨candidate.val + 1, candidateValue⟩ ∧
      final continueTape = encoded EncodedDomain.booleans sizes false ∧
      (∀ name, readOnly name = false →
        ∃ value : (domains scalar name).Carrier sizes,
          final name = encoded (domains scalar name) sizes value) ∧
      (∀ name, name ≠ counterTape 1 → name ≠ nextTape →
        name ≠ continueTape → final name = initial name) := by
  obtain ⟨advanceBound, executeAdvance⟩ := advance_runs scalar
  refine ⟨advanceBound + MvPolynomial.C (2 : ℕ), ?_⟩
  intro sizes initial candidate candidateValue candidateEq headers regions canonical continueEq
  obtain ⟨advanceTicks, advanced, advanceCost, advanceTrace, candidateNext,
      advancedCanonical, advanceOutside⟩ :=
    executeAdvance sizes initial candidate candidateValue candidateEq headers regions canonical
  have advancedContinue : advanced continueTape = initial continueTape :=
    advanceOutside continueTape (by decide) (by decide)
  obtain ⟨old, oldLength, continueRegion⟩ := (advanceTrace.region continueTape (regions continueTape)).exists_buffer
  have continueBuffer : initial continueTape = buffer (word [true]) := by
    rw [continueEq, encoded_booleans]
    rfl
  have advancedBuffer : advanced continueTape = buffer (word [true]) :=
    advancedContinue.trans continueBuffer
  have clearTrace := StandardTapeCommands.setBoolean_runs continueTape false
    (fun name => (domains scalar name).width sizes) readOnly (by rfl)
    (by norm_num [domains, continueTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
    advanced (Binary.data true) (by simpa [word, buffer] using advancedBuffer)
  let final := Function.update advanced continueTape (encoded EncodedDomain.booleans sizes false)
  refine ⟨advanceTicks + 2, final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [map_add, map_ofNat]
    omega
  · let joinedMachine := MultiTape.sequence advance stop false
    have first := advanceTrace.rename Sum.inl (target := joinedMachine)
      (by intro state symbols next actions instruction; simp [joinedMachine, MultiTape.sequence, instruction])
    have handover : Runs (fun name => (domains scalar name).width sizes) readOnly joinedMachine 1
        (.inl advanceExit) (fun _ => 0) advanced (.inr false) (fun _ => 0) advanced := by
      apply Runs.next (nextState := Sum.inr false)
        (actions := stationary (MultiTape.read advanced))
        (by simp [joinedMachine, MultiTape.sequence, advance_halt]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := joinedMachine) (.inr false) (fun _ => 0) advanced)
    have second := clearTrace.rename Sum.inr (target := joinedMachine)
      (by intro state symbols next actions instruction; simp [joinedMachine, MultiTape.sequence, stop, instruction])
    have joined := first.trans (handover.trans second)
    have clearResult : buffer (word [false]) =
        encoded EncodedDomain.booleans sizes false := by
      rw [encoded_booleans]
      rfl
    simpa [loopBody, loopBodyEntry, loopBodyExit, final, stop,
      StandardTapeCommands.setBoolean, encoded_booleans] using
        (clearResult ▸ joined)
  · simpa [final, Function.update_of_ne (by decide : counterTape 1 ≠ continueTape)] using candidateNext
  · simp [final, Function.update_self, EncodedDomain.booleans]
  · intro name writable
    by_cases isContinue : name = continueTape
    · subst name
      have flagResult : final continueTape = encoded EncodedDomain.booleans sizes false := by
        simp [final, EncodedDomain.booleans]
      exact ⟨false, by simpa [domains, continueTape] using flagResult⟩
    · obtain ⟨value, valid⟩ := advancedCanonical name writable
      have afterClear : final name = advanced name := by
        simp [final, Function.update_of_ne isContinue]
      exact ⟨value, afterClear.trans valid⟩
  · intro name notCandidate notNext notContinue
    have afterClear : final name = advanced name := by
      simp [final, Function.update_of_ne notContinue]
    exact afterClear.trans (advanceOutside name notCandidate notNext)

/-- Search the rows starting at `start`. The counter stops at the first
nonzero entry, or at the row count when every remaining entry is zero. -/
theorem loop_runs (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (start column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (startValid : start.val ≤ sizes 1) (columnValid : column.val < sizes 2)
      (rowFits : sizes 1 < 2 ^ sizes 0) (columnsFit : sizes 2 < 2 ^ sizes 0),
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowFits⟩ →
      initial matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial continueTape = encoded EncodedDomain.booleans sizes false →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false →
        ∃ value : (domains scalar name).Carrier sizes,
          initial name = encoded (domains scalar name) sizes value) →
      ∃ ticks final, ∃ resultCount : Fin (2 ^ sizes 0),
        ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (loop scalar isZero) ticks
          (loopEntry (scalar.width Empty.elim)) (fun _ => 0) initial
          (loopExit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        (start.val ≤ resultCount.val ∧ resultCount.val ≤ sizes 1) ∧
        final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          resultCount ∧
        (∀ row : Fin (sizes 1), start.val ≤ row.val → row.val < resultCount.val →
          zeroAt scalar isZero sizes array column columnValid row = true) ∧
        (resultCount.val = sizes 1 ∨
          ∃ row : Fin (sizes 1), row.val = resultCount.val ∧
            zeroAt scalar isZero sizes array column columnValid row = false) ∧
        final foundTape = encoded EncodedDomain.booleans sizes (decide (resultCount.val < sizes 1)) ∧
        final continueTape = encoded EncodedDomain.booleans sizes false ∧
        (∀ name, readOnly name = false →
          ∃ value : (domains scalar name).Carrier sizes,
            final name = encoded (domains scalar name) sizes value) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs scalar isZero
  obtain ⟨bodyBound, executeBody⟩ := loopBody_runs scalar
  let iterationBound : MvPolynomial (Fin 3) ℕ :=
    guardBound + bodyBound + MvPolynomial.C (2 : ℕ)
  let rowBound : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 1 + MvPolynomial.C (2 : ℕ)
  refine ⟨rowBound * iterationBound + MvPolynomial.C (1 : ℕ), ?_⟩
  intro sizes initial start column array startValid columnValid rowFits columnsFit capacity
    startEq columnEq limitEq matrixEq continueEq headers regions canonical
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  let whileController := MultiTape.whileMachine (guard scalar isZero) loopBody
    (guardEntry (scalar.width Empty.elim)) loopBodyEntry continues
  let countState := fun (count : ℕ) (fits : count < 2 ^ sizes 0) =>
    (⟨count, fits⟩ : Fin (2 ^ sizes 0))
  let allowance := MvPolynomial.eval sizes guardBound +
    MvPolynomial.eval sizes bodyBound + 2
  let processedPrefix := fun count : ℕ => ∀ row : Fin (sizes 1), start.val ≤ row.val → row.val < count →
    zeroAt scalar isZero sizes array column columnValid row = true
  have traverse : ∀ remaining count, sizes 1 - count = remaining → count ≤ sizes 1 →
      (counterFits : count < 2 ^ sizes 0) → ∀ tapes : Tapes Alphabet,
      tapes (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes (countState count counterFits) →
      tapes rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowFits⟩ →
      tapes (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      tapes matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) →
      processedPrefix count →
      (∀ name, Region (width name) 0 (tapes name)) →
      (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
        tapes name = encoded (domains scalar name) sizes value) →
      ∃ ticks final, ticks ≤ (remaining + 1) * allowance ∧
        Runs width readOnly whileController ticks (.inl (guardEntry (scalar.width Empty.elim)))
          (fun _ => 0) tapes (.inl (guardExit (scalar.width Empty.elim))) (fun _ => 0) final ∧
        (∃ resultCount : Fin (2 ^ sizes 0), (count ≤ resultCount.val ∧ resultCount.val ≤ sizes 1) ∧
          final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
            resultCount ∧
          processedPrefix resultCount.val ∧
          (resultCount.val = sizes 1 ∨
            ∃ row : Fin (sizes 1), row.val = resultCount.val ∧
              zeroAt scalar isZero sizes array column columnValid row = false) ∧
          final foundTape = encoded EncodedDomain.booleans sizes (decide (resultCount.val < sizes 1))) ∧
        final continueTape = encoded EncodedDomain.booleans sizes false ∧
        (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
          final name = encoded (domains scalar name) sizes value) := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining inductionHypothesis =>
      intro count ranking bounded counterFits tapes candidateEq' limitEq' columnEq' matrixEq'
        headers' skipped tapeRegions tapeCanonical
      obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardCandidate, guardLimit,
        foundEq, continueFlag, guardCanonical⟩ :=
        executeGuard sizes tapes (countState count counterFits) column array rowFits columnValid columnsFit
          capacity candidateEq' columnEq' limitEq' matrixEq' headers' tapeRegions tapeCanonical
      have guardedRegions : ∀ name, Region (width name) 0 (guarded name) :=
        fun name => guardTrace.region name (tapeRegions name)
      have guardedCanonical : ∀ name, readOnly name = false →
          ∃ value : (domains scalar name).Carrier sizes,
            guarded name = encoded (domains scalar name) sizes value := guardCanonical
      have continueValueEq : continueValue scalar isZero sizes array (countState count counterFits) column
          columnValid = if valid : count < sizes 1 then
            zeroAt scalar isZero sizes array column columnValid ⟨count, valid⟩ else false := by
        unfold continueValue zeroAt
        split_ifs <;> rfl
      have tested := continue_result guarded
        (continueValue scalar isZero sizes array (countState count counterFits) column columnValid)
        continueFlag
      rw [continueValueEq] at tested
      have liftedGuard := guardTrace.rename Sum.inl (target := whileController)
        (by intro state symbols next actions instruction; simp [whileController, MultiTape.whileMachine, instruction])
      by_cases active : count < sizes 1
      · by_cases nonzeroSearch : zeroAt scalar isZero sizes array column columnValid
          ⟨count, active⟩ = true
        · have isContinuing : continues (MultiTape.read guarded) = true := by
            simpa [active, nonzeroSearch] using tested
          have nextFits : count + 1 < 2 ^ sizes 0 :=
            Nat.lt_of_le_of_lt (Nat.succ_le_of_lt active) rowFits
          have guardedHeaders : ∀ parameter, guarded (sizeTape parameter) = unary (sizes parameter) :=
            fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers' parameter)
          have guardedContinue : guarded continueTape = encoded EncodedDomain.booleans sizes true := by
            rw [continueFlag, continueValueEq]
            simp [active, nonzeroSearch]
          obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextCandidate,
              continueFalse, advancedCanonical, bodyOutside⟩ :=
            executeBody sizes guarded (countState count counterFits) (by simpa [countState] using nextFits)
              (by simpa [countState] using guardCandidate) guardedHeaders guardedRegions guardedCanonical
              guardedContinue
          have advancedCandidate : advanced (counterTape 1) =
              encoded (EncodedDomain.binaryNaturals 0) sizes (countState (count + 1) nextFits) := by
            simpa [countState] using nextCandidate
          have advancedRegions : ∀ name, Region (width name) 0 (advanced name) :=
            fun name => bodyTrace.region name (guardedRegions name)
          have advancedCanonical' : ∀ name, readOnly name = false →
              ∃ value : (domains scalar name).Carrier sizes,
                advanced name = encoded (domains scalar name) sizes value := advancedCanonical
          have nextSkipped : processedPrefix (count + 1) := by
            intro row lower upper
            by_cases same : row.val = count
            · have rowEq : row = ⟨count, by omega⟩ := Fin.ext same
              rw [rowEq]
              simpa [zeroAt] using nonzeroSearch
            · exact skipped row lower (by omega)
          have toBody : Runs width readOnly whileController 1
              (.inl (guardExit (scalar.width Empty.elim))) (fun _ => 0) guarded
              (.inr loopBodyEntry) (fun _ => 0) guarded := by
            apply Runs.next (nextState := .inr loopBodyEntry)
              (actions := stationary (MultiTape.read guarded))
              (by simp [whileController, MultiTape.whileMachine, guard_halt, isContinuing])
              (by intro name premise; rfl)
            simpa only [stationary, displacement, add_zero, act_stationary] using
              (Runs.zero (machine := whileController) (.inr loopBodyEntry) (fun _ => 0) guarded)
          have liftedBody := bodyTrace.rename Sum.inr (target := whileController)
            (by intro state symbols next actions instruction
                change loopBody state symbols = some (next, actions) at instruction
                change MultiTape.whileMachine (guard scalar isZero) loopBody
                  (guardEntry (scalar.width Empty.elim)) loopBodyEntry continues
                  (.inr state) symbols = some (Sum.inr next, actions)
                simp only [MultiTape.whileMachine]
                rw [instruction])
          have toGuard : Runs width readOnly whileController 1 (.inr loopBodyExit) (fun _ => 0) advanced
              (.inl (guardEntry (scalar.width Empty.elim))) (fun _ => 0) advanced := by
            apply Runs.next (nextState := .inl (guardEntry (scalar.width Empty.elim)))
              (actions := stationary (MultiTape.read advanced))
              (by simp [whileController, MultiTape.whileMachine, loopBody_halt])
              (by intro name premise; rfl)
            simpa only [stationary, displacement, add_zero, act_stationary] using
              (Runs.zero (machine := whileController)
                (.inl (guardEntry (scalar.width Empty.elim))) (fun _ => 0) advanced)
          obtain ⟨restTicks, final, restCost, restTrace, output, stoppedFlag,
            finalCanonical⟩ :=
            inductionHypothesis (remaining - 1) (by omega) (count + 1) (by omega)
              (by omega) nextFits advanced advancedCandidate
              ((bodyOutside rowLimitTape (by decide) (by decide) (by decide)).trans
                guardLimit)
              ((bodyOutside (counterTape 6) (by decide) (by decide) (by decide)).trans
                ((guardTrace.readOnly_tape (counterTape 6) rfl).trans columnEq'))
              ((bodyOutside matrixTape (by decide) (by decide) (by decide)).trans
                ((guardTrace.readOnly_tape matrixTape rfl).trans matrixEq'))
              (fun parameter =>
                (bodyOutside (sizeTape parameter)
                  (by simp [sizeTape, counterTape])
                  (by simp [sizeTape, nextTape])
                  (by simp [sizeTape, continueTape])).trans
                ((guardTrace.readOnly_tape (sizeTape parameter) rfl).trans
                  (headers' parameter)))
              nextSkipped advancedRegions advancedCanonical'
          obtain ⟨finalCount, finalBounds, finalEq, finalPrefix, finalStop, finalFound⟩ := output
          refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, ?_,
            liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace))),
            ⟨finalCount, ⟨le_trans (Nat.le_succ count) finalBounds.1, finalBounds.2⟩,
              finalEq, finalPrefix, finalStop, finalFound⟩, stoppedFlag, finalCanonical⟩
          have split : remaining + 1 = (remaining - 1 + 1) + 1 := by omega
          rw [split, Nat.add_mul]
          dsimp only [allowance] at restCost ⊢
          omega
        · have isStopped : continues (MultiTape.read guarded) = false := by
            have zeroFalse : zeroAt scalar isZero sizes array column columnValid
                ⟨count, active⟩ = false := by
              cases h : zeroAt scalar isZero sizes array column columnValid ⟨count, active⟩ with
              | false => rfl
              | true => exact (nonzeroSearch h).elim
            rw [tested]
            rw [dif_pos active, zeroFalse]
          have stoppedFlag : guarded continueTape = encoded EncodedDomain.booleans sizes false := by
            rw [continueFlag, continueValueEq]
            have zeroFalse : zeroAt scalar isZero sizes array column columnValid
                ⟨count, active⟩ = false := by
              cases h : zeroAt scalar isZero sizes array column columnValid ⟨count, active⟩ with
              | false => rfl
              | true => exact (nonzeroSearch h).elim
            rw [dif_pos active, zeroFalse]
          refine ⟨guardTicks, guarded, ?_, liftedGuard, ⟨countState count counterFits, ⟨le_refl _, bounded⟩,
            by simpa [countState] using guardCandidate, skipped,
            Or.inr ?_, foundEq⟩, stoppedFlag, guardCanonical⟩
          · have positive : 1 ≤ remaining + 1 := by omega
            have dominates := Nat.mul_le_mul_right allowance positive
            simp only [one_mul] at dominates
            dsimp only [allowance] at dominates ⊢
            omega
          · have zeroFalse : zeroAt scalar isZero sizes array column columnValid
                ⟨count, active⟩ = false := by
              cases h : zeroAt scalar isZero sizes array column columnValid ⟨count, active⟩ with
              | false => rfl
              | true => exact (nonzeroSearch h).elim
            exact ⟨⟨count, active⟩, rfl, zeroFalse⟩
      · have isStopped : continues (MultiTape.read guarded) = false := by
          rw [tested]
          rw [dif_neg active]
        have stoppedFlag : guarded continueTape = encoded EncodedDomain.booleans sizes false := by
          rw [continueFlag, continueValueEq]
          simp [active]
        refine ⟨guardTicks, guarded, ?_, liftedGuard, ⟨countState count counterFits, ⟨le_refl _, bounded⟩,
          by simpa [countState] using guardCandidate, skipped,
          Or.inl (Nat.le_antisymm bounded (Nat.le_of_not_gt active)), foundEq⟩,
          stoppedFlag, guardCanonical⟩
        · have positive : 1 ≤ remaining + 1 := by omega
          have dominates := Nat.mul_le_mul_right allowance positive
          simp only [one_mul] at dominates
          dsimp only [allowance] at dominates ⊢
          omega
  obtain ⟨ticks, final, results⟩ :=
    traverse (sizes 1 - start.val) start.val (by omega) (by omega) start.isLt
      initial startEq limitEq columnEq matrixEq headers (by
        intro row lower upper
        omega) regions canonical
  rcases results with ⟨cost, trace, resultData, finalFlag, finalCanonical⟩
  rcases resultData with ⟨finalCount, resultBound, resultEq, resultPrefix, resultStop, finalFound⟩
  have stopped : continues (MultiTape.read final) = false :=
    continue_result final false finalFlag
  have controllerStops : whileController (.inl (guardExit (scalar.width Empty.elim)))
      (MultiTape.read final) = none := by
    change (match guard scalar isZero (guardExit (scalar.width Empty.elim))
        (MultiTape.read final) with
      | some (next, actions) => some (Sum.inl next, actions)
      | none => if continues (MultiTape.read final) then
          some (Sum.inr loopBodyEntry, stationary (MultiTape.read final)) else none) = none
    rw [guard_halt, stopped]
    rfl
  have completed := trace.withExit_at controllerStops
  refine ⟨ticks + 1, final, finalCount, ?_, completed,
    resultBound, resultEq, resultPrefix, resultStop, finalFound, finalFlag, finalCanonical⟩
  · simp only [map_mul, map_add, map_one]
    have rowCount : sizes 1 - start.val + 1 ≤ sizes 1 + 2 := by omega
    have dominates := Nat.mul_le_mul_right allowance rowCount
    have rowEvaluation : MvPolynomial.eval sizes rowBound = sizes 1 + 2 := by
      simp [rowBound, MvPolynomial.eval_X]
    have iterationEvaluation : MvPolynomial.eval sizes iterationBound = allowance := by
      simp [iterationBound, allowance]
    calc
      ticks + 1 ≤ (sizes 1 - start.val + 1) * allowance + 1 :=
        Nat.add_le_add_right cost 1
      _ ≤ (sizes 1 + 2) * allowance + 1 := Nat.add_le_add_right dominates 1
      _ = MvPolynomial.eval sizes rowBound * MvPolynomial.eval sizes iterationBound + 1 := by
        rw [rowEvaluation, iterationEvaluation]

end Polytime2.StandardPivotSearch
