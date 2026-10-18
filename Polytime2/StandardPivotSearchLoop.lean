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
import Polytime2.CallingConventionWhile

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
      initial continueTape = encoded EncodedDomain.booleans sizes true →
      ∃ ticks final,
      ticks ≤ MvPolynomial.eval sizes bound ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly loopBody ticks
        loopBodyEntry (fun _ => 0) initial loopBodyExit (fun _ => 0) final ∧
      final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
        ⟨candidate.val + 1, candidateValue⟩ ∧
      final continueTape = encoded EncodedDomain.booleans sizes false ∧
      (∀ name, name ≠ counterTape 1 → name ≠ nextTape →
        name ≠ continueTape → final name = initial name) := by
  obtain ⟨advanceBound, executeAdvance⟩ := advance_runs scalar
  refine ⟨advanceBound + MvPolynomial.C (2 : ℕ), ?_⟩
  intro sizes initial candidate candidateValue candidateEq headers regions continueEq
  obtain ⟨advanceTicks, advanced, advanceCost, advanceTrace, candidateNext,
      advanceOutside⟩ :=
    executeAdvance sizes initial candidate candidateValue candidateEq headers regions
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
  refine ⟨advanceTicks + 2, final, ?_, ?_, ?_, ?_, ?_⟩
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
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
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
        final continueTape = encoded EncodedDomain.booleans sizes false := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs scalar isZero
  obtain ⟨bodyBound, executeBody⟩ := loopBody_runs scalar
  let iterationBound : MvPolynomial (Fin 3) ℕ :=
    guardBound + bodyBound + MvPolynomial.C (2 : ℕ)
  let rowBound : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 1 + MvPolynomial.C (2 : ℕ)
  refine ⟨rowBound * iterationBound + MvPolynomial.C (1 : ℕ), ?_⟩
  intro sizes initial start column array startValid columnValid rowFits columnsFit capacity
    startEq columnEq limitEq matrixEq headers regions
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  let processedPrefix := fun count : ℕ => ∀ row : Fin (sizes 1), start.val ≤ row.val → row.val < count →
    zeroAt scalar isZero sizes array column columnValid row = true
  let Value := {candidate : Fin (2 ^ sizes 0) //
    start.val ≤ candidate.val ∧ candidate.val ≤ sizes 1 ∧ processedPrefix candidate.val}
  let representation (candidate : Value) (tapes : Tapes Alphabet) : Prop :=
    tapes (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate.val ∧
    tapes rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowFits⟩ ∧
    tapes (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column ∧
    tapes matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array ∧
    (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) ∧
    (∀ name, Region (width name) 0 (tapes name))
  let condition (candidate : Value) :=
    continueValue scalar isZero sizes array candidate.val column columnValid
  let guardedRepresentation (candidate : Value) (tapes : Tapes Alphabet) : Prop :=
    representation candidate tapes ∧
    tapes foundTape = encoded EncodedDomain.booleans sizes (decide (candidate.val.val < sizes 1)) ∧
    tapes continueTape = encoded EncodedDomain.booleans sizes (condition candidate)
  have executeGuarded : ∀ candidate tapes, representation candidate tapes →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly (guard scalar isZero) ticks (guardEntry (scalar.width Empty.elim))
          (fun _ => 0) tapes (guardExit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        guardedRepresentation candidate final := by
    intro candidate tapes represented
    obtain ⟨candidateEq, limitEq, columnEq, matrixEq, headers, regions⟩ := represented
    obtain ⟨ticks, final, cost, trace, nextCandidate, nextLimit, foundEq, continueEq⟩ :=
      executeGuard sizes tapes candidate.val column array rowFits columnValid columnsFit capacity
        candidateEq columnEq limitEq matrixEq headers regions
    exact ⟨ticks, final, cost, trace,
      ⟨nextCandidate, nextLimit, (trace.readOnly_tape (counterTape 6) rfl).trans columnEq,
        (trace.readOnly_tape matrixTape rfl).trans matrixEq,
        (fun parameter => (trace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
        (fun name => trace.region name (regions name))⟩, foundEq, continueEq⟩
  have executeAdvanced : ∀ candidate tapes, guardedRepresentation candidate tapes →
      condition candidate = true → ∃ next : Value, ∃ ticks final,
        ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly loopBody ticks loopBodyEntry (fun _ => 0) tapes
          loopBodyExit (fun _ => 0) final ∧ representation next final ∧
        sizes 1 - next.val.val < sizes 1 - candidate.val.val := by
    intro candidate tapes guarded active
    obtain ⟨⟨candidateEq, limitEq, columnEq, matrixEq, headers, regions⟩,
      foundEq, continueEq⟩ := guarded
    have before : candidate.val.val < sizes 1 := by
      by_contra exhausted
      simp [condition, continueValue, exhausted] at active
    have zero : zeroAt scalar isZero sizes array column columnValid ⟨candidate.val.val, before⟩ = true := by
      simpa only [condition, continueValue, dite_eq_left before, zeroAt] using active
    have nextFits : candidate.val.val + 1 < 2 ^ sizes 0 :=
      lt_of_le_of_lt (Nat.succ_le_of_lt before) rowFits
    obtain ⟨ticks, final, cost, trace, nextCandidate, continueFalse, outside⟩ :=
      executeBody sizes tapes candidate.val nextFits candidateEq headers regions
        (continueEq.trans (congrArg (encoded EncodedDomain.booleans sizes) active))
    let next : Fin (2 ^ sizes 0) := ⟨candidate.val.val + 1, nextFits⟩
    have nextPrefix : processedPrefix next.val := by
      intro row lower upper
      by_cases same : row.val = candidate.val.val
      · have rowEq : row = ⟨candidate.val.val, before⟩ := Fin.ext same
        simpa only [rowEq] using zero
      · exact candidate.property.2.2 row lower (by dsimp [next] at upper; omega)
    refine ⟨⟨next, by have lower := candidate.property.1; dsimp [next]; omega,
      by dsimp [next]; omega, nextPrefix⟩, ticks, final, cost, trace, ?_, ?_⟩
    · exact ⟨nextCandidate,
        (outside rowLimitTape (by decide) (by decide) (by decide)).trans limitEq,
        (trace.readOnly_tape (counterTape 6) rfl).trans columnEq,
        (trace.readOnly_tape matrixTape rfl).trans matrixEq,
        (fun parameter => (trace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
        (fun name => trace.region name (regions name))⟩
    · dsimp [next]
      omega
  let initialValue : Value := ⟨start, le_rfl, startValid, by intro row lower upper; omega⟩
  obtain ⟨ticks, final, terminal, cost, trace, represented, stopped⟩ :=
    Runs.whileValues width readOnly (guard scalar isZero) loopBody
      (guardEntry (scalar.width Empty.elim)) (guardExit (scalar.width Empty.elim))
      loopBodyEntry loopBodyExit continues representation guardedRepresentation condition
      (fun candidate => sizes 1 - candidate.val.val)
      (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes bodyBound)
      (guard_halt scalar isZero) loopBody_halt executeGuarded executeAdvanced
      (fun candidate tapes represented => continue_result tapes _ represented.2.2)
      initialValue initial ⟨startEq, limitEq, columnEq, matrixEq, headers, regions⟩
  obtain ⟨⟨resultEq, _, _, _, _, _⟩, finalFound, finalFlag⟩ := represented
  have terminalFlag : final continueTape = encoded EncodedDomain.booleans sizes false := by
    simpa only [stopped] using finalFlag
  have terminalStop : terminal.val.val = sizes 1 ∨
      ∃ row : Fin (sizes 1), row.val = terminal.val.val ∧
        zeroAt scalar isZero sizes array column columnValid row = false := by
    by_cases before : terminal.val.val < sizes 1
    · refine Or.inr ⟨⟨terminal.val.val, before⟩, rfl, ?_⟩
      simpa only [condition, continueValue, dite_eq_left before, zeroAt] using stopped
    · exact Or.inl (by have upper := terminal.property.2.1; omega)
  have finished := trace.withExit_at (by
    simp [MultiTape.whileMachine, guard_halt,
      continue_result final false terminalFlag])
  refine ⟨ticks + 1, final, terminal.val, ?_, finished,
    ⟨terminal.property.1, terminal.property.2.1⟩, resultEq,
    terminal.property.2.2, terminalStop, finalFound, terminalFlag⟩
  have remainingBound : sizes 1 - start.val + 1 ≤ sizes 1 + 2 := by omega
  have boundedCost := cost.trans (Nat.mul_le_mul_right
    (MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2) remainingBound)
  simpa only [iterationBound, rowBound, initialValue, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X] using Nat.add_le_add_right boundedCost 1

end Polytime2.StandardPivotSearch
