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

import Polytime2.StandardMatrixRowsCalls

/-! # Guarded traversal of all columns of two matrix rows -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention
open StandardMatrixEntry (index_lt)

abbrev LoopState (width : ℕ) := Sum
  (Sum (Sum StandardBinaryArithmetic.State Unit) (StandardMatrixRowStep.State width)) Unit

instance loopFinite (width : ℕ) : Fintype (LoopState width) := by
  letI : Fintype (StandardMatrixRowStep.State width) := inferInstance
  dsimp only [LoopState]
  infer_instance

noncomputable def loop (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (LoopState (scalar.width Empty.elim)) :=
  MultiTape.withExit (MultiTape.whileMachine guard (body writeSource scalar operation)
    BinarySubtraction.entry (StandardMatrixRowStep.entry (scalar.width Empty.elim)) result)

def loopEntry (width : ℕ) : LoopState width := .inl (.inl BinarySubtraction.entry)
def loopExit (width : ℕ) : LoopState width := .inr ()

@[simp] theorem loop_halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (symbols : Symbols Alphabet) : loop writeSource scalar operation (loopExit (scalar.width Empty.elim)) symbols = none := rfl

/-- The mathematical array after the first `count` columns. Indices and scalar
operations act on mathematical values; no tape representation occurs here. -/
noncomputable def processed (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (sizes : Fin 3 → ℕ) (sourceRow targetRow : Fin (2 ^ sizes 0))
    (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes) :
    ℕ → (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes
  | 0 => array
  | count + 1 =>
    let current := processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array count
    if valid : count < sizes 2 then
      let sourceIndex := ⟨sourceRow.val * sizes 2 + count, index_lt sizes sourceRow.val count sourceValid valid⟩
      let targetIndex := ⟨targetRow.val * sizes 2 + count, index_lt sizes targetRow.val count targetValid valid⟩
      let values := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
        coefficient (current sourceIndex) (current targetIndex)
      Function.update (Function.update current sourceIndex values.1) targetIndex values.2
    else current

private theorem result_of_encoded (tapes : Tapes Alphabet) (bit : Bool)
    (encodedFlag : tapes guardTape = encoded EncodedDomain.booleans (fun _ : Fin 3 => 0) bit) :
    result (MultiTape.read tapes) = bit := by
  unfold result MultiTape.read
  rw [encodedFlag, encoded_booleans]
  cases bit <;> rfl

private theorem guard_canonical (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (initial final : Tapes Alphabet) (bit : Bool)
    (canonical : ∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
      initial name = encoded (domains scalar name) sizes value)
    (flag : final guardTape = encoded EncodedDomain.booleans sizes bit)
    (difference : ∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value)
    (outside : ∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) :
    ∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
      final name = encoded (domains scalar name) sizes value := by
  intro name writable
  by_cases isFlag : name = guardTape
  · subst name
    exact ⟨bit, flag⟩
  · by_cases isDifference : name = differenceTape
    · subst name
      exact difference
    · obtain ⟨value, valid⟩ := canonical name writable
      exact ⟨value, (outside name isDifference isFlag).trans valid⟩

/-- The bounded binary column counter reaches the declared limit. Both the
working and result matrices contain the same completed row operation, including
for zero columns; all scratch values remain canonical on return. -/
theorem loop_runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (coefficient : scalar.Carrier Empty.elim)
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (fits : sizes 2 < 2 ^ sizes 0), sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) →
      initial (dataTape 3) = encoded scalar Empty.elim coefficient →
      initial (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
        initial name = encoded (domains scalar name) sizes value) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (loop writeSource scalar operation) ticks
          (loopEntry (scalar.width Empty.elim)) (fun _ => 0) initial (loopExit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes
          (processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array (sizes 2)) ∧
        final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
        (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
          final name = encoded (domains scalar name) sizes value) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs scalar
  obtain ⟨bodyBound, executeBody⟩ := body_runs writeSource scalar operation
  refine ⟨(MvPolynomial.X 2 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial sourceRow targetRow sourceValid targetValid coefficient array fits capacity
    sourceEq targetEq columnEq coefficientEq workEq matrixEq limitEq headers regions canonical
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  let current := processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array
  let bodyMachine := body writeSource scalar operation
  let whileController := MultiTape.whileMachine guard bodyMachine BinarySubtraction.entry
    (StandardMatrixRowStep.entry (scalar.width Empty.elim)) result
  let allowance := MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2
  have traverse : ∀ remaining (count : ℕ), sizes 2 - count = remaining →
      ∀ (bounded : count ≤ sizes 2) (counterFits : count < 2 ^ sizes 0) (tapes : Tapes Alphabet),
      tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      tapes (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      tapes (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ →
      tapes (dataTape 3) = encoded scalar Empty.elim coefficient →
      tapes (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count) →
      tapes (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count) →
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ →
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region (width name) 0 (tapes name)) →
      (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
        tapes name = encoded (domains scalar name) sizes value) →
      ∃ ticks final, ticks ≤ (remaining + 1) * allowance ∧
        Runs width readOnly whileController ticks (.inl BinarySubtraction.entry) (fun _ => 0) tapes
          (.inl BinarySubtraction.exit) (fun _ => 0) final ∧
        final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current (sizes 2)) ∧
        final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
        (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
          final name = encoded (domains scalar name) sizes value) ∧ result (MultiTape.read final) = false := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining inductionHypothesis =>
      intro count ranking bounded counterFits tapes sourceEq targetEq columnEq coefficientEq workEq matrixEq limitEq headers regions canonical
      obtain ⟨guardTicks, guarded, guardCost, guardTrace, flagEq, difference, guardOutside⟩ :=
        executeGuard sizes tapes ⟨count, counterFits⟩ ⟨sizes 2, fits⟩ (headers 0) columnEq limitEq
          (regions differenceTape) (regions guardTape)
      have guardedRegions : ∀ name, Region (width name) 0 (guarded name) := fun name => guardTrace.region name (regions name)
      have guardedCanonical := guard_canonical scalar sizes tapes guarded _ canonical flagEq difference guardOutside
      have tested : result (MultiTape.read guarded) = decide (count < sizes 2) := result_of_encoded guarded _ flagEq
      have liftedGuard := guardTrace.rename Sum.inl (target := whileController)
        (by intro state symbols next actions instruction; simp [whileController, MultiTape.whileMachine, instruction])
      by_cases valid : count < sizes 2
      · obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextWorkEq, nextResultEq, nextColumnEq, bodyCanonical, bodyOutside⟩ :=
          executeBody sizes guarded sourceRow targetRow ⟨count, counterFits⟩ (current count) coefficient
            (index_lt sizes sourceRow.val count sourceValid valid) (index_lt sizes targetRow.val count targetValid valid)
            fits sourceValid targetValid valid capacity
            ((guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq)
            ((guardTrace.readOnly_tape (dataTape 1) rfl).trans targetEq)
            ((guardOutside (dataTape 2) (by decide) (by decide)).trans columnEq)
            ((guardTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq)
            ((guardOutside (dataTape 4) (by decide) (by decide)).trans workEq)
            (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)) guardedRegions
        have nextFits : count + 1 < 2 ^ sizes 0 := by omega
        have nextValue : StandardBinaryIncrement.next 0 sizes ⟨count, counterFits⟩ = (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt nextFits
        rw [nextValue] at nextColumnEq
        let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
          ⟨sourceRow.val * sizes 2 + count, index_lt sizes sourceRow.val count sourceValid valid⟩
        let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
          ⟨targetRow.val * sizes 2 + count, index_lt sizes targetRow.val count targetValid valid⟩
        let values := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
          coefficient (current count sourceIndex) (current count targetIndex)
        have nextArray : current (count + 1) =
            Function.update (Function.update (current count) sourceIndex values.1) targetIndex values.2 := by
          dsimp only [current]
          rw [processed]
          exact dite_eq_left valid
        have nextWorkEq' : advanced (dataTape 4) =
            encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current (count + 1)) := by
          exact nextWorkEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm)
        have nextResultEq' : advanced (dataTape 5) =
            encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current (count + 1)) := by
          exact nextResultEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm)
        have advancedCanonical : ∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
            advanced name = encoded (domains scalar name) sizes value := by
          intro name writable
          cases name with
          | inl name => exact bodyCanonical name writable
          | inr name =>
            obtain ⟨value, encodedValue⟩ := guardedCanonical (.inr name) writable
            exact ⟨value, (bodyOutside name).trans encodedValue⟩
        obtain ⟨restTicks, final, restCost, restTrace, finalMatrix, finalColumn, finalCanonical, stopped⟩ :=
          inductionHypothesis (sizes 2 - (count + 1)) (by omega) (count + 1) rfl (by omega) nextFits advanced
            ((bodyTrace.readOnly_tape (dataTape 0) rfl).trans ((guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq))
            ((bodyTrace.readOnly_tape (dataTape 1) rfl).trans ((guardTrace.readOnly_tape (dataTape 1) rfl).trans targetEq))
            nextColumnEq
            ((bodyTrace.readOnly_tape (dataTape 3) rfl).trans ((guardTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq))
            nextWorkEq' nextResultEq' ((bodyOutside 0).trans ((guardOutside limitTape (by decide) (by decide)).trans limitEq))
            (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) rfl).trans
              ((guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
            (fun name => bodyTrace.region name (guardedRegions name)) advancedCanonical
        have liftedBody := bodyTrace.rename Sum.inr (target := whileController)
          (by intro state symbols next actions instruction; simp [whileController, bodyMachine, MultiTape.whileMachine, instruction])
        have toBody : Runs width readOnly whileController 1 (.inl BinarySubtraction.exit) (fun _ => 0) guarded
            (.inr (StandardMatrixRowStep.entry (scalar.width Empty.elim))) (fun _ => 0) guarded := by
          apply Runs.next (nextState := Sum.inr (StandardMatrixRowStep.entry (scalar.width Empty.elim)))
            (actions := stationary (MultiTape.read guarded))
            (by simp [whileController, MultiTape.whileMachine, guard_halt, tested, valid]) (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := whileController) (Sum.inr (StandardMatrixRowStep.entry (scalar.width Empty.elim))) (fun _ => 0) guarded
        have toGuard : Runs width readOnly whileController 1 (.inr (StandardMatrixRowStep.exit (scalar.width Empty.elim))) (fun _ => 0) advanced
            (.inl BinarySubtraction.entry) (fun _ => 0) advanced := by
          apply Runs.next (nextState := Sum.inl BinarySubtraction.entry) (actions := stationary (MultiTape.read advanced))
            (by simp [whileController, MultiTape.whileMachine, bodyMachine, body, MultiTape.wire, StandardMatrixRowStep.halt])
            (by intro name premise; rfl)
          simpa only [stationary, displacement, add_zero, act_stationary] using
            Runs.zero (machine := whileController) (Sum.inl BinarySubtraction.entry) (fun _ => 0) advanced
        refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, ?_,
          liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace))),
          finalMatrix, finalColumn, finalCanonical, stopped⟩
        have split : remaining + 1 = (sizes 2 - (count + 1) + 1) + 1 := by omega
        rw [split, Nat.add_mul, one_mul]
        dsimp only [allowance] at restCost ⊢
        omega
      · have finished : count = sizes 2 := by omega
        subst count
        refine ⟨guardTicks, guarded, ?_, liftedGuard, ?_, ?_, guardedCanonical, ?_⟩
        · have positive := Nat.mul_le_mul_right allowance (show 1 ≤ remaining + 1 by omega)
          simp only [one_mul] at positive
          dsimp only [allowance] at positive ⊢
          omega
        · exact (guardOutside (dataTape 5) (by decide) (by decide)).trans matrixEq
        · exact (guardOutside (dataTape 2) (by decide) (by decide)).trans columnEq
        · simpa only [lt_self_iff_false, decide_false] using tested
  obtain ⟨ticks, final, cost, trace, resultEq, finalColumn, finalCanonical, stopped⟩ :=
    traverse (sizes 2) 0 (by simp) (by omega) (by positivity) initial sourceEq targetEq columnEq coefficientEq
      workEq matrixEq limitEq headers regions canonical
  refine ⟨ticks + 1, final, ?_, ?_, resultEq, finalColumn, finalCanonical⟩
  · simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using Nat.add_le_add_right cost 1
  · exact trace.withExit_at (by simp [whileController, MultiTape.whileMachine, guard_halt, stopped])

end Polytime2.StandardMatrixRows
