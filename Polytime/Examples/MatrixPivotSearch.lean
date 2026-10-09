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

import Polytime.Examples.MatrixPivotGuard
import Polytime.HeaderIncrementMachine
import Polytime.WhileMachine
import Polytime.GaussJordan

/-! # Pivot search by a guarded runtime row traversal

The loop skips zero entries, stops at the first nonzero entry or the row-count
sentinel, erases the final guard bit, and preserves the matrix and column.
The iteration count appears only in the proof, never as execution fuel.
-/

namespace Polytime.Examples.MatrixPivotSearch

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeSearch

/-- Search a column from a runtime starting row. The returned counter is the
first eligible nonzero row, or the row count if every eligible entry is zero.
The mathematical contract includes minimality and a polynomial tape bound. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (start : ℕ) (_bounded : start ≤ rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          ∃ (candidate : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([start, rows, column.val, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([candidate, rows, column.val, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) ∧
            start ≤ candidate ∧ candidate ≤ rows ∧
            (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
            (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
            GaussJordan.findPivot matrix start column =
              (if valid : candidate < rows then some ⟨candidate, valid⟩ else none) := by
  classical
  obtain ⟨GuardState, finite, inhabited, guardEntry, guardExit, guard, guardBound,
    guardHalt, guardRuns⟩ := MatrixPivotGuard.realizes_with_counters field extraCount extraBound
  let guardControllerFinite : Fintype GuardState := finite
  let guardControllerInhabited : Inhabited GuardState := inhabited
  let incrementer := HeaderIncrementMachine.machine 0
  let incrementEntry : HeaderIncrementMachine.State 0 := .inl (Fin.last 0)
  let body := Tape.sequence HeaderGuardMachine.consume incrementer incrementEntry
  let bodyEntry : Sum (Fin 3) (HeaderIncrementMachine.State 0) := .inl 0
  let bodyExit : Sum (Fin 3) (HeaderIncrementMachine.State 0) := .inr (.inr (0, 2))
  let loop := WhileMachine.machine guard body guardEntry bodyEntry
  let loopBound : SizePolynomial Matrices.context :=
    (SizePolynomial.parameter (ctx := Matrices.context) .K + 1) * (guardBound + SizePolynomial.constant 7)
  refine ⟨Sum (Sum GuardState (Sum (Fin 3) (HeaderIncrementMachine.State 0))) (Fin 3),
    inferInstance, inferInstance, .inl (.inl guardEntry), .inr 2,
    Tape.sequence loop HeaderGuardMachine.consume 0, loopBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderGuardMachine.consume_halt]
  · intro rows columns matrix start bounded column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let Value := ℕ × field.Carrier
    let refreshed (value : Value) :=
      if valid : value.1 < rows then matrix ⟨value.1, valid⟩ column else value.2
    let condition (value : Value) :=
      if valid : value.1 < rows then decide (matrix ⟨value.1, valid⟩ column = 0) else false
    let frame (index : ℕ) (scalar : field.Carrier) :=
      UnaryMachine.fields ([index, rows, column.val, columns] ++ extra) ++
        word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
          (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let entryTape (value : Value) := (Tape.configuration () [] (frame value.1 value.2)).Tape
    let resultTape (value : Value) :=
      (Tape.configuration () [] (data (condition value) :: frame value.1 (refreshed value))).Tape
    let advance (value : Value) : Value := (value.1 + 1, refreshed value)
    let invariant (value : Value) := start ≤ value.1 ∧ value.1 ≤ rows ∧
      ∀ row : Fin rows, start ≤ row.val → row.val < value.1 → matrix row column = 0
    let initial : Value := (start, initialScalar)
    have initialValid : invariant initial := by
      refine ⟨le_rfl, bounded, ?_⟩
      intro row eligible earlier
      change row.val < start at earlier
      omega
    have preserves : ∀ value, invariant value → condition value = true → invariant (advance value) := by
      intro value valid positive
      have active : value.1 < rows := by
        by_contra inactive
        simp [condition, inactive] at positive
      have zero : matrix ⟨value.1, active⟩ column = 0 := by simpa [condition, active] using positive
      refine ⟨by dsimp [advance]; omega, by dsimp [advance]; omega, ?_⟩
      intro row eligible earlier
      by_cases previous : row.val < value.1
      · exact valid.2.2 row eligible previous
      · have equal : row = (⟨value.1, active⟩ : Fin rows) := Fin.ext (by
          change row.val = value.1
          change row.val < value.1 + 1 at earlier
          omega)
        simpa only [equal] using zero
    let terminalPredicate (index : ℕ) := start ≤ index ∧
      (rows ≤ index ∨ ∃ valid : index < rows, matrix ⟨index, valid⟩ column ≠ 0)
    have terminalExists : ∃ index, terminalPredicate index := ⟨rows, bounded, Or.inl le_rfl⟩
    let terminal := Nat.find terminalExists
    have terminalSpec : terminalPredicate terminal := Nat.find_spec terminalExists
    have terminalBound : terminal ≤ rows := Nat.find_min' terminalExists ⟨bounded, Or.inl le_rfl⟩
    have earlierZero : ∀ row : Fin rows, start ≤ row.val → row.val < terminal → matrix row column = 0 := by
      intro row eligible earlier
      by_contra nonzero
      exact Nat.find_min terminalExists earlier ⟨eligible, Or.inr ⟨row.isLt, nonzero⟩⟩
    have index : ∀ count, (advance^[count] initial).1 = start + count := by
      intro count
      induction count with
      | zero => simp [initial]
      | succ count hypothesis =>
        rw [Function.iterate_succ_apply']
        simp [advance, hypothesis, Nat.add_assoc]
    have running : ∀ count < terminal - start, condition (advance^[count] initial) = true := by
      intro count earlier
      have before : start + count < terminal := by have lower := terminalSpec.1; omega
      have active : (advance^[count] initial).1 < rows := by rw [index]; omega
      have zero := earlierZero ⟨(advance^[count] initial).1, active⟩ (by change start ≤ (advance^[count] initial).1; rw [index]; omega)
        (by change (advance^[count] initial).1 < terminal; rw [index]; exact before)
      simp [condition, active, zero]
    have stops : condition (advance^[terminal - start] initial) = false := by
      have finalIndex : (advance^[terminal - start] initial).1 = terminal := by rw [index]; have lower := terminalSpec.1; omega
      by_cases active : terminal < rows
      · have nonzero : matrix ⟨terminal, active⟩ column ≠ 0 := by
          rcases terminalSpec.2 with reached | ⟨valid, nonzero⟩
          · omega
          · exact nonzero
        simp [condition, finalIndex, active, nonzero]
      · simp [condition, finalIndex, active]
    have guards : ∀ value, invariant value → ∃ ticks,
        ticks ≤ guardBound.eval (assignment rows columns) ∧
          Tape.Steps guard ticks ⟨guardEntry, entryTape value⟩ ⟨guardExit, resultTape value⟩ := by
      intro value valid
      obtain ⟨ticks, cost, trace⟩ := guardRuns rows columns matrix value.1 valid.2.1 column extra extraLength extraBounded value.2 right
      refine ⟨ticks, cost, ?_⟩
      simpa only [entryTape, resultTape, frame, refreshed, condition, matrixWidth, payload, Tape.configuration] using trace
    have bodies : ∀ value, invariant value → condition value = true → ∃ ticks,
        ticks ≤ 5 ∧ Tape.Steps body ticks
          ⟨bodyEntry, resultTape value⟩ ⟨bodyExit, entryTape (advance value)⟩ := by
      intro value _ positive
      have consumed := HeaderGuardMachine.consumes true (frame value.1 (refreshed value))
      have incremented := HeaderIncrementMachine.realizes [] value.1
        (UnaryMachine.fields ([rows, column.val, columns] ++ extra) ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode (refreshed value)))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
      have incremented' : Tape.Steps incrementer 2
          (Tape.configuration incrementEntry [] (frame value.1 (refreshed value)))
          (Tape.configuration (.inr (0, 2)) [] (frame (value.1 + 1) (refreshed value))) := by
        simpa [incrementer, incrementEntry, frame, UnaryMachine.fields, List.append_assoc] using incremented
      have computation := Tape.sequence_steps incrementEntry consumed HeaderGuardMachine.consume_halt incremented'
      refine ⟨5, le_rfl, ?_⟩
      simpa [body, bodyEntry, bodyExit, entryTape, resultTape, advance, positive, Tape.configuration] using computation
    have loopResult := WhileMachine.realizes guard body guardEntry guardExit bodyEntry bodyExit
      entryTape resultTape condition advance invariant (guardBound.eval (assignment rows columns)) 5
      guardHalt (by intro symbol; simp [body, bodyExit, incrementer, Tape.sequence, HeaderIncrementMachine.halt])
      (by intro value _; simp [resultTape, Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk])
      preserves guards bodies initial initialValid (terminal - start) running stops
    obtain ⟨loopTicks, loopCost, loopTrace, loopHalt⟩ := loopResult
    let final := advance^[terminal - start] initial
    have finalIndex : final.1 = terminal := by rw [index]; have lower := terminalSpec.1; omega
    have consumed := HeaderGuardMachine.consumes false (frame final.1 (refreshed final))
    have consumed' : Tape.Steps HeaderGuardMachine.consume 2
        ⟨0, resultTape final⟩
        ⟨2, (Tape.configuration () [] (frame final.1 (refreshed final))).Tape⟩ := by
      simpa [resultTape, final, stops, Tape.configuration] using consumed
    have computation := Tape.sequence_steps_of_halt 0 loopTrace loopHalt consumed'
    refine ⟨terminal, refreshed final, loopTicks + (2 + 1), ?_, ?_, terminalSpec.1, terminalBound, earlierZero, ?_, ?_⟩
    · have dominated := Nat.mul_le_mul_right (guardBound.eval (assignment rows columns) + 5 + 2)
        (show terminal - start + 1 ≤ rows + 1 by omega)
      have boundValue : loopBound.eval (assignment rows columns) =
          (rows + 1) * (guardBound.eval (assignment rows columns) + 5 + 2) := by
        simp [loopBound, assignment]
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant, boundValue]
      omega
    · simpa only [loop, initial, finalIndex, entryTape, frame, matrixWidth, payload,
        Tape.configuration] using computation
    · intro active
      rcases terminalSpec.2 with reached | ⟨valid, nonzero⟩
      · omega
      · exact nonzero

    · apply GaussJordan.findPivot_eq_of_minimal matrix start terminal column terminalSpec.1 terminalBound earlierZero
      intro active
      rcases terminalSpec.2 with reached | ⟨valid, nonzero⟩
      · omega
      · exact nonzero

/-- The search routine with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (start : ℕ) (_bounded : start ≤ rows) (column : Fin columns)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          ∃ (candidate : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [start, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [candidate, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) ∧
            start ≤ candidate ∧ candidate ≤ rows ∧
            (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
            (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
            GaussJordan.findPivot matrix start column =
              (if valid : candidate < rows then some ⟨candidate, valid⟩ else none) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix start bounded column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix start bounded column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeSearch

end Polytime.Examples.MatrixPivotSearch
