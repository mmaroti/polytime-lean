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

import Polytime.Examples.MatrixColumnStep
import Polytime.WhileMachine

/-! # Complete elimination in a prepared matrix frame

A restoring guard traverses all columns. Each body performs the certified
column step and increments the runtime column counter. The loop invariant
identifies the remaining mathematical elimination, including empty dimensions.
-/

namespace Polytime.Examples.MatrixEliminate

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section Elimination

/-- One finite controller realizes complete Gauss–Jordan elimination in a
prepared frame, with a polynomial bound in both matrix dimensions. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (GaussJordan.eliminate matrix)).getLsbD index.val)
          ∃ (finalRow : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [0, rows, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [finalRow, rows, columns, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            finalRow ≤ rows ∧ (GaussJordan.eliminate matrix).IsReducedRowEchelon ∧
            ∃ transformation : Matrix.GeneralLinearGroup (Fin rows) field.Carrier,
              (transformation : Matrix (Fin rows) (Fin rows) field.Carrier) * matrix = GaussJordan.eliminate matrix := by
  classical
  obtain ⟨StepState, finite, inhabited, stepEntry, stepExit, stepMachine, stepBound,
    stepHalt, stepRuns⟩ := MatrixColumnStep.realizes field
  let stepControllerFinite : Fintype StepState := finite
  let stepControllerInhabited : Inhabited StepState := inhabited
  let guard := HeaderGuardMachine.machine 2
  let guardEntry : HeaderGuardMachine.State 2 := (Fin.last 2, false, 0)
  let guardExit : HeaderGuardMachine.State 2 := (0, false, 14)
  let incrementer := HeaderIncrementMachine.machine 2
  let incrementEntry : HeaderIncrementMachine.State 2 := .inl (Fin.last 2)
  let firstBody := Tape.sequence HeaderGuardMachine.consume stepMachine stepEntry
  let body := Tape.sequence firstBody incrementer incrementEntry
  let bodyEntry : Sum (Sum (Fin 3) StepState) (HeaderIncrementMachine.State 2) := .inl (.inl 0)
  let bodyExit : Sum (Sum (Fin 3) StepState) (HeaderIncrementMachine.State 2) := .inr (.inr (0, 2))
  let loop := WhileMachine.machine guard body guardEntry bodyEntry
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .L +
      SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 12
  let bodyBound := stepBound + SizePolynomial.constant 6 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 12
  let loopBound : SizePolynomial Matrices.context :=
    (SizePolynomial.parameter (ctx := Matrices.context) .L + 1) * (guardBound + bodyBound + SizePolynomial.constant 2)
  refine ⟨Sum (Sum (HeaderGuardMachine.State 2) (Sum (Sum (Fin 3) StepState) (HeaderIncrementMachine.State 2))) (Fin 3),
    inferInstance, inferInstance, .inl (.inl guardEntry), .inr 2,
    Tape.sequence loop HeaderGuardMachine.consume 0, loopBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderGuardMachine.consume_halt]
  · intro rows columns matrix initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let Value := ℕ × (Matrix (Fin rows) (Fin columns) field.Carrier × ℕ) × field.Carrier
    let suffix (value : Value) := word (List.ofFn (BoolTuple.fromBits (field.codec.encode value.2.2))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 ::
        (word (List.ofFn (fun index : Fin matrixWidth =>
          (encode field rows columns value.2.1.1).getLsbD index.val)) ++ right))
    let frame (value : Value) := UnaryMachine.fields [value.2.1.2, rows, value.1, columns] ++ suffix value
    let execution (value : Value) (active : value.1 < columns) (bounded : value.2.1.2 ≤ rows) :=
      stepRuns rows columns value.2.1.1 value.2.1.2 bounded ⟨value.1, active⟩ value.2.2 right
    let advance (value : Value) : Value := if active : value.1 < columns then
      if bounded : value.2.1.2 ≤ rows then
        (value.1 + 1, GaussJordan.columnStep value.2.1.1 value.2.1.2 ⟨value.1, active⟩,
          Classical.choose (execution value active bounded)) else value else value
    let condition (value : Value) := decide (value.1 < columns)
    let entryTape (value : Value) := (Tape.configuration () [] (frame value)).Tape
    let resultTape (value : Value) := (Tape.configuration () [] (data (condition value) :: frame value)).Tape
    let invariant (value : Value) := value.1 ≤ columns ∧ value.2.1.2 ≤ rows ∧
      GaussJordan.eliminateColumns value.2.1.1 value.2.1.2 ((List.finRange columns).drop value.1) =
        GaussJordan.eliminateColumns matrix 0 (List.finRange columns)
    let initial : Value := (0, (matrix, 0), initialScalar)
    have initialValid : invariant initial := by simp [initial, invariant]
    have preserves : ∀ value, invariant value → condition value = true → invariant (advance value) := by
      intro value valid positive
      have active : value.1 < columns := by simpa only [condition, decide_eq_true_eq] using positive
      have remaining : (List.finRange columns).drop value.1 =
          ⟨value.1, active⟩ :: (List.finRange columns).drop (value.1 + 1) := by
        rw [List.drop_eq_getElem_cons (l := List.finRange columns) (i := value.1) (by simpa using active)]
        congr 1
        apply Fin.ext
        simp
      refine ⟨?_, ?_, ?_⟩
      · simp only [advance, dite_eq_left active, dite_eq_left valid.2.1]; omega
      · simpa only [advance, dite_eq_left active, dite_eq_left valid.2.1] using
          (GaussJordan.columnStep_row_bound value.2.1.1 value.2.1.2 ⟨value.1, active⟩ valid.2.1).2
      · have equality := valid.2.2
        rw [remaining, GaussJordan.eliminateColumns] at equality
        simpa only [advance, dite_eq_left active, dite_eq_left valid.2.1] using equality
    have nextIndex (value : Value) (active : value.1 < columns) (bounded : value.2.1.2 ≤ rows) :
        (advance value).1 = value.1 + 1 := by
      simp only [advance, dite_eq_left active, dite_eq_left bounded]
    have iterates : ∀ count ≤ columns,
        (advance^[count] initial).1 = count ∧ invariant (advance^[count] initial) := by
      intro count
      induction count with
      | zero => intro _; exact ⟨rfl, initialValid⟩
      | succ count hypothesis =>
        intro bounded
        obtain ⟨index, valid⟩ := hypothesis (by omega)
        have active : (advance^[count] initial).1 < columns := by omega
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', nextIndex _ active valid.2.1, index]
        · simpa only [Function.iterate_succ_apply'] using preserves _ valid (by simp [condition, active])
    have guards : ∀ value, invariant value → ∃ ticks,
        ticks ≤ guardBound.eval (assignment rows columns) ∧
          Tape.Steps guard ticks ⟨guardEntry, entryTape value⟩ ⟨guardExit, resultTape value⟩ := by
      intro value valid
      have trace := HeaderGuardMachine.realizes [value.2.1.2, rows] value.1 columns (suffix value) valid.1
      refine ⟨2 * value.1 ^ 2 + 10 * value.1 + 2 * (UnaryMachine.fields [value.2.1.2, rows]).length + 8, ?_, ?_⟩
      · have square := Nat.pow_le_pow_left valid.1 2
        have rowBound := valid.2.1
        simp [guardBound, assignment]; nlinarith
      · simpa [guard, guardEntry, guardExit, entryTape, resultTape, frame, condition,
          UnaryMachine.fields, Tape.configuration, List.append_assoc] using trace
    have bodies : ∀ value, invariant value → condition value = true → ∃ ticks,
        ticks ≤ bodyBound.eval (assignment rows columns) ∧
          Tape.Steps body ticks ⟨bodyEntry, resultTape value⟩ ⟨bodyExit, entryTape (advance value)⟩ := by
      intro value valid positive
      have active : value.1 < columns := by simpa only [condition, decide_eq_true_eq] using positive
      obtain ⟨ticks, cost, trace, _, _, nextBound⟩ := Classical.choose_spec (execution value active valid.2.1)
      let next : Value := (value.1, GaussJordan.columnStep value.2.1.1 value.2.1.2 ⟨value.1, active⟩,
        Classical.choose (execution value active valid.2.1))
      have trace' : Tape.Steps stepMachine ticks
          ⟨stepEntry, entryTape value⟩ ⟨stepExit, entryTape next⟩ := by
        simpa only [execution, entryTape, frame, suffix, next, matrixWidth, Tape.configuration,
          List.append_assoc] using trace
      have consumed := HeaderGuardMachine.consumes true (frame value)
      have firstTrace := Tape.sequence_steps stepEntry consumed HeaderGuardMachine.consume_halt trace'
      have incremented := HeaderIncrementMachine.realizes [next.2.1.2, rows] value.1
        (UnaryMachine.fields [columns] ++ suffix next)
      have incremented' : Tape.Steps incrementer (3 * (next.2.1.2 + rows + 2) + 2)
          ⟨incrementEntry, entryTape next⟩ ⟨.inr (0, 2), entryTape (advance value)⟩ := by
        simpa [incrementer, incrementEntry, entryTape, frame, next, advance, active, valid.2.1,
          suffix, UnaryMachine.fields, Tape.configuration, List.append_assoc, Nat.add_assoc] using incremented
      have firstHalt (symbol : Symbol) : firstBody (.inr stepExit) symbol = none := by
        simp [firstBody, Tape.sequence, stepHalt]
      have computation := Tape.sequence_steps incrementEntry firstTrace firstHalt incremented'
      refine ⟨2 + (ticks + 1) + (3 * (next.2.1.2 + rows + 2) + 2 + 1), ?_, ?_⟩
      · change (GaussJordan.columnStep value.2.1.1 value.2.1.2 ⟨value.1, active⟩).2 ≤ rows at nextBound
        simp only [next]
        simp only [bodyBound, SizePolynomial.eval_add, SizePolynomial.eval_mul,
          SizePolynomial.eval_constant, SizePolynomial.eval_parameter, assignment]
        omega
      · simpa [body, bodyEntry, bodyExit, firstBody, resultTape, entryTape, condition, active,
          Tape.configuration, List.append_assoc] using computation
    have loopResult := WhileMachine.realizes guard body guardEntry guardExit bodyEntry bodyExit
      entryTape resultTape condition advance invariant (guardBound.eval (assignment rows columns))
      (bodyBound.eval (assignment rows columns)) (by intro symbol; exact HeaderGuardMachine.halt symbol)
      (by intro symbol; simp [body, bodyExit, incrementer, Tape.sequence, HeaderIncrementMachine.halt])
      (by intro value _; simp [resultTape, Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk])
      preserves guards bodies initial initialValid columns
      (by intro count earlier; simp [condition, (iterates count (by omega)).1, earlier])
      (by simp [condition, (iterates columns le_rfl).1])
    obtain ⟨loopTicks, loopCost, loopTrace, loopHalt⟩ := loopResult
    let final := advance^[columns] initial
    have finalIndex : final.1 = columns := (iterates columns le_rfl).1
    have finalValid : invariant final := (iterates columns le_rfl).2
    have finalResult : final.2.1 = GaussJordan.eliminateColumns matrix 0 (List.finRange columns) := by
      have equality := finalValid.2.2
      have empty : (List.finRange columns).drop columns = [] := List.drop_eq_nil_of_le (by simp)
      rw [finalIndex, empty, GaussJordan.eliminateColumns] at equality
      exact equality
    have finalMatrix : final.2.1.1 = GaussJordan.eliminate matrix := by
      exact congrArg Prod.fst finalResult
    have consumed := HeaderGuardMachine.consumes false (frame final)
    have consumed' : Tape.Steps HeaderGuardMachine.consume 2
        ⟨0, resultTape final⟩ ⟨2, entryTape final⟩ := by
      simpa [resultTape, entryTape, condition, finalIndex, Tape.configuration] using consumed
    have computation := Tape.sequence_steps_of_halt 0 loopTrace loopHalt consumed'
    refine ⟨final.2.1.2, final.2.2, loopTicks + (2 + 1), ?_, ?_, finalValid.2.1, ?_⟩
    · have boundValue : loopBound.eval (assignment rows columns) = (columns + 1) *
          (guardBound.eval (assignment rows columns) + bodyBound.eval (assignment rows columns) + 2) := by
        simp [loopBound, assignment]
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant, boundValue]
      omega
    · simpa only [loop, initial, entryTape, frame, suffix, finalIndex, finalMatrix, matrixWidth,
        Tape.configuration, List.append_assoc] using computation
    · exact GaussJordan.correct matrix

end Elimination

end Polytime.Examples.MatrixEliminate
