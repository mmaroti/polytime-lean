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

import Polytime.Examples.MatrixClearTargetStep
import Polytime.HeaderGuardMachine
import Polytime.WhileMachine

/-! # Clearing a runtime interval of target rows

A restoring guard and the certified target step traverse `[start, limit)`.
The interval excludes the pivot row, so the source row remains unchanged.
The matrix formula and row equivalence are proved together as a loop invariant.
-/

namespace Polytime.Examples.MatrixClearRange

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section TargetRange

/-- Clear the target rows in a runtime interval disjoint from the source row.
The final target counter is the interval limit, and the final guard bit is erased. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source : Fin rows) (start limit : ℕ) (_ordered : start ≤ limit) (_limitBound : limit ≤ rows)
          (_outside : limit ≤ source.val ∨ source.val < start) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated : Matrix (Fin rows) (Fin columns) field.Carrier := fun row index =>
            if start ≤ row.val ∧ row.val < limit then
              matrix row index + -matrix row column * matrix source index else matrix row index
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, start, limit, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, limit, limit, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated ∧
            (matrix source column = 1 → ∀ row : Fin rows,
              start ≤ row.val → row.val < limit → updated row column = 0) := by
  classical
  obtain ⟨StepState, finite, inhabited, stepEntry, stepExit, stepMachine, stepBound,
    stepHalt, stepRuns⟩ := MatrixClearTargetStep.realizes_with_counters field extraCount extraBound
  let stepControllerFinite : Fintype StepState := finite
  let stepControllerInhabited : Inhabited StepState := inhabited
  let guard := HeaderGuardMachine.machine 1
  let guardEntry : HeaderGuardMachine.State 1 := (Fin.last 1, false, 0)
  let guardExit : HeaderGuardMachine.State 1 := (0, false, 14)
  let body := Tape.sequence HeaderGuardMachine.consume stepMachine stepEntry
  let bodyEntry : Sum (Fin 3) StepState := .inl 0
  let bodyExit : Sum (Fin 3) StepState := .inr stepExit
  let loop := WhileMachine.machine guard body guardEntry bodyEntry
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K ^ 2 +
      SizePolynomial.constant 12 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 10
  let loopBound : SizePolynomial Matrices.context :=
    (SizePolynomial.parameter (ctx := Matrices.context) .K + 1) *
      (guardBound + stepBound + SizePolynomial.constant 5)
  refine ⟨Sum (Sum (HeaderGuardMachine.State 1) (Sum (Fin 3) StepState)) (Fin 3),
    inferInstance, inferInstance, .inl (.inl guardEntry), .inr 2,
    Tape.sequence loop HeaderGuardMachine.consume 0, loopBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderGuardMachine.consume_halt]
  · intro rows columns matrix source start limit ordered limitBound outside column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let Value := ℕ × Matrix (Fin rows) (Fin columns) field.Carrier × field.Carrier
    let frame (value : Value) := UnaryMachine.fields ([source.val, value.1, limit, 0, columns, column.val] ++ extra) ++
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode value.2.2))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value.2.1).getLsbD index.val)) ++ right))
    let execution (value : Value) (active : value.1 < rows) :=
      stepRuns rows columns value.2.1 source ⟨value.1, active⟩ limit limitBound column extra extraLength extraBounded value.2.2 right
    let advance (value : Value) : Value := if active : value.1 < rows then
      (value.1 + 1, Function.update value.2.1 ⟨value.1, active⟩
        (fun index => value.2.1 ⟨value.1, active⟩ index +
          -value.2.1 ⟨value.1, active⟩ column * value.2.1 source index),
        Classical.choose (execution value active)) else value
    let condition (value : Value) := decide (value.1 < limit)
    let entryTape (value : Value) := (Tape.configuration () [] (frame value)).Tape
    let resultTape (value : Value) := (Tape.configuration () [] (data (condition value) :: frame value)).Tape
    let invariant (value : Value) := start ≤ value.1 ∧ value.1 ≤ limit ∧
      (∀ row index, value.2.1 row index = if start ≤ row.val ∧ row.val < value.1 then
        matrix row index + -matrix row column * matrix source index else matrix row index) ∧
      Matrix.RowEquivalent matrix value.2.1
    let initial : Value := (start, matrix, initialScalar)
    have initialValid : invariant initial := by
      refine ⟨le_rfl, ordered, ?_, Matrix.RowEquivalent.refl matrix⟩
      intro row index
      have impossible : ¬(start ≤ row.val ∧ row.val < start) := by omega
      simp [initial, impossible]
    have preserves : ∀ value, invariant value → condition value = true → invariant (advance value) := by
      intro value valid positive
      simp only [condition, decide_eq_true_eq] at positive
      have active : value.1 < rows := by omega
      let target : Fin rows := ⟨value.1, active⟩
      have distinct : source ≠ target := by
        intro equal
        have equality : source.val = value.1 := congrArg Fin.val equal
        rcases outside with before | after <;> omega
      have sourceUnprocessed : ¬(start ≤ source.val ∧ source.val < value.1) := by
        rcases outside with before | after <;> omega
      have oldSource (index : Fin columns) : value.2.1 source index = matrix source index := by
        simpa only [sourceUnprocessed, ↓reduceIte] using valid.2.2.1 source index
      have oldTarget (index : Fin columns) : value.2.1 target index = matrix target index := by
        simpa only [target, Fin.val_mk, lt_self_iff_false, and_false, ↓reduceIte] using valid.2.2.1 target index
      refine ⟨by simp [advance, active]; omega, by simp [advance, active]; omega, ?_, ?_⟩
      · intro row index
        by_cases same : row.val = value.1
        · have equal : row = target := Fin.ext same
          subst row
          simp [advance, active, target, Function.update, oldTarget, oldSource, valid.1]
        · have unequal : row ≠ target := by intro equal; exact same (congrArg Fin.val equal)
          have cutoff : row.val < value.1 + 1 ↔ row.val < value.1 := by omega
          simpa [advance, active, unequal, target, Function.update, cutoff] using valid.2.2.1 row index
      · have equivalent := MatrixOperations.addRow_rowEquivalent value.2.1 source target
          (-value.2.1 target column) distinct
        simpa only [advance, dite_eq_left active, target] using valid.2.2.2.trans equivalent
    have nextIndex (value : Value) (active : value.1 < rows) : (advance value).1 = value.1 + 1 := by
      simp only [advance, dite_eq_left active]
    have iterates : ∀ count ≤ limit - start,
        (advance^[count] initial).1 = start + count ∧ invariant (advance^[count] initial) := by
      intro count
      induction count with
      | zero => intro _; exact ⟨by simp [initial], initialValid⟩
      | succ count hypothesis =>
        intro bounded
        obtain ⟨index, valid⟩ := hypothesis (by omega)
        have positive : (advance^[count] initial).1 < limit := by omega
        have active : (advance^[count] initial).1 < rows := by omega
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply']
          rw [nextIndex _ active, index]
          omega
        · simpa only [Function.iterate_succ_apply'] using preserves _ valid (by simp [condition, positive])
    have guards : ∀ value, invariant value → ∃ ticks,
        ticks ≤ guardBound.eval (assignment rows columns) ∧
          Tape.Steps guard ticks ⟨guardEntry, entryTape value⟩ ⟨guardExit, resultTape value⟩ := by
      intro value valid
      have trace := HeaderGuardMachine.realizes [source.val] value.1 limit
        (UnaryMachine.fields ([0, columns, column.val] ++ extra) ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode value.2.2))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 ::
              (word (List.ofFn (fun index : Fin matrixWidth =>
                (encode field rows columns value.2.1).getLsbD index.val)) ++ right))) valid.2.1
      refine ⟨2 * value.1 ^ 2 + 10 * value.1 + 2 * (UnaryMachine.fields [source.val]).length + 8, ?_, ?_⟩
      · have indexBound : value.1 ≤ rows := valid.2.1.trans limitBound
        have square := Nat.pow_le_pow_left indexBound 2
        have sourceBound := source.isLt
        simp [guardBound, assignment]; nlinarith
      · simpa [guard, guardEntry, guardExit, entryTape, resultTape, frame, condition,
          UnaryMachine.fields, UnaryMachine.fields_append, Tape.configuration, List.append_assoc] using trace
    have bodies : ∀ value, invariant value → condition value = true → ∃ ticks,
        ticks ≤ stepBound.eval (assignment rows columns) + 3 ∧
          Tape.Steps body ticks ⟨bodyEntry, resultTape value⟩ ⟨bodyExit, entryTape (advance value)⟩ := by
      intro value _ positive
      simp only [condition, decide_eq_true_eq] at positive
      have active : value.1 < rows := by omega
      obtain ⟨ticks, cost, trace, _, _⟩ := Classical.choose_spec (execution value active)
      have trace' : Tape.Steps stepMachine ticks
          ⟨stepEntry, entryTape value⟩ ⟨stepExit, entryTape (advance value)⟩ := by
        simp only [entryTape, frame, advance, dite_eq_left active]
        simpa only [execution, matrixWidth, Tape.configuration] using trace
      have consumed := HeaderGuardMachine.consumes true (frame value)
      have computation := Tape.sequence_steps stepEntry consumed HeaderGuardMachine.consume_halt trace'
      refine ⟨2 + (ticks + 1), by omega, ?_⟩
      simpa [body, bodyEntry, bodyExit, resultTape, condition, positive, Tape.configuration] using computation
    have loopResult := WhileMachine.realizes guard body guardEntry guardExit bodyEntry bodyExit
      entryTape resultTape condition advance invariant (guardBound.eval (assignment rows columns))
      (stepBound.eval (assignment rows columns) + 3) (by intro symbol; exact HeaderGuardMachine.halt symbol)
      (by intro symbol; simp [body, bodyExit, Tape.sequence, stepHalt])
      (by intro value _; simp [resultTape, Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk])
      preserves guards bodies initial initialValid (limit - start)
      (by intro count earlier; simp [condition, (iterates count (by omega)).1]; omega)
      (by simp [condition, (iterates (limit - start) le_rfl).1, Nat.add_sub_of_le ordered])
    obtain ⟨loopTicks, loopCost, loopTrace, loopHalt⟩ := loopResult
    let final := advance^[limit - start] initial
    have finalIndex : final.1 = limit := by
      have index := (iterates (limit - start) le_rfl).1
      simpa [Nat.add_sub_of_le ordered] using index
    have finalValid : invariant final := (iterates (limit - start) le_rfl).2
    let updated : Matrix (Fin rows) (Fin columns) field.Carrier := fun row index =>
      if start ≤ row.val ∧ row.val < limit then
        matrix row index + -matrix row column * matrix source index else matrix row index
    have finalMatrix : final.2.1 = updated := by
      funext row index
      simpa only [finalIndex, updated] using finalValid.2.2.1 row index
    have consumed := HeaderGuardMachine.consumes false (frame final)
    have consumed' : Tape.Steps HeaderGuardMachine.consume 2
        ⟨0, resultTape final⟩ ⟨2, entryTape final⟩ := by
      simpa [resultTape, entryTape, condition, finalIndex, Tape.configuration] using consumed
    have computation := Tape.sequence_steps_of_halt 0 loopTrace loopHalt consumed'
    refine ⟨final.2.2, loopTicks + (2 + 1), ?_, ?_, ?_, ?_⟩
    · have dominated := Nat.mul_le_mul_right
        (guardBound.eval (assignment rows columns) + (stepBound.eval (assignment rows columns) + 3) + 2)
        (show limit - start + 1 ≤ rows + 1 by omega)
      have boundValue : loopBound.eval (assignment rows columns) = (rows + 1) *
          (guardBound.eval (assignment rows columns) + (stepBound.eval (assignment rows columns) + 3) + 2) := by
        simp [loopBound, assignment]; ring
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant, boundValue]
      omega
    · simpa only [loop, initial, entryTape, frame, finalIndex, finalMatrix, updated, matrixWidth,
        Tape.configuration] using computation
    · simpa only [finalMatrix, updated] using finalValid.2.2.2
    · intro normalized row eligible earlier
      simp [eligible, earlier, normalized]

/-- Clear a target interval with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source : Fin rows) (start limit : ℕ) (_ordered : start ≤ limit) (_limitBound : limit ≤ rows)
          (_outside : limit ≤ source.val ∨ source.val < start) (column : Fin columns)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated : Matrix (Fin rows) (Fin columns) field.Carrier := fun row index =>
            if start ≤ row.val ∧ row.val < limit then
              matrix row index + -matrix row column * matrix source index else matrix row index
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, start, limit, 0, columns, column.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, limit, limit, 0, columns, column.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated ∧
            (matrix source column = 1 → ∀ row : Fin rows,
              start ≤ row.val → row.val < limit → updated row column = 0) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source start limit ordered limitBound outside column initialScalar right
  simpa only [List.append_nil] using
    runs rows columns matrix source start limit ordered limitBound outside column [] rfl
      (by simp [UnaryMachine.fields]) initialScalar right

end TargetRange

end Polytime.Examples.MatrixClearRange
