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

import Polytime.Examples.MatrixClearRowSaved
import Polytime.HeaderMoves
import Polytime.HeaderIncrementMachine

/-! # One target-row iteration of column elimination

Retain the row limit and pivot column, change to the row-operation layout,
clear the target, restore the guard layout, and increment the target counter.
-/

namespace Polytime.Examples.MatrixClearTargetStep

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeTarget

/-- Clear one runtime target row and advance its counter in the loop-guard
layout. The row limit and saved pivot column survive the entire computation. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (limit : ℕ) (_limitBound : limit ≤ rows)
          (column : Fin columns) (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target
            (fun index => matrix target index + -matrix target column * matrix source index)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, target.val, limit, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val + 1, limit, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (matrix source column = 1 → updated target column = 0) ∧
            (source ≠ target → Matrix.RowEquivalent matrix updated) := by
  classical
  obtain ⟨PrepareState, prepareFinite, prepareInhabited, prepareEntry, prepareExit, prepare,
    prepareHalt, prepareRuns⟩ := HeaderMoves.realizes_guard_to_row
  let prepareControllerFinite : Fintype PrepareState := prepareFinite
  let prepareControllerInhabited : Inhabited PrepareState := prepareInhabited
  obtain ⟨RestoreState, restoreFinite, restoreInhabited, restoreEntry, restoreExit, restore,
    restoreHalt, restoreRuns⟩ := HeaderMoves.realizes_row_to_guard
  let restoreControllerFinite : Fintype RestoreState := restoreFinite
  let restoreControllerInhabited : Inhabited RestoreState := restoreInhabited
  obtain ⟨ClearState, clearFinite, clearInhabited, clearEntry, clearExit, clearer, clearBound,
    clearHalt, clearRuns⟩ := MatrixClearRowSaved.realizes_with_counters field (1 + extraCount)
      (SizePolynomial.parameter (ctx := Matrices.context) .K + 1 + extraBound)
  let clearControllerFinite : Fintype ClearState := clearFinite
  let clearControllerInhabited : Inhabited ClearState := clearInhabited
  let incrementer := HeaderIncrementMachine.machine 1
  let incrementEntry : HeaderIncrementMachine.State 1 := .inl (Fin.last 1)
  let first := Tape.sequence prepare clearer clearEntry
  let second := Tape.sequence first restore restoreEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 7
  let relocationBound := SizePolynomial.constant 6 * (SizePolynomial.constant 128 * headerBound ^ 2 + 1)
  let incrementBound := SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  refine ⟨Sum (Sum (Sum PrepareState ClearState) RestoreState) (HeaderIncrementMachine.State 1),
    inferInstance, inferInstance, .inl (.inl (.inl prepareEntry)), .inr (.inr (0, 2)),
    Tape.sequence second incrementer incrementEntry,
    clearBound + SizePolynomial.constant 2 * relocationBound + incrementBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, incrementer, HeaderIncrementMachine.halt]
  · intro rows columns matrix source target limit limitBound column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let updated := Function.update matrix target
      (fun index => matrix target index + -matrix target column * matrix source index)
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    obtain ⟨prepareTicks, prepareCost, prepared⟩ :=
      prepareRuns source.val target.val limit 0 columns column.val (UnaryMachine.fields extra ++ suffix matrix initialScalar)
    obtain ⟨finalScalar, clearTicks, clearCost, cleared, zero, equivalent⟩ :=
      clearRuns rows columns matrix source target column (limit :: extra)
        (by simp [extraLength, Nat.add_comm])
        (by
          have extraCost := extraBounded
          simp [UnaryMachine.fields_length] at extraCost
          simp [assignment]
          omega) initialScalar right
    have cleared' : Tape.Steps clearer clearTicks
        (Tape.configuration clearEntry []
          (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val, limit] ++ extra) ++ suffix matrix initialScalar))
        (Tape.configuration clearExit []
          (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val, limit] ++ extra) ++ suffix updated finalScalar)) := by
      simpa only [suffix, updated, matrixWidth, List.cons_append, List.nil_append, List.append_assoc] using cleared
    obtain ⟨restoreTicks, restoreCost, restored⟩ :=
      restoreRuns source.val target.val limit 0 columns column.val (UnaryMachine.fields extra ++ suffix updated finalScalar)
    have incremented := HeaderIncrementMachine.realizes [source.val] target.val
      (UnaryMachine.fields ([limit, 0, columns, column.val] ++ extra) ++ suffix updated finalScalar)
    have incremented' : Tape.Steps incrementer (3 * (source.val + 1) + 2)
        (Tape.configuration incrementEntry []
          (UnaryMachine.fields ([source.val, target.val, limit, 0, columns, column.val] ++ extra) ++ suffix updated finalScalar))
        (Tape.configuration (.inr (0, 2)) []
          (UnaryMachine.fields ([source.val, target.val + 1, limit, 0, columns, column.val] ++ extra) ++ suffix updated finalScalar)) := by
      simpa [incrementer, incrementEntry, UnaryMachine.fields, List.append_assoc] using incremented
    have prepared' := prepared
    have restored' := restored
    simp only [← List.append_assoc, ← UnaryMachine.fields_append] at prepared' restored'
    have firstTrace := Tape.sequence_steps clearEntry prepared' prepareHalt cleared'
    have firstHalt (symbol : Symbol) : first (.inr clearExit) symbol = none := by
      simp [first, Tape.sequence, clearHalt]
    have secondTrace := Tape.sequence_steps restoreEntry firstTrace firstHalt restored'
    have secondHalt (symbol : Symbol) : second (.inr restoreExit) symbol = none := by
      simp [second, Tape.sequence, restoreHalt]
    have computation := Tape.sequence_steps incrementEntry secondTrace secondHalt incremented'
    have headerCost : source.val + target.val + limit + 0 + columns + column.val + 7 ≤
        headerBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have targetBound := target.isLt
      have columnBound := column.isLt
      simp [headerBound, assignment]; omega
    have relocationCost : 6 * (128 * (source.val + target.val + limit + 0 + columns + column.val + 7) ^ 2 + 1) ≤
        relocationBound.eval (assignment rows columns) := by
      simp only [relocationBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one]
      exact Nat.mul_le_mul_left 6 (Nat.add_le_add_right
        (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left headerCost 2)) 1)
    have advanceCost : 3 * (source.val + 1) + 2 ≤ incrementBound.eval (assignment rows columns) := by
      simp [incrementBound, assignment]
    refine ⟨finalScalar, prepareTicks + (clearTicks + 1) + (restoreTicks + 1) +
      (3 * (source.val + 1) + 2 + 1), ?_, ?_, zero, equivalent⟩
    · have firstCost := prepareCost.trans relocationCost
      have lastCost := restoreCost.trans relocationCost
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, incrementer, incrementEntry, suffix, updated, matrixWidth,
        Tape.configuration, List.append_assoc] using computation

/-- The target step with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (limit : ℕ) (_limitBound : limit ≤ rows)
          (column : Fin columns) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target
            (fun index => matrix target index + -matrix target column * matrix source index)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, target.val, limit, 0, columns, column.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val + 1, limit, 0, columns, column.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (matrix source column = 1 → updated target column = 0) ∧
            (source ≠ target → Matrix.RowEquivalent matrix updated) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target limit limitBound column initialScalar right
  simpa only [List.append_nil] using
    runs rows columns matrix source target limit limitBound column [] rfl
      (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeTarget

end Polytime.Examples.MatrixClearTargetStep
