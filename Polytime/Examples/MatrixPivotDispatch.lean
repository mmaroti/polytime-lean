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

import Polytime.NamedHeader
import Polytime.Examples.MatrixPivotStep
import Polytime.FiniteDispatchMachine

/-! # Dispatching a completed pivot search

A runtime comparison distinguishes a found pivot from the row-count sentinel.
Both branches return the same four-counter frame for the outer column loop.
-/

namespace Polytime.Examples.MatrixPivotDispatch

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

/-- Candidate and saved starting row remain distinct header roles. -/
inductive HeaderField
  | zeroColumn | candidate | rowCount | column | columnCount | start
  deriving DecidableEq

def prepareSource : List HeaderField := [.zeroColumn, .candidate, .rowCount, .column, .columnCount, .start]
def prepareTarget : List HeaderField := [.start, .candidate, .zeroColumn, .columnCount, .column, .rowCount]
def prepareMoves : List HeaderField := prepareTarget.reverse

def skipSource : List HeaderField := [.candidate, .rowCount, .column, .columnCount, .start]
def skipTarget : List HeaderField := [.candidate, .start, .rowCount, .column, .columnCount]
def skipMoves : List HeaderField := skipTarget.reverse

noncomputable section SearchDispatch

/-- Consume a search result and its saved starting row. A found pivot performs
one complete pivot step; the sentinel preserves the matrix and next-row counter. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (start candidate : ℕ) (_ordered : start ≤ candidate) (_bounded : candidate ≤ rows)
          (column : Fin columns) (_nonzero : ∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := if valid : candidate < rows then
            MatrixOperations.pivotStep matrix ⟨start, lt_of_le_of_lt _ordered valid⟩ ⟨candidate, valid⟩ column else matrix
          let nextRow := if candidate < rows then start + 1 else start
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [nextRow, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  classical
  obtain ⟨PivotState, pivotFinite, pivotInhabited, pivotEntry, pivotExit, pivotMachine,
    pivotBound, pivotHalt, pivotRuns⟩ := MatrixPivotStep.realizes_restored field
  let pivotControllerFinite : Fintype PivotState := pivotFinite
  let pivotControllerInhabited : Inhabited PivotState := pivotInhabited
  obtain ⟨PrepareState, prepareFinite, prepareInhabited, prepareEntry, prepareExit, prepare,
    prepareHalt, prepareRuns⟩ := NamedHeader.realizes prepareSource prepareMoves (by decide)
  let prepareControllerFinite : Fintype PrepareState := prepareFinite
  let prepareControllerInhabited : Inhabited PrepareState := prepareInhabited
  obtain ⟨SkipState, skipFinite, skipInhabited, skipEntry, skipExit, skip,
    skipHalt, skipRuns⟩ := NamedHeader.realizes skipSource skipMoves (by decide)
  let skipControllerFinite : Fintype SkipState := skipFinite
  let skipControllerInhabited : Inhabited SkipState := skipInhabited
  obtain ⟨RemoveState, removeFinite, removeInhabited, removeEntry, removeExit, remover,
    removeHalt, removeRuns⟩ := HeaderMoves.realizes_remove_front 1
  let removeControllerFinite : Fintype RemoveState := removeFinite
  let removeControllerInhabited : Inhabited RemoveState := removeInhabited
  let zeroer := SizeMachine.Constant.machine 0
  let zeroEntry : SizeMachine.Constant.State 0 := (Fin.last 0, 0)
  let zeroExit : SizeMachine.Constant.State 0 := (0, 4)
  let preparedMachine := Tape.sequence zeroer prepare prepareEntry
  let trueMachine := Tape.sequence preparedMachine pivotMachine pivotEntry
  let falseMachine := Tape.sequence skip remover removeEntry
  let TrueState := Sum (Sum (SizeMachine.Constant.State 0) PrepareState) PivotState
  let FalseState := Sum SkipState RemoveState
  let Bits := Fin 1 → Bool
  let Branch (_bits : Bits) := Sum TrueState FalseState
  let branches (_bits : Bits) : Turing.TM0.Machine Symbol (Branch _bits) := fun state symbol =>
    match state with
    | .inl next => (trueMachine next symbol).map (fun (state, action) => (Sum.inl state, action))
    | .inr next => (falseMachine next symbol).map (fun (state, action) => (Sum.inr state, action))
  let entries (bits : Bits) : Branch bits := if bits 0 then .inl (.inl (.inl zeroEntry)) else .inr (.inl skipEntry)
  let exits (bits : Bits) : Branch bits := if bits 0 then .inl (.inr pivotExit) else .inr (.inr removeExit)
  have halts (bits : Bits) (symbol : Symbol) : branches bits (exits bits) symbol = none := by
    cases selected : bits 0 <;> simp [branches, exits, selected, trueMachine, falseMachine,
      Tape.sequence, pivotHalt, removeHalt]
  let guard := HeaderGuardMachine.machine 0
  let guardEntry : HeaderGuardMachine.State 0 := (Fin.last 0, false, 0)
  let guardExit : HeaderGuardMachine.State 0 := (0, false, 14)
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 7
  let relocationBound := SizePolynomial.constant 6 * (SizePolynomial.constant 128 * headerBound ^ 2 + 1)
  let removalBound := SizePolynomial.constant 4 * headerBound + SizePolynomial.constant 8
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 8
  refine ⟨Sum (HeaderGuardMachine.State 0) (FiniteDispatchMachine.State Branch),
    inferInstance, inferInstance, .inl guardEntry, .inr (.inr (.inr ())),
    Tape.sequence guard (FiniteDispatchMachine.machine branches entries) (.inl (0, (fun _ => false), 0)),
    guardBound + pivotBound + SizePolynomial.constant 2 * relocationBound + removalBound + SizePolynomial.constant 15, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, FiniteDispatchMachine.halt]
  · intro rows columns matrix start candidate ordered bounded column nonzero initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let headerValues : HeaderField → ℕ
      | .zeroColumn => 0
      | .candidate => candidate
      | .rowCount => rows
      | .column => column.val
      | .columnCount => columns
      | .start => start
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    let updated := if valid : candidate < rows then
      MatrixOperations.pivotStep matrix ⟨start, lt_of_le_of_lt ordered valid⟩ ⟨candidate, valid⟩ column else matrix
    let nextRow := if candidate < rows then start + 1 else start
    let selector : Bits := fun _ => decide (candidate < rows)
    have guarded := HeaderGuardMachine.realizes [] candidate rows
      (UnaryMachine.fields [column.val, columns, start] ++ suffix matrix initialScalar) bounded
    have guarded' : Tape.Steps guard (2 * candidate ^ 2 + 10 * candidate + 8)
        (Tape.configuration guardEntry []
          (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar))
        (Tape.configuration guardExit []
          (word (List.ofFn selector) ++ UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar)) := by
      simpa [guard, guardEntry, guardExit, selector, word, UnaryMachine.fields, List.append_assoc] using guarded
    have storage : (UnaryMachine.fields [0, candidate, rows, column.val, columns, start]).length + 1 ≤
        headerBound.eval (assignment rows columns) := by
      have columnBound := column.isLt
      simp [headerBound, assignment]; omega
    have relocationCost : 6 * (128 * ((UnaryMachine.fields [0, candidate, rows, column.val, columns, start]).length + 1) ^ 2 + 1) ≤
        relocationBound.eval (assignment rows columns) := by
      simp only [relocationBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one]
      exact Nat.mul_le_mul_left 6 (Nat.add_le_add_right (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left storage 2)) 1)
    have branchRun : ∃ (finalScalar : field.Carrier) (ticks : ℕ),
        ticks ≤ pivotBound.eval (assignment rows columns) +
          2 * relocationBound.eval (assignment rows columns) + removalBound.eval (assignment rows columns) + 6 ∧
          Tape.Steps (branches selector) ticks
            (Tape.configuration (entries selector) []
              (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar))
            (Tape.configuration (exits selector) []
              (UnaryMachine.fields [nextRow, rows, column.val, columns] ++ suffix updated finalScalar)) := by
      by_cases active : candidate < rows
      · have zeroed := SizeMachine.Constant.realizes 0
          (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar)
        obtain ⟨prepareTicks, prepareCost, prepared⟩ := prepareRuns headerValues (suffix matrix initialScalar)
        change prepareTicks ≤ 6 * (128 * ((UnaryMachine.fields
          [0, candidate, rows, column.val, columns, start]).length + 1) ^ 2 + 1) at prepareCost
        have prepared' : Tape.Steps prepare prepareTicks
            (Tape.configuration prepareEntry []
              (UnaryMachine.fields [0, candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar))
            (Tape.configuration prepareExit []
              (UnaryMachine.fields [start, candidate, 0, columns, column.val, rows] ++ suffix matrix initialScalar)) := by
          simpa [prepareSource, prepareTarget, prepareMoves, headerValues, NamedHeader.result, NamedHeader.move] using prepared
        have zeroed' : Tape.Steps zeroer 3
            (Tape.configuration zeroEntry []
              (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar))
            (Tape.configuration zeroExit []
              (UnaryMachine.fields [0, candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar)) := by
          simpa [zeroer, zeroEntry, zeroExit, UnaryMachine.fields, UnaryMachine.units] using zeroed
        have zeroHalt (symbol : Symbol) : zeroer zeroExit symbol = none := by
          simp [zeroer, zeroExit, SizeMachine.Constant.machine]
        have firstTrace := Tape.sequence_steps prepareEntry zeroed' zeroHalt prepared'
        obtain ⟨finalScalar, pivotTicks, pivotCost, pivotTrace, _, _, _⟩ := pivotRuns rows columns matrix
          ⟨start, lt_of_le_of_lt ordered active⟩ ⟨candidate, active⟩ ordered column (nonzero active) initialScalar right
        simp only [List.append_assoc] at pivotTrace
        have firstHalt (symbol : Symbol) : preparedMachine (.inr prepareExit) symbol = none := by
          simp [preparedMachine, Tape.sequence, prepareHalt]
        have trace := Tape.sequence_steps pivotEntry firstTrace firstHalt pivotTrace
        have renamed := trace.rename Sum.inl (targetMachine := branches selector)
          (by
            intro state symbol next action transition
            change trueMachine state symbol = some (next, action) at transition
            simp only [branches, transition, Option.map_some])
        have prepareBounded : prepareTicks ≤ relocationBound.eval (assignment rows columns) := by
          apply prepareCost.trans
          simpa only [List.length_cons, List.length_nil] using relocationCost
        refine ⟨finalScalar, 3 + (prepareTicks + 1) + (pivotTicks + 1), by omega, ?_⟩
        simpa [entries, exits, selector, trueMachine, preparedMachine, zeroer, zeroEntry,
          nextRow, updated, active, suffix, matrixWidth, Tape.configuration, List.append_assoc] using renamed
      · obtain ⟨skipTicks, skipCost, skipped⟩ := skipRuns headerValues (suffix matrix initialScalar)
        change skipTicks ≤ 5 * (128 * ((UnaryMachine.fields
          [candidate, rows, column.val, columns, start]).length + 1) ^ 2 + 1) at skipCost
        have skipped' : Tape.Steps skip skipTicks
            (Tape.configuration skipEntry []
              (UnaryMachine.fields [candidate, rows, column.val, columns, start] ++ suffix matrix initialScalar))
            (Tape.configuration skipExit []
              (UnaryMachine.fields [candidate, start, rows, column.val, columns] ++ suffix matrix initialScalar)) := by
          simpa [skipSource, skipTarget, skipMoves, headerValues, NamedHeader.result, NamedHeader.move] using skipped
        obtain ⟨removeTicks, removeCost, removed⟩ := removeRuns
          [candidate, start, rows, column.val, columns] (by simp) (suffix matrix initialScalar)
        have removed' : Tape.Steps remover removeTicks
            (Tape.configuration removeEntry []
              (UnaryMachine.fields [candidate, start, rows, column.val, columns] ++ suffix matrix initialScalar))
            (Tape.configuration removeExit []
              (UnaryMachine.fields [start, rows, column.val, columns] ++ suffix matrix initialScalar)) := by
          simpa only [List.drop_succ_cons, List.drop_zero] using removed
        have trace := Tape.sequence_steps removeEntry skipped' skipHalt removed'
        have renamed := trace.rename Sum.inr (targetMachine := branches selector)
          (by
            intro state symbol next action transition
            change falseMachine state symbol = some (next, action) at transition
            simp only [branches, transition, Option.map_some])
        have skipBounded : skipTicks ≤ relocationBound.eval (assignment rows columns) := by
          have lengthBound : (UnaryMachine.fields [candidate, rows, column.val, columns, start]).length + 1 ≤
              (UnaryMachine.fields [0, candidate, rows, column.val, columns, start]).length + 1 := by
            simp [UnaryMachine.fields]
          have dominated := Nat.mul_le_mul_left 6 (Nat.add_le_add_right
            (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left lengthBound 2)) 1)
          nlinarith
        have removeBounded : removeTicks ≤ removalBound.eval (assignment rows columns) := by
          have smaller : (UnaryMachine.fields [candidate, start, rows, column.val, columns]).length ≤
              (UnaryMachine.fields [0, candidate, rows, column.val, columns, start]).length + 1 := by
            simp [UnaryMachine.fields]; omega
          simp only [removalBound, SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
          omega
        refine ⟨initialScalar, skipTicks + (removeTicks + 1), by omega, ?_⟩
        simpa [entries, exits, selector, falseMachine, nextRow, updated, active, Tape.configuration] using renamed
    obtain ⟨finalScalar, ticks, cost, trace⟩ := branchRun
    have dispatched := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      ticks _ _ (halts selector) trace
    have computation := Tape.sequence_steps
      (Sum.inl (0, (fun _ => false), 0) : FiniteDispatchMachine.State Branch)
      guarded' (by intro symbol; exact HeaderGuardMachine.halt symbol) dispatched
    have guardCost : 2 * candidate ^ 2 + 10 * candidate + 8 ≤ guardBound.eval (assignment rows columns) := by
      have square := Nat.pow_le_pow_left bounded 2
      simp [guardBound, assignment]; nlinarith
    refine ⟨finalScalar, (2 * candidate ^ 2 + 10 * candidate + 8) + (4 * 1 + ticks + 4 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [guard, guardEntry, nextRow, updated, suffix, matrixWidth,
        Tape.configuration, List.append_assoc] using computation

end SearchDispatch

end Polytime.Examples.MatrixPivotDispatch
