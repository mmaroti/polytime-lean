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
import Polytime.Examples.MatrixRowSwap
import Polytime.Examples.MatrixNormalizeRowSaved
import Polytime.Examples.MatrixClearColumn

/-! # One complete runtime pivot step

Swap an ordered pair of runtime rows, normalize the selected nonzero pivot,
and clear its column. The saved dimensions and pivot column survive each stage.
-/

namespace Polytime.Examples.MatrixPivotStep

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

/-- Names distinguish header roles even when their counter values coincide. -/
inductive HeaderField
  | savedPivotRow | targetRow | rowLimit | zeroColumn | columnCount | pivotColumn | pivotRow
  deriving DecidableEq

def sourceLayout : List HeaderField := [.savedPivotRow, .targetRow, .rowLimit, .zeroColumn, .columnCount, .pivotColumn, .pivotRow]

def targetLayout : List HeaderField := [.rowLimit, .zeroColumn, .savedPivotRow, .pivotRow, .targetRow, .pivotColumn, .columnCount]

def relocation : List HeaderField := targetLayout.reverse

noncomputable section PivotStep

/-- Realize the mathematical pivot step on tape. The source row is supplied at
runtime; pivot search is a separate certified routine. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (target source : Fin rows) (_ordered : target.val ≤ source.val)
          (column : Fin columns) (_nonzero : matrix source column ≠ 0)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.pivotStep matrix target source column
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [target.val, source.val, 0, columns, column.val, rows] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [target.val, rows, rows, 0, columns, column.val, target.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated ∧ updated target column = 1 ∧
            (∀ row : Fin rows, row ≠ target → updated row column = 0) := by
  classical
  obtain ⟨SwapState, swapFinite, swapInhabited, swapEntry, swapExit, swapper,
    swapBound, swapHalt, swapRuns⟩ := MatrixRowSwap.realizes_ordered_with_counters field 2
      (SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2)
  let swapControllerFinite : Fintype SwapState := swapFinite
  let swapControllerInhabited : Inhabited SwapState := swapInhabited
  obtain ⟨NormalizeState, normalizeFinite, normalizeInhabited, normalizeEntry, normalizeExit,
    normalizer, normalizeBound, normalizeHalt, normalizeRuns⟩ := MatrixNormalizeRowSaved.realizes field 1
      (SizePolynomial.parameter (ctx := Matrices.context) .K + 1)
  let normalizeControllerFinite : Fintype NormalizeState := normalizeFinite
  let normalizeControllerInhabited : Inhabited NormalizeState := normalizeInhabited
  obtain ⟨ClearState, clearFinite, clearInhabited, clearEntry, clearExit, clearer,
    clearBound, clearHalt, clearRuns⟩ := MatrixClearColumn.realizes field
  let clearControllerFinite : Fintype ClearState := clearFinite
  let clearControllerInhabited : Inhabited ClearState := clearInhabited
  let exchanger := HeaderMoveMachine.machine 1
  let exchangeEntry : HeaderMoveMachine.State 1 := .inl (Fin.last 1, 0)
  let exchangeExit : HeaderMoveMachine.State 1 := .inr (.inr (.inr (0, 7)))
  let resetter := HeaderResetMachine.machine 0
  let resetEntry : HeaderResetMachine.State 0 := .inl (Fin.last 0)
  let copier := SizeMachine.Copy.machine 1
  let copyEntry : SizeMachine.Copy.State 1 := (Fin.last 1, 0)
  let copyExit : SizeMachine.Copy.State 1 := (0, 19)
  let first := Tape.sequence swapper exchanger exchangeEntry
  let second := Tape.sequence first normalizer normalizeEntry
  let third := Tape.sequence second resetter resetEntry
  let fourth := Tape.sequence third copier copyEntry
  let exchangeBound : SizePolynomial Matrices.context := SizePolynomial.constant 128 *
    (SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 5) ^ 2
  let resetBound := SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  let copyBound : SizePolynomial Matrices.context := SizePolynomial.constant 64 *
    (SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 7) ^ 2
  refine ⟨Sum (Sum (Sum (Sum (Sum SwapState (HeaderMoveMachine.State 1)) NormalizeState)
    (HeaderResetMachine.State 0)) (SizeMachine.Copy.State 1)) ClearState,
    inferInstance, inferInstance, .inl (.inl (.inl (.inl (.inl swapEntry)))), .inr clearExit,
    Tape.sequence fourth clearer clearEntry,
    swapBound + exchangeBound + normalizeBound + resetBound + copyBound + clearBound + SizePolynomial.constant 5, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, clearHalt]
  · intro rows columns matrix target source ordered column nonzero initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let swapped := MatrixOperations.swapRows matrix target source
    let normalized := MatrixOperations.scaleRow swapped target (matrix source column)⁻¹
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    have swappedPivot : swapped target column = matrix source column := by
      simp [swapped, MatrixOperations.swapRows]
    obtain ⟨swapScalar, swapTicks, swapCost, swappedTrace, _⟩ :=
      swapRuns rows columns matrix target source ordered [column.val, rows] rfl
        (by have columnBound := column.isLt; simp [assignment]; omega) initialScalar right
    obtain ⟨exchangeTicks, exchangeCost, exchanged⟩ :=
      HeaderMoveMachine.swaps_row_indices target.val source.val 0 columns
        (UnaryMachine.fields [column.val, rows] ++ suffix swapped swapScalar)
    simp only [List.cons_append, List.nil_append, List.append_assoc] at swappedTrace
    simp only [← List.append_assoc, ← UnaryMachine.fields_append, List.cons_append, List.nil_append] at exchanged
    have firstTrace := Tape.sequence_steps exchangeEntry swappedTrace swapHalt exchanged
    obtain ⟨normalizeScalar, normalizeTicks, normalizeCost, normalizedTrace, _⟩ :=
      normalizeRuns rows columns swapped source target column [rows] rfl
        (by simp [assignment]) swapScalar right
    rw [swappedPivot] at normalizedTrace
    simp only [List.cons_append, List.nil_append, List.append_assoc] at normalizedTrace
    have firstHalt (symbol : Symbol) : first (.inr exchangeExit) symbol = none := by
      simp [first, exchanger, exchangeExit, Tape.sequence, HeaderMoveMachine.halt]
    have secondTrace := Tape.sequence_steps normalizeEntry firstTrace firstHalt normalizedTrace
    have reset := HeaderResetMachine.realizes [] source.val
      (UnaryMachine.fields [target.val, 0, columns, column.val, rows] ++ suffix normalized normalizeScalar)
    have reset' : Tape.Steps resetter (4 * source.val + 2)
        (Tape.configuration resetEntry []
          (UnaryMachine.fields [source.val, target.val, 0, columns, column.val, rows] ++ suffix normalized normalizeScalar))
        (Tape.configuration (.inr (0, 8)) []
          (UnaryMachine.fields [0, target.val, 0, columns, column.val, rows] ++ suffix normalized normalizeScalar)) := by
      simpa [resetter, resetEntry, UnaryMachine.fields, List.append_assoc, Nat.mul_comm] using reset
    have secondHalt (symbol : Symbol) : second (.inr normalizeExit) symbol = none := by
      simp [second, Tape.sequence, normalizeHalt]
    have thirdTrace := Tape.sequence_steps resetEntry secondTrace secondHalt reset'
    obtain ⟨copyTicks, copyCost, copied⟩ := SizeMachine.Copy.realizes [0]
      [0, columns, column.val, rows] target.val (suffix normalized normalizeScalar)
    have copied' : Tape.Steps copier copyTicks
        (Tape.configuration copyEntry []
          (UnaryMachine.fields [0, target.val, 0, columns, column.val, rows] ++ suffix normalized normalizeScalar))
        (Tape.configuration copyExit []
          (UnaryMachine.fields [target.val, 0, target.val, 0, columns, column.val, rows] ++ suffix normalized normalizeScalar)) := by
      simpa only [copier, copyEntry, copyExit, List.length_cons, List.length_nil,
        Nat.reduceAdd, List.cons_append, List.nil_append] using copied
    have thirdHalt (symbol : Symbol) : third (.inr (.inr (0, 8))) symbol = none := by
      simp [third, resetter, Tape.sequence, HeaderResetMachine.halt]
    have fourthTrace := Tape.sequence_steps copyEntry thirdTrace thirdHalt copied'
    obtain ⟨finalScalar, clearTicks, clearCost, cleared, _, _⟩ :=
      clearRuns rows columns normalized target column normalizeScalar right
    have fourthHalt (symbol : Symbol) : fourth (.inr copyExit) symbol = none := by
      simp [fourth, copier, copyExit, Tape.sequence, SizeMachine.Copy.machine, UnaryMachine.machine]
    simp only [List.append_assoc] at cleared
    have computation := Tape.sequence_steps clearEntry fourthTrace fourthHalt cleared
    have exchangeBounded : exchangeTicks ≤ exchangeBound.eval (assignment rows columns) := by
      apply exchangeCost.trans
      have targetBound := target.isLt
      have sourceBound := source.isLt
      simp only [exchangeBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_add, SizePolynomial.eval_parameter, assignment]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have resetBounded : 4 * source.val + 2 ≤ resetBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      simp [resetBound, assignment]
    have copyBounded : copyTicks ≤ copyBound.eval (assignment rows columns) := by
      apply copyCost.trans
      have targetBound := target.isLt
      have columnBound := column.isLt
      simp only [copyBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_add, SizePolynomial.eval_parameter, assignment]
      apply Nat.mul_le_mul_left 64
      apply Nat.pow_le_pow_left
      simp [UnaryMachine.fields]; omega
    refine ⟨finalScalar, swapTicks + (exchangeTicks + 1) + (normalizeTicks + 1) +
      (4 * source.val + 2 + 1) + (copyTicks + 1) + (clearTicks + 1), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, third, fourth, exchanger, exchangeEntry, resetter,
        resetEntry, copier, copyEntry, suffix, swapped, normalized, matrixWidth,
        MatrixOperations.pivotStep, Tape.configuration, List.append_assoc] using computation
    · exact MatrixOperations.pivotStep_rowEquivalent matrix target source column nonzero
    · exact MatrixOperations.pivotStep_pivot matrix target source column nonzero
    · intro row different
      exact MatrixOperations.pivotStep_zero matrix target source row column nonzero different

/-- Restore the four-counter column frame and advance the pivot row after a successful step. -/
theorem realizes_restored (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (target source : Fin rows) (_ordered : target.val ≤ source.val)
          (column : Fin columns) (_nonzero : matrix source column ≠ 0)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.pivotStep matrix target source column
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [target.val, source.val, 0, columns, column.val, rows] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [target.val + 1, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated ∧ updated target column = 1 ∧
            (∀ row : Fin rows, row ≠ target → updated row column = 0) := by
  classical
  obtain ⟨PivotState, pivotFinite, pivotInhabited, pivotEntry, pivotExit, pivotMachine,
    pivotBound, pivotHalt, pivotRuns⟩ := realizes field
  let pivotControllerFinite : Fintype PivotState := pivotFinite
  let pivotControllerInhabited : Inhabited PivotState := pivotInhabited
  obtain ⟨MoveState, moveFinite, moveInhabited, moveEntry, moveExit, mover,
    moveHalt, moveRuns⟩ := NamedHeader.realizes sourceLayout relocation (by decide)
  let moveControllerFinite : Fintype MoveState := moveFinite
  let moveControllerInhabited : Inhabited MoveState := moveInhabited
  obtain ⟨RemoveState, removeFinite, removeInhabited, removeEntry, removeExit, remover,
    removeHalt, removeRuns⟩ := HeaderMoves.realizes_remove_front 3
  let removeControllerFinite : Fintype RemoveState := removeFinite
  let removeControllerInhabited : Inhabited RemoveState := removeInhabited
  let first := Tape.sequence pivotMachine mover moveEntry
  let second := Tape.sequence first remover removeEntry
  let incrementer := HeaderIncrementMachine.machine 0
  let incrementEntry : HeaderIncrementMachine.State 0 := .inl (Fin.last 0)
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 8
  let moveBound := SizePolynomial.constant 7 * (SizePolynomial.constant 128 * headerBound ^ 2 + 1)
  let removeBound := SizePolynomial.constant 3 * (SizePolynomial.constant 4 * headerBound + SizePolynomial.constant 8)
  refine ⟨Sum (Sum (Sum PivotState MoveState) RemoveState) (HeaderIncrementMachine.State 0),
    inferInstance, inferInstance, .inl (.inl (.inl pivotEntry)), .inr (.inr (0, 2)),
    Tape.sequence second incrementer incrementEntry,
    pivotBound + moveBound + removeBound + SizePolynomial.constant 5, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, incrementer, HeaderIncrementMachine.halt]
  · intro rows columns matrix target source ordered column nonzero initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let updated := MatrixOperations.pivotStep matrix target source column
    obtain ⟨finalScalar, pivotTicks, pivotCost, pivotTrace, equivalent, normalized, cleared⟩ :=
      pivotRuns rows columns matrix target source ordered column nonzero initialScalar right
    let outputSuffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 ::
        (word (List.ofFn (fun index : Fin matrixWidth =>
          (encode field rows columns updated).getLsbD index.val)) ++ right))
    let headerValues : HeaderField → ℕ
      | .savedPivotRow => target.val
      | .targetRow => rows
      | .rowLimit => rows
      | .zeroColumn => 0
      | .columnCount => columns
      | .pivotColumn => column.val
      | .pivotRow => target.val
    obtain ⟨moveTicks, moveCost, moved⟩ := moveRuns headerValues outputSuffix
    change moveTicks ≤ 7 * (128 * ((UnaryMachine.fields [target.val, rows, rows, 0, columns, column.val, target.val]).length + 1) ^ 2 + 1) at moveCost
    have moved' : Tape.Steps mover moveTicks
        (Tape.configuration moveEntry []
          (UnaryMachine.fields [target.val, rows, rows, 0, columns, column.val, target.val] ++ outputSuffix))
        (Tape.configuration moveExit []
          (UnaryMachine.fields [rows, 0, target.val, target.val, rows, column.val, columns] ++ outputSuffix)) := by
      simpa [sourceLayout, targetLayout, relocation, headerValues, NamedHeader.result, NamedHeader.move] using moved
    obtain ⟨removeTicks, removeCost, removed⟩ := removeRuns
      [rows, 0, target.val, target.val, rows, column.val, columns] (by simp) outputSuffix
    have removed' : Tape.Steps remover removeTicks
        (Tape.configuration removeEntry []
          (UnaryMachine.fields [rows, 0, target.val, target.val, rows, column.val, columns] ++ outputSuffix))
        (Tape.configuration removeExit []
          (UnaryMachine.fields [target.val, rows, column.val, columns] ++ outputSuffix)) := by
      simpa only [List.drop_succ_cons, List.drop_zero] using removed
    have incremented := HeaderIncrementMachine.realizes [] target.val
      (UnaryMachine.fields [rows, column.val, columns] ++ outputSuffix)
    have incremented' : Tape.Steps incrementer 2
        (Tape.configuration incrementEntry []
          (UnaryMachine.fields [target.val, rows, column.val, columns] ++ outputSuffix))
        (Tape.configuration (.inr (0, 2)) []
          (UnaryMachine.fields [target.val + 1, rows, column.val, columns] ++ outputSuffix)) := by
      simpa [incrementer, incrementEntry, UnaryMachine.fields, List.append_assoc] using incremented
    simp only [List.append_assoc] at pivotTrace
    have firstTrace := Tape.sequence_steps moveEntry pivotTrace pivotHalt moved'
    have firstHalt (symbol : Symbol) : first (.inr moveExit) symbol = none := by
      simp [first, Tape.sequence, moveHalt]
    have secondTrace := Tape.sequence_steps removeEntry firstTrace firstHalt removed'
    have secondHalt (symbol : Symbol) : second (.inr removeExit) symbol = none := by
      simp [second, Tape.sequence, removeHalt]
    have computation := Tape.sequence_steps incrementEntry secondTrace secondHalt incremented'
    have headerCost : (UnaryMachine.fields [target.val, rows, rows, 0, columns, column.val, target.val]).length + 1 ≤
        headerBound.eval (assignment rows columns) := by
      have targetBound := target.isLt
      have columnBound := column.isLt
      simp [headerBound, assignment]; omega
    have moveBounded : moveTicks ≤ moveBound.eval (assignment rows columns) := by
      have dominated := Nat.mul_le_mul_left 7 (Nat.add_le_add_right
        (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left headerCost 2)) 1)
      simp only [moveBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one]
      simpa only [List.length_cons, List.length_nil] using moveCost.trans dominated
    have removeBounded : removeTicks ≤ removeBound.eval (assignment rows columns) := by
      have permuted : (UnaryMachine.fields [rows, 0, target.val, target.val, rows, column.val, columns]).length =
          (UnaryMachine.fields [target.val, rows, rows, 0, columns, column.val, target.val]).length := by
        simp [UnaryMachine.fields]; omega
      rw [permuted] at removeCost
      simp only [removeBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_add]
      omega
    refine ⟨finalScalar, pivotTicks + (moveTicks + 1) + (removeTicks + 1) + (2 + 1), ?_, ?_, equivalent, normalized, cleared⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, incrementer, incrementEntry, outputSuffix, updated, matrixWidth,
        Tape.configuration, List.append_assoc] using computation

end PivotStep

end Polytime.Examples.MatrixPivotStep
