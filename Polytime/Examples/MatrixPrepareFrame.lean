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

import Polytime.Examples.Matrices
import Polytime.SizeEvaluation
import Polytime.HeaderMoves
import Polytime.HeaderInsertMachine

/-! # Preparing the complete matrix elimination frame

Read the unary dimension header, compute the dense matrix capacity, discard
arithmetic temporaries, and format the traversal counters and scalar window.
The payload is an arbitrary preserved suffix throughout preparation.
-/

namespace Polytime.Examples.MatrixPrepareFrame

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite domain.
universe scalarLevel

noncomputable section Preparation

/-- Prepare the elimination frame from just the runtime dimensions and payload.
The initial scalar is fixed when the machine is compiled; no scratch is supplied. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) (initialScalar : field.Carrier) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (tail : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry [] (UnaryMachine.fields [rows, columns] ++ tail))
            (Tape.configuration exit []
              (UnaryMachine.fields [0, rows, 0, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: tail))) := by
  classical
  let row : SizeExpression Matrices.context := .parameter .K
  let column : SizeExpression Matrices.context := .parameter .L
  let area := row * column
  let width : SizeExpression Matrices.context := .constant field.bitWidth
  have arithmetic : SizeEvaluation.Realizes [row, column]
      [.constant 0, .constant 0, width * area, width, area, row, column] :=
    (SizeEvaluation.Realizes.mul row column []).trans
      ((SizeEvaluation.Realizes.constant field.bitWidth [area, row, column]).trans
        ((SizeEvaluation.Realizes.mul width area [row, column]).trans
          ((SizeEvaluation.Realizes.constant 0 [width * area, width, area, row, column]).trans
            (SizeEvaluation.Realizes.constant 0 [.constant 0, width * area, width, area, row, column]))))
  obtain ⟨ArithmeticState, arithmeticFinite, arithmeticInhabited, arithmeticEntry, arithmeticExit,
    calculator, arithmeticBound, arithmeticHalt, arithmeticRuns⟩ := arithmetic
  let arithmeticControllerFinite : Fintype ArithmeticState := arithmeticFinite
  let arithmeticControllerInhabited : Inhabited ArithmeticState := arithmeticInhabited
  obtain ⟨MoveState, moveFinite, moveInhabited, moveEntry, moveExit, mover,
    moveHalt, moveRuns⟩ := HeaderMoves.realizes [2, 6, 3, 6, 4, 6, 6]
  let moveControllerFinite : Fintype MoveState := moveFinite
  let moveControllerInhabited : Inhabited MoveState := moveInhabited
  obtain ⟨RemoveState, removeFinite, removeInhabited, removeEntry, removeExit, remover,
    removeHalt, removeRuns⟩ := HeaderMoves.realizes_remove_front 2
  let removeControllerFinite : Fintype RemoveState := removeFinite
  let removeControllerInhabited : Inhabited RemoveState := removeInhabited
  let delimiter := HeaderInsertMachine.CounterDelimiter.machine 4
  let delimiterEntry : HeaderInsertMachine.State 4 := .inl (Fin.last 4)
  let delimiterExit : HeaderInsertMachine.State 4 := .inr (0, 2)
  let inserted := word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++ [3]
  obtain ⟨InsertState, insertFinite, insertInhabited, insertEntry, insertExit, inserter,
    insertHalt, insertRuns⟩ := HeaderInsertMachine.realizes_word 4 inserted
  let insertControllerFinite : Fintype InsertState := insertFinite
  let insertControllerInhabited : Inhabited InsertState := insertInhabited
  let first := Tape.sequence calculator mover moveEntry
  let second := Tape.sequence first remover removeEntry
  let third := Tape.sequence second delimiter delimiterEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant (field.bitWidth + 1) * SizePolynomial.parameter (ctx := Matrices.context) .K *
      SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.parameter (ctx := Matrices.context) .K +
        SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant (field.bitWidth + 8)
  let moveBound := SizePolynomial.constant 7 * (SizePolynomial.constant 128 * headerBound ^ 2 + 1)
  let removeBound := SizePolynomial.constant 2 * (SizePolynomial.constant 4 * headerBound + SizePolynomial.constant 8)
  let delimiterBound := SizePolynomial.constant 2 * headerBound + SizePolynomial.constant 3
  let insertBound := SizePolynomial.constant (field.bitWidth + 1) *
    (SizePolynomial.constant 3 * headerBound + SizePolynomial.constant 3)
  refine ⟨Sum (Sum (Sum (Sum ArithmeticState MoveState) RemoveState) (HeaderInsertMachine.State 4)) InsertState,
    inferInstance, inferInstance, .inl (.inl (.inl (.inl arithmeticEntry))), .inr insertExit,
    Tape.sequence third inserter insertEntry,
    arithmeticBound + moveBound + removeBound + delimiterBound + insertBound + SizePolynomial.constant 4, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, insertHalt]
  · intro rows columns tail
    dsimp only
    let matrixWidth := rows * columns * field.bitWidth
    obtain ⟨arithmeticTicks, arithmeticCost, calculated⟩ := arithmeticRuns (assignment rows columns) tail
    have calculated' : Tape.Steps calculator arithmeticTicks
        (Tape.configuration arithmeticEntry [] (UnaryMachine.fields [rows, columns] ++ tail))
        (Tape.configuration arithmeticExit []
          (UnaryMachine.fields [0, 0, matrixWidth, field.bitWidth, rows * columns, rows, columns] ++ tail)) := by
      simpa [row, column, area, width, SizeExpression.eval, assignment, matrixWidth,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using calculated
    obtain ⟨moveTicks, moveCost, moved⟩ := moveRuns
      [0, 0, matrixWidth, field.bitWidth, rows * columns, rows, columns] (by simp) tail
    have moved' : Tape.Steps mover moveTicks
        (Tape.configuration moveEntry []
          (UnaryMachine.fields [0, 0, matrixWidth, field.bitWidth, rows * columns, rows, columns] ++ tail))
        (Tape.configuration moveExit []
          (UnaryMachine.fields [field.bitWidth, rows * columns, 0, rows, 0, columns, matrixWidth] ++ tail)) := by
      simpa [HeaderMoves.applyMoves, HeaderMoves.moveToFront, List.getD] using moved
    obtain ⟨removeTicks, removeCost, removed⟩ := removeRuns
      [field.bitWidth, rows * columns, 0, rows, 0, columns, matrixWidth] (by simp) tail
    have removed' : Tape.Steps remover removeTicks
        (Tape.configuration removeEntry []
          (UnaryMachine.fields [field.bitWidth, rows * columns, 0, rows, 0, columns, matrixWidth] ++ tail))
        (Tape.configuration removeExit []
          (UnaryMachine.fields [0, rows, 0, columns, matrixWidth] ++ tail)) := by
      simpa only [List.drop_succ_cons, List.drop_zero] using removed
    have formatted := HeaderInsertMachine.CounterDelimiter.realizes [0, rows, 0, columns] matrixWidth tail
    have formatted' : Tape.Steps delimiter (2 * ((UnaryMachine.fields [0, rows, 0, columns]).length + matrixWidth) + 3)
        (Tape.configuration delimiterEntry [] (UnaryMachine.fields [0, rows, 0, columns, matrixWidth] ++ tail))
        (Tape.configuration delimiterExit []
          (UnaryMachine.fields [0, rows, 0, columns] ++ UnaryMachine.units matrixWidth ++ 4 :: tail)) := by
      simpa [delimiter, delimiterEntry, delimiterExit, UnaryMachine.fields, List.append_assoc] using formatted
    obtain ⟨insertTicks, insertCost, insertedTrace⟩ := insertRuns [0, rows, 0, columns] rfl
      (UnaryMachine.units matrixWidth ++ 4 :: tail)
    have firstTrace := Tape.sequence_steps moveEntry calculated' arithmeticHalt moved'
    have firstHalt (symbol : Symbol) : first (.inr moveExit) symbol = none := by
      simp [first, Tape.sequence, moveHalt]
    have secondTrace := Tape.sequence_steps removeEntry firstTrace firstHalt removed'
    have secondHalt (symbol : Symbol) : second (.inr removeExit) symbol = none := by
      simp [second, Tape.sequence, removeHalt]
    simp only [List.append_assoc] at formatted'
    have thirdTrace := Tape.sequence_steps delimiterEntry secondTrace secondHalt formatted'
    have thirdHalt (symbol : Symbol) : third (.inr delimiterExit) symbol = none := by
      simp [third, delimiter, delimiterExit, Tape.sequence, HeaderInsertMachine.CounterDelimiter.halt]
    simp only [List.append_assoc] at insertedTrace
    have computation := Tape.sequence_steps insertEntry thirdTrace thirdHalt insertedTrace
    have headerValue : headerBound.eval (assignment rows columns) =
        matrixWidth + rows * columns + rows + columns + field.bitWidth + 8 := by
      simp [headerBound, assignment, matrixWidth]; ring
    have moveBounded : moveTicks ≤ moveBound.eval (assignment rows columns) := by
      apply moveCost.trans
      simp only [moveBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one, headerValue]
      simp [UnaryMachine.fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      apply Nat.pow_le_pow_left
      omega
    have removeBounded : removeTicks ≤ removeBound.eval (assignment rows columns) := by
      simp only [removeBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, headerValue]
      simp [UnaryMachine.fields] at removeCost
      omega
    have delimiterBounded : 2 * ((UnaryMachine.fields [0, rows, 0, columns]).length + matrixWidth) + 3 ≤
        delimiterBound.eval (assignment rows columns) := by
      simp only [delimiterBound, SizePolynomial.eval_add, SizePolynomial.eval_mul,
        SizePolynomial.eval_constant, headerValue]
      simp [UnaryMachine.fields]; omega
    have insertBounded : insertTicks ≤ insertBound.eval (assignment rows columns) := by
      have insertedLength : inserted.length = field.bitWidth + 1 := by simp [inserted, word]
      rw [insertedLength] at insertCost
      apply insertCost.trans
      simp only [insertBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, headerValue]
      apply Nat.mul_le_mul_left
      simp [UnaryMachine.fields]; omega
    refine ⟨arithmeticTicks + (moveTicks + 1) + (removeTicks + 1) +
      (2 * ((UnaryMachine.fields [0, rows, 0, columns]).length + matrixWidth) + 3 + 1) + (insertTicks + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, third, delimiter, delimiterEntry, inserted, matrixWidth,
        exact_width, UnaryMachine.units, data, Bool.true_eq, ↓reduceIte, List.append_assoc, List.singleton_append,
        Tape.configuration] using computation

end Preparation

end Polytime.Examples.MatrixPrepareFrame
