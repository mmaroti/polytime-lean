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
import Polytime.Examples.MatrixClearRange

/-! # Complete runtime column clearing

Two disjoint row intervals clear every row except the pivot. A saved row count
survives the first traversal and becomes the second traversal's loop limit.
-/

namespace Polytime.Examples.MatrixClearColumn

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

/-- Names distinguish header roles even when their counter values coincide. -/
inductive HeaderField
  | pivotRow | targetRow | rowLimit | zeroColumn | columnCount | pivotColumn | savedRowCount
  deriving DecidableEq

def sourceLayout : List HeaderField := [.pivotRow, .targetRow, .rowLimit, .zeroColumn, .columnCount, .pivotColumn, .savedRowCount]

def targetLayout : List HeaderField := [.pivotRow, .targetRow, .savedRowCount, .zeroColumn, .columnCount, .pivotColumn, .rowLimit]

def relocation : List HeaderField := targetLayout.reverse

noncomputable section ColumnClearing

/-- Clear all nonpivot rows, agreeing exactly with the mathematical column operation.
The pivot row is preserved, including when either traversal is empty. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source : Fin rows) (column : Fin columns) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.clearColumn matrix source column
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, 0, source.val, 0, columns, column.val, rows] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, rows, rows, 0, columns, column.val, source.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated ∧
            (matrix source column = 1 → ∀ row : Fin rows, row ≠ source → updated row column = 0) := by
  classical
  obtain ⟨RangeState, rangeFinite, rangeInhabited, rangeEntry, rangeExit, rangeMachine,
    rangeBound, rangeHalt, rangeRuns⟩ := MatrixClearRange.realizes_with_counters field 1
      (SizePolynomial.parameter (ctx := Matrices.context) .K + 1)
  let rangeControllerFinite : Fintype RangeState := rangeFinite
  let rangeControllerInhabited : Inhabited RangeState := rangeInhabited
  obtain ⟨MoveState, moveFinite, moveInhabited, moveEntry, moveExit, mover,
    moveHalt, moveRuns⟩ := NamedHeader.realizes sourceLayout relocation (by decide)
  let moveControllerFinite : Fintype MoveState := moveFinite
  let moveControllerInhabited : Inhabited MoveState := moveInhabited
  let incrementer := HeaderIncrementMachine.machine 1
  let incrementEntry : HeaderIncrementMachine.State 1 := .inl (Fin.last 1)
  let first := Tape.sequence rangeMachine mover moveEntry
  let second := Tape.sequence first incrementer incrementEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 8
  let moveBound := SizePolynomial.constant 7 * (SizePolynomial.constant 128 * headerBound ^ 2 + 1)
  let incrementBound := SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  refine ⟨Sum (Sum (Sum RangeState MoveState) (HeaderIncrementMachine.State 1)) RangeState,
    inferInstance, inferInstance, .inl (.inl (.inl rangeEntry)), .inr rangeExit,
    Tape.sequence second rangeMachine rangeEntry,
    SizePolynomial.constant 2 * rangeBound + moveBound + incrementBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, rangeHalt]
  · intro rows columns matrix source column initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    let lower : Matrix (Fin rows) (Fin columns) field.Carrier := fun row index =>
      if 0 ≤ row.val ∧ row.val < source.val then
        matrix row index + -matrix row column * matrix source index else matrix row index
    let upper : Matrix (Fin rows) (Fin columns) field.Carrier := fun row index =>
      if source.val + 1 ≤ row.val ∧ row.val < rows then
        lower row index + -lower row column * lower source index else lower row index
    have combined : upper = MatrixOperations.clearColumn matrix source column := by
      funext row index
      by_cases below : row.val < source.val
      · have distinct : row ≠ source := by intro equal; subst row; omega
        have notAbove : ¬(source.val + 1 ≤ row.val ∧ row.val < rows) := by omega
        simp only [upper, notAbove, ↓reduceIte, lower, Nat.zero_le, true_and, below,
          ↓reduceIte, MatrixOperations.clearColumn, MatrixOperations.addPivotRow, ite_eq_right distinct]
      · by_cases same : row = source
        · subst row
          simp [upper, lower, MatrixOperations.clearColumn, MatrixOperations.addPivotRow]
        · have above : source.val + 1 ≤ row.val := by
            have different : row.val ≠ source.val := by intro equal; exact same (Fin.ext equal)
            omega
          simp only [upper, above, row.isLt, and_self, ↓reduceIte, lower, Nat.zero_le,
            true_and, below, lt_self_iff_false, ↓reduceIte, MatrixOperations.clearColumn,
            MatrixOperations.addPivotRow, ite_eq_right same]
    obtain ⟨lowerScalar, lowerTicks, lowerCost, lowerTrace, lowerEquivalent, _⟩ :=
      rangeRuns rows columns matrix source 0 source.val (Nat.zero_le _) (Nat.le_of_lt source.isLt)
        (Or.inl le_rfl) column [rows] rfl (by simp [assignment]) initialScalar right
    have lowerTrace' : Tape.Steps rangeMachine lowerTicks
        (Tape.configuration rangeEntry []
          (UnaryMachine.fields [source.val, 0, source.val, 0, columns, column.val, rows] ++ suffix matrix initialScalar))
        (Tape.configuration rangeExit []
          (UnaryMachine.fields [source.val, source.val, source.val, 0, columns, column.val, rows] ++ suffix lower lowerScalar)) := by
      simpa only [lower, suffix, matrixWidth, List.cons_append, List.nil_append, List.append_assoc] using lowerTrace
    let headerValues : HeaderField → ℕ
      | .pivotRow => source.val
      | .targetRow => source.val
      | .rowLimit => source.val
      | .zeroColumn => 0
      | .columnCount => columns
      | .pivotColumn => column.val
      | .savedRowCount => rows
    obtain ⟨moveTicks, moveCost, moved⟩ := moveRuns headerValues (suffix lower lowerScalar)
    change moveTicks ≤ 7 * (128 * ((UnaryMachine.fields [source.val, source.val, source.val, 0, columns, column.val, rows]).length + 1) ^ 2 + 1) at moveCost
    have moved' : Tape.Steps mover moveTicks
        (Tape.configuration moveEntry []
          (UnaryMachine.fields [source.val, source.val, source.val, 0, columns, column.val, rows] ++ suffix lower lowerScalar))
        (Tape.configuration moveExit []
          (UnaryMachine.fields [source.val, source.val, rows, 0, columns, column.val, source.val] ++ suffix lower lowerScalar)) := by
      simpa [sourceLayout, targetLayout, relocation, headerValues, NamedHeader.result, NamedHeader.move] using moved
    have incremented := HeaderIncrementMachine.realizes [source.val] source.val
      (UnaryMachine.fields [rows, 0, columns, column.val, source.val] ++ suffix lower lowerScalar)
    have incremented' : Tape.Steps incrementer (3 * (source.val + 1) + 2)
        (Tape.configuration incrementEntry []
          (UnaryMachine.fields [source.val, source.val, rows, 0, columns, column.val, source.val] ++ suffix lower lowerScalar))
        (Tape.configuration (.inr (0, 2)) []
          (UnaryMachine.fields [source.val, source.val + 1, rows, 0, columns, column.val, source.val] ++ suffix lower lowerScalar)) := by
      simpa [incrementer, incrementEntry, UnaryMachine.fields, List.append_assoc] using incremented
    obtain ⟨finalScalar, upperTicks, upperCost, upperTrace, upperEquivalent, _⟩ :=
      rangeRuns rows columns lower source (source.val + 1) rows source.isLt le_rfl
        (Or.inr (by omega)) column [source.val] rfl (by simp [assignment]) lowerScalar right
    have upperTrace' : Tape.Steps rangeMachine upperTicks
        (Tape.configuration rangeEntry []
          (UnaryMachine.fields [source.val, source.val + 1, rows, 0, columns, column.val, source.val] ++ suffix lower lowerScalar))
        (Tape.configuration rangeExit []
          (UnaryMachine.fields [source.val, rows, rows, 0, columns, column.val, source.val] ++ suffix upper finalScalar)) := by
      simpa only [upper, suffix, matrixWidth, List.cons_append, List.nil_append, List.append_assoc] using upperTrace
    have firstTrace := Tape.sequence_steps moveEntry lowerTrace' rangeHalt moved'
    have firstHalt (symbol : Symbol) : first (.inr moveExit) symbol = none := by
      simp [first, Tape.sequence, moveHalt]
    have secondTrace := Tape.sequence_steps incrementEntry firstTrace firstHalt incremented'
    have secondHalt (symbol : Symbol) : second (.inr (.inr (0, 2))) symbol = none := by
      simp [second, Tape.sequence, incrementer, HeaderIncrementMachine.halt]
    have computation := Tape.sequence_steps rangeEntry secondTrace secondHalt upperTrace'
    have headerCost : (UnaryMachine.fields [source.val, source.val, source.val, 0, columns, column.val, rows]).length + 1 ≤
        headerBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have columnBound := column.isLt
      simp [headerBound, assignment]; omega
    have relocationCost : moveTicks ≤ moveBound.eval (assignment rows columns) := by
      have dominated := Nat.mul_le_mul_left 7 (Nat.add_le_add_right
        (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left headerCost 2)) 1)
      simp only [moveBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one]
      simpa only [List.length_cons, List.length_nil] using moveCost.trans dominated
    have advanceCost : 3 * (source.val + 1) + 2 ≤ incrementBound.eval (assignment rows columns) := by
      simp [incrementBound, assignment]
    refine ⟨finalScalar, lowerTicks + (moveTicks + 1) + (3 * (source.val + 1) + 2 + 1) +
      (upperTicks + 1), ?_, ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, incrementer, incrementEntry, suffix, matrixWidth, combined,
        Tape.configuration, List.append_assoc] using computation
    · have equivalent : Matrix.RowEquivalent matrix upper := lowerEquivalent.trans upperEquivalent
      rw [combined] at equivalent
      exact equivalent
    · intro normalized row distinct
      exact MatrixOperations.clearColumn_zero matrix source row column normalized distinct

end ColumnClearing

end Polytime.Examples.MatrixClearColumn
