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

import Polytime.Examples.MatrixPivotSearch
import Polytime.Examples.MatrixPivotDispatch
import Polytime.NamedHeader

/-! # A complete Gauss–Jordan column step on tape

Save the next pivot-row counter, search for the first eligible pivot, and
dispatch to elimination or the no-pivot branch. Both outcomes restore the
four-counter frame, ready for column advancement.
-/

namespace Polytime.Examples.MatrixColumnStep

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

/-- Compile-time identities of the counters used during pivot search. -/
inductive HeaderField
  | candidate | savedRow | rowCount | column | columnCount
  deriving DecidableEq

def searchLayout : List HeaderField := [.candidate, .savedRow, .rowCount, .column, .columnCount]

def preparedLayout : List HeaderField := [.candidate, .rowCount, .column, .columnCount, .savedRow]

/-- Moving the desired fields to the front in reverse order builds the target layout. -/
def prepareMoves : List HeaderField := preparedLayout.reverse

noncomputable section ColumnStep

/-- Search and process one runtime column, agreeing exactly with `columnStep`.
The row-count sentinel and zero-row matrices are included. -/
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
          let updated := GaussJordan.columnStep matrix start column
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated.1).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [start, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [updated.2, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated.1 ∧ start ≤ updated.2 ∧ updated.2 ≤ rows := by
  classical
  obtain ⟨SearchState, searchFinite, searchInhabited, searchEntry, searchExit, search,
    searchBound, searchHalt, searchRuns⟩ := MatrixPivotSearch.realizes_with_counters field 1
      (SizePolynomial.parameter (ctx := Matrices.context) .K + 1)
  let searchControllerFinite : Fintype SearchState := searchFinite
  let searchControllerInhabited : Inhabited SearchState := searchInhabited
  obtain ⟨DispatchState, dispatchFinite, dispatchInhabited, dispatchEntry, dispatchExit, dispatcher,
    dispatchBound, dispatchHalt, dispatchRuns⟩ := MatrixPivotDispatch.realizes field
  let dispatchControllerFinite : Fintype DispatchState := dispatchFinite
  let dispatchControllerInhabited : Inhabited DispatchState := dispatchInhabited
  obtain ⟨PrepareState, prepareFinite, prepareInhabited, prepareEntry, prepareExit, prepare,
    prepareHalt, prepareRuns⟩ := NamedHeader.realizes searchLayout prepareMoves (by decide)
  let prepareControllerFinite : Fintype PrepareState := prepareFinite
  let prepareControllerInhabited : Inhabited PrepareState := prepareInhabited
  let copier := SizeMachine.Copy.machine 0
  let copyEntry : SizeMachine.Copy.State 0 := (Fin.last 0, 0)
  let copyExit : SizeMachine.Copy.State 0 := (0, 19)
  let first := Tape.sequence copier prepare prepareEntry
  let second := Tape.sequence first search searchEntry
  let copyBound : SizePolynomial Matrices.context := SizePolynomial.constant 64 *
    (SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 5) ^ 2
  let prepareBound : SizePolynomial Matrices.context := SizePolynomial.constant 5 *
    (SizePolynomial.constant 128 *
      (SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K +
        SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 6) ^ 2 + 1)
  refine ⟨Sum (Sum (Sum (SizeMachine.Copy.State 0) PrepareState) SearchState) DispatchState,
    inferInstance, inferInstance, .inl (.inl (.inl copyEntry)), .inr dispatchExit,
    Tape.sequence second dispatcher dispatchEntry,
    copyBound + prepareBound + searchBound + dispatchBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, dispatchHalt]
  · intro rows columns matrix start bounded column initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    obtain ⟨copyTicks, copyCost, copied⟩ := SizeMachine.Copy.realizes []
      [rows, column.val, columns] start (suffix matrix initialScalar)
    have copied' : Tape.Steps copier copyTicks
        (Tape.configuration copyEntry []
          (UnaryMachine.fields [start, rows, column.val, columns] ++ suffix matrix initialScalar))
        (Tape.configuration copyExit []
          (UnaryMachine.fields [start, start, rows, column.val, columns] ++ suffix matrix initialScalar)) := by
      simpa only [copier, copyEntry, copyExit, List.length_nil, List.nil_append, List.cons_append] using copied
    let headerValues : HeaderField → ℕ
      | .candidate | .savedRow => start
      | .rowCount => rows
      | .column => column.val
      | .columnCount => columns
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := prepareRuns headerValues (suffix matrix initialScalar)
    change prepareTicks ≤ 5 * (128 * ((UnaryMachine.fields [start, start, rows, column.val, columns]).length + 1) ^ 2 + 1)
      at prepareCost
    have prepared' : Tape.Steps prepare prepareTicks
        (Tape.configuration prepareEntry []
          (UnaryMachine.fields [start, start, rows, column.val, columns] ++ suffix matrix initialScalar))
        (Tape.configuration prepareExit []
          (UnaryMachine.fields [start, rows, column.val, columns, start] ++ suffix matrix initialScalar)) := by
      simpa [searchLayout, preparedLayout, prepareMoves, headerValues, NamedHeader.result, NamedHeader.move] using prepared
    have copyHalt (symbol : Symbol) : copier copyExit symbol = none := by
      simp [copier, copyExit, SizeMachine.Copy.machine, UnaryMachine.machine]
    have firstTrace := Tape.sequence_steps prepareEntry copied' copyHalt prepared'
    obtain ⟨candidate, searchScalar, searchTicks, searchCost, searched, lower, upper, _, nonzero, found⟩ :=
      searchRuns rows columns matrix start bounded column [start] rfl
        (by simpa [assignment] using bounded) initialScalar right
    simp only [List.cons_append, List.nil_append, List.append_assoc] at searched
    have firstHalt (symbol : Symbol) : first (.inr prepareExit) symbol = none := by
      simp [first, Tape.sequence, prepareHalt]
    have secondTrace := Tape.sequence_steps searchEntry firstTrace firstHalt searched
    obtain ⟨finalScalar, dispatchTicks, dispatchCost, dispatched⟩ :=
      dispatchRuns rows columns matrix start candidate lower upper column nonzero searchScalar right
    have agreement :
        (if valid : candidate < rows then
          MatrixOperations.pivotStep matrix ⟨start, lt_of_le_of_lt lower valid⟩ ⟨candidate, valid⟩ column
          else matrix, if candidate < rows then start + 1 else start) = GaussJordan.columnStep matrix start column := by
      by_cases active : candidate < rows
      · have startValid : start < rows := lt_of_le_of_lt lower active
        simp [GaussJordan.columnStep, startValid, found, active]
      · by_cases startValid : start < rows
        · simp [GaussJordan.columnStep, startValid, found, active]
        · simp [GaussJordan.columnStep, startValid, active]
    have matrixAgreement := congrArg Prod.fst agreement
    have rowAgreement := congrArg Prod.snd agreement
    dsimp only [Prod.fst, Prod.snd] at matrixAgreement rowAgreement
    rw [matrixAgreement, rowAgreement] at dispatched
    simp only [List.append_assoc] at dispatched
    have secondHalt (symbol : Symbol) : second (.inr searchExit) symbol = none := by
      simp [second, Tape.sequence, searchHalt]
    have computation := Tape.sequence_steps dispatchEntry secondTrace secondHalt dispatched
    have copyBounded : copyTicks ≤ copyBound.eval (assignment rows columns) := by
      apply copyCost.trans
      have columnBound := column.isLt
      simp only [copyBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_add, SizePolynomial.eval_parameter, assignment]
      apply Nat.mul_le_mul_left 64
      apply Nat.pow_le_pow_left
      simp [UnaryMachine.fields]; omega
    have prepareBounded : prepareTicks ≤ prepareBound.eval (assignment rows columns) := by
      apply prepareCost.trans
      have columnBound := column.isLt
      simp only [prepareBound, SizePolynomial.eval_mul,
        SizePolynomial.eval_constant, SizePolynomial.eval_add, SizePolynomial.eval_pow, SizePolynomial.eval_one,
        SizePolynomial.eval_parameter, assignment]
      apply Nat.mul_le_mul_left 5
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left 128
      apply Nat.pow_le_pow_left
      simp [UnaryMachine.fields]; omega
    refine ⟨finalScalar, copyTicks + (prepareTicks + 1) + (searchTicks + 1) + (dispatchTicks + 1), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, copier, copyEntry, suffix, matrixWidth,
        Tape.configuration, List.append_assoc] using computation
    · exact GaussJordan.columnStep_rowEquivalent matrix start column
    · exact (GaussJordan.columnStep_row_bound matrix start column bounded).1
    · exact (GaussJordan.columnStep_row_bound matrix start column bounded).2

end ColumnStep

end Polytime.Examples.MatrixColumnStep
