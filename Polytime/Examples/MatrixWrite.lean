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

import Polytime.Examples.MatrixAccess
import Polytime.RetainedWriteMachine
import Polytime.HeaderIncrementMachine

/-! # Canonical matrix writes from runtime row and column counters -/

namespace Polytime.Examples.MatrixWrite

open Matrices TupleMachine

-- scalarLevel: the fixed carrier of matrix entries.
universe scalarLevel

noncomputable section RuntimeWrites

/-- Compute the address, read the runtime replacement, update one canonical
matrix entry, clear evaluation scratch, and restore the counter header. The
controller is fixed before dimensions, indices, and replacement values vary. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (column : Fin columns) (replacement : field.Carrier)
          (inputSymbol : Symbol) (right : List Symbol) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode replacement).getLsbD offset.val)
          let updated := Function.update matrix row (Function.update (matrix row) column replacement)
          let result := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨scratch, certificate⟩ := MatrixAddress.frame_realization field.bitWidth
  let input : List (SizeExpression MatrixAddress.context) :=
    [.parameter .rowIndex, .parameter .columnIndex, .parameter .columnCount]
  let parameters := scratch ++ input
  obtain ⟨WriteState, finite, inhabited, writeEntry, writeExit, writeMachine, arithmeticCost, writeHalt, writeRuns⟩ :=
    RetainedWriteMachine.realizes_computed_address input parameters (MatrixAddress.expression field.bitWidth)
      certificate (MatrixAccess.scalar_width_positive field)
  let _writeFinite : Fintype WriteState := finite
  let _writeInhabited : Inhabited WriteState := inhabited
  let dimensions : MatrixAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let storage : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((parameters.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant parameters.length
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  let headerBound : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K +
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 3
  refine ⟨Sum WriteState (HeaderReturnMachine.State 3), inferInstance, inferInstance,
    .inl writeEntry, .inr (0, 5),
    Tape.sequence writeMachine (HeaderReturnMachine.machine 3) (Fin.last 3, 0),
    MvPolynomial.rename dimensions arithmeticCost + SizePolynomial.constant 1024 * (capacity + storage + 1) ^ 2 + headerBound +
      SizePolynomial.constant 3 * (storage + capacity) + SizePolynomial.constant 10, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderReturnMachine.halt]
  · intro rows columns matrix row column replacement inputSymbol right inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let original := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
    let scalar := fun offset : Fin field.bitWidth => (field.codec.encode replacement).getLsbD offset.val
    let updated := Function.update matrix row (Function.update (matrix row) column replacement)
    let output := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns updated).getLsbD index.val)
    let start := (row.val * columns + column.val) * field.bitWidth
    let values := scratch.map (·.eval (MatrixAddress.assignment row.val column.val columns))
    let retained := UnaryMachine.fields values ++ UnaryMachine.fields [row.val, column.val, columns]
    have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
    have partition : payload.take start ++ List.ofFn original ++ payload.drop (start + field.bitWidth) = payload ∧
        (payload.take start).length = start ∧
        (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
      encode_entry_partition field rows columns matrix row column
    obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
    have retainedEquality : retained = UnaryMachine.fields
        (parameters.map (·.eval (MatrixAddress.assignment row.val column.val columns))) := by
      simp [retained, values, parameters, input, MatrixAddress.assignment]
    have retainedCost : retained.length ≤ storage.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((parameters.map SizeExpression.polynomial).sum)
        (MatrixAddress.assignment row.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have source : retained.length = ((parameters.map SizeExpression.polynomial).sum).eval
          (MatrixAddress.assignment row.val column.val columns) + parameters.length := by
        rw [retainedEquality]
        simp only [UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have target : storage.eval (assignment rows columns) = ((parameters.map SizeExpression.polynomial).sum).eval
          (fun name => assignment rows columns (dimensions name)) + parameters.length := by
        simp [storage, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [source, target]
      exact Nat.add_le_add_right monotone parameters.length
    have scratchCost : (UnaryMachine.fields values).length ≤ storage.eval (assignment rows columns) :=
      (by simp [retained] : (UnaryMachine.fields values).length ≤ retained.length).trans retainedCost
    have headerCost : (UnaryMachine.fields [row.val, column.val, columns]).length ≤ headerBound.eval (assignment rows columns) := by
      simp [headerBound, assignment]
      omega
    have capacityValue : capacity.eval (assignment rows columns) = matrixWidth := by
      simp [capacity, matrixWidth, exact_width, assignment]
    have addressCost : start ≤ capacity.eval (assignment rows columns) := by rw [capacityValue]; omega
    obtain ⟨writeTicks, writeCost, written⟩ := writeRuns (MatrixAddress.assignment row.val column.val columns) scalar original
      (payload.take start) (payload.drop (start + field.bitWidth)) [] right inputSymbol
      (by simpa only [start, MatrixAddress.expression, SizeExpression.eval_mul,
        SizeExpression.eval_add, SizeExpression.eval_constant, SizeExpression.eval_parameter,
        MatrixAddress.assignment] using beforeLength) inputValid
    simp only [List.append_nil] at writeCost written
    rw [physicalWidth] at writeCost written
    simp only [beforeLength] at written
    rw [← retainedEquality] at writeCost written
    have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word output := by
      rw [← word_append, ← word_append]
      simpa only [List.append_assoc] using congrArg word
        (encode_update_entry field rows columns matrix row column replacement).symm
    have updatedTrace : Tape.Steps writeMachine writeTicks
        (Tape.configuration writeEntry []
          (UnaryMachine.fields ([row.val, column.val, columns]) ++ word (List.ofFn scalar) ++
            3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
        (Tape.configuration writeExit (retained.reverse ++ 6 :: (List.replicate start 0 ++ [7]))
          (word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
      simpa only [input, List.map_cons, List.map_nil, SizeExpression.eval_parameter,
        MatrixAddress.assignment, UnaryMachine.fields_cons, UnaryMachine.fields_append,
        List.append_assoc, List.cons_append, decomposition, packed] using written
    have arithmeticBound : arithmeticCost.eval (MatrixAddress.assignment row.val column.val columns) ≤
        (MvPolynomial.rename dimensions arithmeticCost).eval (assignment rows columns) := by
      calc
        _ ≤ arithmeticCost.eval (fun name => assignment rows columns (dimensions name)) :=
          SizePolynomial.eval_mono arithmeticCost _ _ (by
            intro name; cases name <;> simp only [MatrixAddress.assignment, dimensions, assignment]
            · exact Nat.le_of_lt row.isLt
            · exact Nat.le_of_lt column.isLt
            · exact le_rfl)
        _ = _ := by
          simp only [SizePolynomial.eval, MvPolynomial.eval_rename, Function.comp_def]
    have result := HeaderReturnMachine.restore_blank (count := 3) [row.val, column.val, columns] values start
      (word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))
      rfl (by simp) writeHalt updatedTrace
    refine ⟨writeTicks + ((UnaryMachine.fields [row.val, column.val, columns]).length +
      3 * ((UnaryMachine.fields values).length + start) + 8 + 1), ?_, ?_⟩
    · have storageBound : 1024 * (matrixWidth + retained.length + 1) ^ 2 ≤
          1024 * (matrixWidth + storage.eval (assignment rows columns) + 1) ^ 2 :=
        Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left (by omega) 2)
      simp only [SizePolynomial.eval, map_add, map_mul, map_pow, map_one,
        SizePolynomial.constant, MvPolynomial.eval_C]
      simp only [SizePolynomial.eval] at arithmeticBound scratchCost headerCost addressCost storageBound capacityValue writeCost retainedCost
      rw [capacityValue] at *
      omega
    · simpa only [Tape.configuration, scalar, payload, output, updated, matrixWidth, List.append_assoc] using result

/-- Read, transform, and write one entry in a shared frame. Both addresses are
computed from runtime counters; the scalar operation is a fixed table. -/
theorem realizes_entry_map (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (column : Fin columns) (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let replacement := operation (matrix row column)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode replacement).getLsbD offset.val)
          let updated := Function.update matrix row (Function.update (matrix row) column replacement)
          let result := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨ReadState, readFinite, readInhabited, readEntry, readExit, readMachine,
    readBound, readHalt, readRuns⟩ := MatrixAccess.realizes_runtime_entry_restored field operation
  let readerFinite : Fintype ReadState := readFinite
  let readerInhabited : Inhabited ReadState := readInhabited
  obtain ⟨WriteState, writeFinite, writeInhabited, writeEntry, writeExit, writeMachine,
    writeBound, writeHalt, writeRuns⟩ := realizes field
  let writerFinite : Fintype WriteState := writeFinite
  let writerInhabited : Inhabited WriteState := writeInhabited
  refine ⟨Sum ReadState WriteState, inferInstance, inferInstance, .inl readEntry, .inr writeExit,
    Tape.sequence readMachine writeMachine writeEntry, readBound + writeBound + 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, writeHalt]
  · intro rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row column
      window inputSymbol right windowWidth windowValid inputValid
    obtain ⟨writeTicks, writeCost, written⟩ := writeRuns rows columns matrix row column
      (operation (matrix row column)) (data true) right (by decide)
    have result := Tape.sequence_steps writeEntry read readHalt written
    refine ⟨readTicks + (writeTicks + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_one]
      omega
    · simpa only [Tape.configuration] using result

/-- One column-loop body transforms an entry and advances its runtime column
counter. The terminal index may equal the column count; another body execution
requires a new proof that its index is in range. -/
theorem realizes_entry_map_next_column (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (column : Fin columns) (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let replacement := operation (matrix row column)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode replacement).getLsbD offset.val)
          let updated := Function.update matrix row (Function.update (matrix row) column replacement)
          let result := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, column.val + 1, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨MapState, finite, inhabited, mapEntry, mapExit, mapMachine,
    mapBound, mapHalt, mapRuns⟩ := realizes_entry_map field operation
  let mapperFinite : Fintype MapState := finite
  let mapperInhabited : Inhabited MapState := inhabited
  refine ⟨Sum MapState (HeaderIncrementMachine.State 1), inferInstance, inferInstance,
    .inl mapEntry, .inr (.inr (0, 2)),
    Tape.sequence mapMachine (HeaderIncrementMachine.machine 1) (.inl (Fin.last 1)),
    mapBound + SizePolynomial.constant 3 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderIncrementMachine.halt]
  · intro rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
    let updated := Function.update matrix row
      (Function.update (matrix row) column (operation (matrix row column)))
    let output := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns updated).getLsbD index.val)
    obtain ⟨mapTicks, mapCost, mapped⟩ := mapRuns rows columns matrix row column
      window inputSymbol right windowWidth windowValid inputValid
    have incremented := HeaderIncrementMachine.realizes [row.val] column.val
      (UnaryMachine.fields [columns] ++ word scalar ++
        3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))
    have incremented' : Tape.Steps (HeaderIncrementMachine.machine 1) (3 * (row.val + 1) + 2)
        (Tape.configuration (.inl (Fin.last 1)) []
          (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))))
        (Tape.configuration (.inr (0, 2)) []
          (UnaryMachine.fields [row.val, column.val + 1, columns] ++ word scalar ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
      simpa [UnaryMachine.fields, List.append_assoc] using incremented
    have result := Tape.sequence_steps (Sum.inl (Fin.last 1) : HeaderIncrementMachine.State 1)
      mapped mapHalt incremented'
    refine ⟨mapTicks + (3 * (row.val + 1) + 2 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_parameter, assignment]
      have rowBound := row.isLt
      omega
    · simpa only [Tape.configuration, matrixWidth, scalar, updated, output] using result

end RuntimeWrites

end Polytime.Examples.MatrixWrite
