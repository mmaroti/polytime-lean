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

import Polytime.Examples.MatrixFrameAccess
import Polytime.RetainedWriteMachine

/-! # Matrix-entry updates retaining additional runtime header counters

Retained counters, including the pivot column used by column elimination,
survive address evaluation, scalar writes, and restoration of the caller header.
-/

namespace Polytime.Examples.MatrixFrameWrite

open Matrices TupleMachine

-- scalarLevel: the fixed mathematical carrier of matrix entries.
universe scalarLevel

noncomputable section RetainedHeaderWrites

/-- Compute the address, read the runtime replacement, update one canonical
matrix entry, clear evaluation scratch, and restore the counter header. The
controller is fixed before dimensions, indices, and replacement values vary. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row otherRow : Fin rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (replacement : field.Carrier)
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
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word scalar ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨scratch, ArithmeticState, finite, inhabited, arithmeticEntry, arithmeticExit,
    arithmetic, arithmeticBound, arithmeticHalt, arithmeticRuns⟩ := MatrixPairAddress.realizes field.bitWidth
  let arithmeticFinite : Fintype ArithmeticState := finite
  let arithmeticInhabited : Inhabited ArithmeticState := inhabited
  let WriterState := Sum (Fin 6) (Sum (Fin 4) (RetainedWriteMachine.State field.bitWidth))
  let writer : Turing.TM0.Machine Symbol WriterState := Tape.sequence RetainedLookupMachine.Entry.machine
    (Tape.sequence AddressMachine.ZeroWindow.machine
      (RetainedWriteMachine.machine (width := field.bitWidth)) (.inl (.inl 3))) (.inl 0)
  let writerEntry : WriterState := .inl 0
  let writerExit : WriterState := .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr .halt))))))))
  let dimensions : MatrixPairAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .otherRowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let parameters := scratch ++ [SizeExpression.parameter (ctx := MatrixPairAddress.context) .rowIndex,
    .parameter .otherRowIndex, .parameter .columnIndex, .parameter .columnCount]
  let storage : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((parameters.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant parameters.length + extraBound
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  let headerBound : SizePolynomial Matrices.context := SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 4 + extraBound
  refine ⟨Sum (Sum ArithmeticState WriterState) (HeaderReturnMachine.State (4 + extraCount)), inferInstance, inferInstance,
    .inl (.inl arithmeticEntry), .inr (0, 5),
    Tape.sequence (Tape.sequence arithmetic writer writerEntry) (HeaderReturnMachine.machine (4 + extraCount)) (Fin.last (4 + extraCount), 0),
    arithmeticBound + SizePolynomial.constant 1024 * (capacity + storage + 1) ^ 2 + headerBound +
      SizePolynomial.constant 3 * (storage + capacity) + SizePolynomial.constant 10, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderReturnMachine.halt]
  · intro rows columns matrix row otherRow column extra extraLength extraBounded replacement inputSymbol right inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let original := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
    let scalar := fun offset : Fin field.bitWidth => (field.codec.encode replacement).getLsbD offset.val
    let updated := Function.update matrix row (Function.update (matrix row) column replacement)
    let output := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns updated).getLsbD index.val)
    let start := (row.val * columns + column.val) * field.bitWidth
    let values := scratch.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns))
    let retained := UnaryMachine.fields values ++ UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)
    have entryBound : row.val * columns + column.val + 1 ≤ rows * columns := by
      calc
        _ ≤ row.val * columns + columns := by omega
        _ = (row.val + 1) * columns := by ring
        _ ≤ rows * columns := Nat.mul_le_mul_right columns row.isLt
    have blockFits : start + field.bitWidth ≤ matrixWidth := by
      dsimp only [start, matrixWidth]
      rw [exact_width]
      simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right field.bitWidth entryBound
    have payloadLength : payload.length = matrixWidth := List.length_ofFn
    have slice : (payload.drop start).take field.bitWidth = List.ofFn original :=
      encode_entry_slice field rows columns matrix row column
    have decomposition : payload.take start ++ List.ofFn original ++ payload.drop (start + field.bitWidth) = payload := by
      have split := List.take_append_drop (start + field.bitWidth) payload
      rw [List.take_add, slice] at split
      exact split
    have beforeLength : (payload.take start).length = start := by
      simp only [List.length_take, payloadLength, Nat.min_eq_left (by omega : start ≤ matrixWidth)]
    have physicalWidth : (payload.take start).length + field.bitWidth +
        (payload.drop (start + field.bitWidth)).length = matrixWidth := by
      have lengths := congrArg List.length decomposition
      simpa only [List.length_append, List.length_ofFn, payloadLength] using lengths
    have retainedEquality : retained = UnaryMachine.fields
        (parameters.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns)) ++ extra) := by
      simp [retained, values, parameters, MatrixPairAddress.assignment, UnaryMachine.fields_append, List.append_assoc]
    have retainedValid : ∀ symbol ∈ retained, symbol ≠ 3 ∧ symbol ≠ 6 := by
      rw [retainedEquality]
      intro symbol member
      rcases UnaryMachine.fields_symbols _ symbol member with equality | equality <;> subst symbol <;> decide
    have retainedCost : retained.length ≤ storage.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((parameters.map SizeExpression.polynomial).sum)
        (MatrixPairAddress.assignment row.val otherRow.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixPairAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt otherRow.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have source : retained.length = ((parameters.map SizeExpression.polynomial).sum).eval
          (MatrixPairAddress.assignment row.val otherRow.val column.val columns) + parameters.length + (UnaryMachine.fields extra).length := by
        rw [retainedEquality]
        simp only [UnaryMachine.fields_append, List.length_append, UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have target : storage.eval (assignment rows columns) = ((parameters.map SizeExpression.polynomial).sum).eval
          (fun name => assignment rows columns (dimensions name)) + parameters.length + extraBound.eval (assignment rows columns) := by
        simp [storage, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [source, target]
      omega
    have scratchCost : (UnaryMachine.fields values).length ≤ storage.eval (assignment rows columns) :=
      (by simp [retained] : (UnaryMachine.fields values).length ≤ retained.length).trans retainedCost
    have headerCost : (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).length ≤ headerBound.eval (assignment rows columns) := by
      simp [headerBound, assignment]
      have rowBound := row.isLt
      have otherBound := otherRow.isLt
      have columnBound := column.isLt
      simp [UnaryMachine.fields_length] at extraBounded ⊢
      omega
    have capacityValue : capacity.eval (assignment rows columns) = matrixWidth := by
      simp [capacity, matrixWidth, exact_width, assignment]
    have addressCost : start ≤ capacity.eval (assignment rows columns) := by rw [capacityValue]; omega
    obtain ⟨addressTicks, addressCost', evaluated⟩ := arithmeticRuns rows columns row otherRow.castSucc column
      (UnaryMachine.fields extra ++ word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right)))
    obtain ⟨writeTicks, writeCost, written⟩ := RetainedWriteMachine.realizes_evaluated_address scalar original
      (payload.take start) (payload.drop (start + field.bitWidth)) inputSymbol retained right
      inputValid retainedValid (MatrixAccess.scalar_width_positive field)
    rw [physicalWidth] at writeCost written
    rw [beforeLength] at written
    have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word output := by
      rw [← word_append, ← word_append]
      simpa only [List.append_assoc] using congrArg word
        (encode_update_entry field rows columns matrix row column replacement).symm
    have evaluated' : Tape.Steps arithmetic addressTicks
        (Tape.configuration arithmeticEntry []
          (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word (List.ofFn scalar) ++
            3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
        (Tape.configuration arithmeticExit []
          (UnaryMachine.units start ++ 1 :: (retained ++ word (List.ofFn scalar) ++
            3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))) := by
      simpa only [Fin.val_castSucc, retained, values, start, UnaryMachine.fields_append, List.append_assoc] using evaluated
    have written' : Tape.Steps writer writeTicks
        (Tape.configuration writerEntry []
          (UnaryMachine.units start ++ 1 :: (retained ++ word (List.ofFn scalar) ++
            3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right)))))
        (Tape.configuration writerExit (retained.reverse ++ 6 :: (List.replicate start 0 ++ [7]))
          (word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
      simpa only [writer, writerEntry, writerExit, decomposition, packed] using written
    have updatedTrace := Tape.sequence_steps writerEntry evaluated' arithmeticHalt written'
    have updatedHalt (symbol : Symbol) : (Tape.sequence arithmetic writer writerEntry) (.inr writerExit) symbol = none := by
      simp [Tape.sequence, writer, writerExit, RetainedWriteMachine.halt]
    have returned := HeaderReturnMachine.realizes ([row.val, otherRow.val, column.val, columns] ++ extra) values start
      (word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))) (by simp)
    have headerLength : ([row.val, otherRow.val, column.val, columns] ++ extra).length = 4 + extraCount := by
      simp [extraLength]; omega
    rw [headerLength] at returned
    have returned' : Tape.Steps (HeaderReturnMachine.machine (4 + extraCount))
        ((UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).length + 3 * ((UnaryMachine.fields values).length + start) + 8)
        (Tape.configuration (Fin.last (4 + extraCount), 0) (retained.reverse ++ 6 :: (List.replicate start 0 ++ [7]))
          (word (List.ofFn scalar) ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))))
        (Tape.configuration (0, 5) []
          (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word (List.ofFn scalar) ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
      simpa only [retained, List.reverse_append, List.append_assoc, List.length_cons, List.length_nil, Nat.reduceAdd] using returned
    have result := Tape.sequence_steps (Fin.last (4 + extraCount), 0) updatedTrace updatedHalt returned'
    refine ⟨addressTicks + (writeTicks + 1) + ((UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).length +
      3 * ((UnaryMachine.fields values).length + start) + 8 + 1), ?_, ?_⟩
    · have boundedWrite : writeTicks ≤ 1024 * (matrixWidth + storage.eval (assignment rows columns) + 1) ^ 2 :=
        writeCost.trans (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left (by omega) 2))
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_one, capacityValue]
      omega
    · simpa only [Tape.configuration, scalar, payload, output, updated, matrixWidth] using result

/-- Read, transform, and write one entry in a shared frame. Both addresses are
computed from runtime counters; the scalar operation is a fixed table. -/
theorem realizes_entry_map (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row otherRow : Fin rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (window : List Symbol) (inputSymbol : Symbol)
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
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨ReadState, readFinite, readInhabited, readEntry, readExit, readMachine,
    readBound, readHalt, readRuns⟩ := MatrixFrameAccess.realizes_runtime_entry_restored field operation extraCount extraBound
  let readerFinite : Fintype ReadState := readFinite
  let readerInhabited : Inhabited ReadState := readInhabited
  obtain ⟨WriteState, writeFinite, writeInhabited, writeEntry, writeExit, writeMachine,
    writeBound, writeHalt, writeRuns⟩ := realizes field extraCount extraBound
  let writerFinite : Fintype WriteState := writeFinite
  let writerInhabited : Inhabited WriteState := writeInhabited
  refine ⟨Sum ReadState WriteState, inferInstance, inferInstance, .inl readEntry, .inr writeExit,
    Tape.sequence readMachine writeMachine writeEntry, readBound + writeBound + 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, writeHalt]
  · intro rows columns matrix row otherRow column extra extraLength extraBounded window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row otherRow.castSucc column
      extra extraLength extraBounded window inputSymbol right windowWidth windowValid inputValid
    simp only [Fin.val_castSucc] at read
    obtain ⟨writeTicks, writeCost, written⟩ := writeRuns rows columns matrix row otherRow column
      extra extraLength extraBounded (operation (matrix row column)) (data true) right (by decide)
    have result := Tape.sequence_steps writeEntry read readHalt written
    refine ⟨readTicks + (writeTicks + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_one]
      omega
    · simpa only [Tape.configuration] using result

end RetainedHeaderWrites

end Polytime.Examples.MatrixFrameWrite
