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

import Polytime1.Examples.MatrixAccess
import Polytime1.Examples.MatrixPairAddress

/-! # Matrix-entry reads retaining additional runtime header counters

The four address fields are followed by a fixed number of retained counters.
Column elimination uses these counters to keep the pivot column while an
independent counter traverses a target row. Their total storage is polynomially bounded.
-/

namespace Polytime1.Examples.MatrixFrameAccess

open Matrices TupleMachine

-- scalarLevel: the fixed mathematical carrier of matrix entries.
universe scalarLevel

noncomputable section RetainedHeaderAccess

/-- A controller fixed by the scalar presentation computes a runtime row-major
address and reads the canonical matrix entry. The retained second counter may
equal the row count. The input counters and evaluator
scratch survive. Reserved output and binary windows are the entry requirements. -/
theorem realizes_runtime_entry (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (extraBound : SizePolynomial Matrices.context) :
    ∃ (scratch : List (SizeExpression MatrixPairAddress.context)) (Controller : Type)
      (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns)
          (extra : List ℕ) (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (matrix row column)).getLsbD offset.val)
          let retained := UnaryMachine.fields
            (scratch.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns))) ++
              UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit
              (retained.reverse ++ 6 :: (List.replicate ((row.val * columns + column.val) * field.bitWidth) 0 ++ [7]))
              (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨scratch, certificate⟩ := MatrixPairAddress.frame_realization field.bitWidth
  let input : List (SizeExpression MatrixPairAddress.context) :=
    [.parameter .rowIndex, .parameter .otherRowIndex, .parameter .columnIndex, .parameter .columnCount]
  let parameters := scratch ++ input
  obtain ⟨Controller, finite, inhabited, entry, exit, program, arithmeticCost, halt, runs⟩ :=
    RetainedLookupMachine.realizes_computed_address input parameters (MatrixPairAddress.expression field.bitWidth)
      certificate (MatrixAccess.scalar_width_positive field)
  let dimensions : MatrixPairAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .otherRowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let storage : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((parameters.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant parameters.length + extraBound
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  refine ⟨scratch, Controller, finite, inhabited, entry, exit, program,
    MvPolynomial.rename dimensions arithmeticCost + SizePolynomial.constant 1280 * (capacity + storage + 1) ^ 2 + 1,
    halt, ?_⟩
  · intro rows columns matrix row otherRow column extra extraBounded window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let scalar := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
    let start := (row.val * columns + column.val) * field.bitWidth
    let retained := UnaryMachine.fields (scratch.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns))) ++
      UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)
    have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
    have partition : payload.take start ++ List.ofFn scalar ++ payload.drop (start + field.bitWidth) = payload ∧
        (payload.take start).length = start ∧
        (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
      encode_entry_partition field rows columns matrix row column
    obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
    have retainedEquality : retained = UnaryMachine.fields
        (parameters.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns)) ++ extra) := by
      simp [retained, parameters, input, MatrixPairAddress.assignment, UnaryMachine.fields_append, List.append_assoc]
    have retainedCost : retained.length ≤ storage.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((parameters.map SizeExpression.polynomial).sum)
        (MatrixPairAddress.assignment row.val otherRow.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixPairAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt_succ otherRow.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have retainedLength : retained.length = ((parameters.map SizeExpression.polynomial).sum).eval
          (MatrixPairAddress.assignment row.val otherRow.val column.val columns) + parameters.length + (UnaryMachine.fields extra).length := by
        rw [retainedEquality]
        simp only [UnaryMachine.fields_append, List.length_append, UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have storageValue : storage.eval (assignment rows columns) =
          ((parameters.map SizeExpression.polynomial).sum).eval
            (fun name => assignment rows columns (dimensions name)) + parameters.length + extraBound.eval (assignment rows columns) := by
        simp [storage, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [retainedLength, storageValue]
      omega
    obtain ⟨ticks, cost, trace⟩ := runs (MatrixPairAddress.assignment row.val otherRow.val column.val columns) scalar
      (payload.take start) (payload.drop (start + field.bitWidth)) extra window right inputSymbol
      (by simpa only [start, MatrixPairAddress.expression, SizeExpression.eval_mul,
        SizeExpression.eval_add, SizeExpression.eval_constant, SizeExpression.eval_parameter,
        MatrixPairAddress.assignment] using beforeLength)
      windowWidth windowValid inputValid
    rw [physicalWidth] at cost trace
    simp only [beforeLength] at trace
    have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word payload := by
      rw [← word_append, ← word_append, decomposition]
    have arithmeticBound : arithmeticCost.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns) ≤
        (MvPolynomial.rename dimensions arithmeticCost).eval (assignment rows columns) := by
      calc
        _ ≤ arithmeticCost.eval (fun name => assignment rows columns (dimensions name)) :=
          SizePolynomial.eval_mono arithmeticCost _ _ (by
            intro name; cases name <;> simp only [MatrixPairAddress.assignment, dimensions, assignment]
            · exact Nat.le_of_lt row.isLt
            · exact Nat.le_of_lt_succ otherRow.isLt
            · exact Nat.le_of_lt column.isLt
            · exact le_rfl)
        _ = _ := by
          simp only [SizePolynomial.eval, MvPolynomial.eval_rename, Function.comp_def]
    refine ⟨ticks, ?_, ?_⟩
    · have capacityValue : capacity.eval (assignment rows columns) = matrixWidth := by
        simp [capacity, matrixWidth, exact_width, assignment]
      have storageBound : 1280 * (matrixWidth + retained.length + 1) ^ 2 ≤
          1280 * (matrixWidth + storage.eval (assignment rows columns) + 1) ^ 2 :=
        Nat.mul_le_mul_left 1280 (Nat.pow_le_pow_left (by omega) 2)
      rw [← retainedEquality] at cost
      simp only [SizePolynomial.eval, map_add, map_mul, map_pow, map_one,
        SizePolynomial.constant, MvPolynomial.eval_C]
      change ticks ≤ (MvPolynomial.rename dimensions arithmeticCost).eval (assignment rows columns) +
        1280 * (capacity.eval (assignment rows columns) + storage.eval (assignment rows columns) + 1) ^ 2 + 1
      rw [capacityValue]
      omega
    · rw [← retainedEquality] at trace
      simpa only [input, List.map_cons, List.map_nil, SizeExpression.eval_parameter,
        MatrixPairAddress.assignment, UnaryMachine.fields_cons, UnaryMachine.fields_append,
        retained, List.append_assoc, List.cons_append, decomposition, packed,
        scalar, payload, matrixWidth, start] using trace

/-- Read from runtime counters, optionally apply a fixed scalar operation in
place, and clear evaluator scratch before returning to the header. The matrix
and trailing caller-owned input are preserved. -/
theorem realizes_runtime_entry_restored (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount) (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨scratch, ReadState, finite, inhabited, readEntry, readExit, readMachine,
    readBound, readHalt, readRuns⟩ := realizes_runtime_entry field extraBound
  let readFinite : Fintype ReadState := finite
  let readInhabited : Inhabited ReadState := inhabited
  let dimensions : MatrixPairAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .otherRowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let scratchBound : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((scratch.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant scratch.length
  let headerBound : SizePolynomial Matrices.context := SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 4 + extraBound
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  let scalarMachine := InPlaceTableMachine.machine (FiniteTableMachine.encodedTable field.codec field.codec operation)
  let finishMachine := Tape.sequence scalarMachine (HeaderReturnMachine.machine (4 + extraCount)) (Fin.last (4 + extraCount), 0)
  refine ⟨Sum ReadState (Sum (FiniteTableMachine.State field.bitWidth field.bitWidth)
      (HeaderReturnMachine.State (4 + extraCount))), inferInstance, inferInstance,
    .inl readEntry, .inr (.inr (0, 5)),
    Tape.sequence readMachine finishMachine (.inl (.read 0 (fun _ => false))),
    readBound + headerBound + SizePolynomial.constant 3 * (scratchBound + capacity) +
      SizePolynomial.constant (3 * field.bitWidth + 12),
    ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, finishMachine, HeaderReturnMachine.halt]
  · intro rows columns matrix row otherRow column extra extraLength extraBounded window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth => (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
    let values := scratch.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns))
    let start := (row.val * columns + column.val) * field.bitWidth
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row otherRow column extra extraBounded window inputSymbol right windowWidth windowValid inputValid
    have transformed := InPlaceTableMachine.realizes_operation field.codec operation (matrix row column)
      ((UnaryMachine.fields values ++ UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).reverse ++
        6 :: (List.replicate start 0 ++ [7]))
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have finished := HeaderReturnMachine.restore_blank (count := 4 + extraCount) ([row.val, otherRow.val, column.val, columns] ++ extra) values start
      (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
      (by simp [extraLength]; omega) (by simp) (InPlaceTableMachine.halt _) transformed
    have result := Tape.sequence_steps
      (Sum.inl (FiniteTableMachine.State.read 0 (fun _ => false)) :
        Sum (FiniteTableMachine.State field.bitWidth field.bitWidth) (HeaderReturnMachine.State (4 + extraCount)))
      read readHalt finished
    have scratchCost : (UnaryMachine.fields values).length ≤ scratchBound.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((scratch.map SizeExpression.polynomial).sum)
        (MatrixPairAddress.assignment row.val otherRow.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixPairAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt_succ otherRow.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have source : (UnaryMachine.fields values).length = ((scratch.map SizeExpression.polynomial).sum).eval
          (MatrixPairAddress.assignment row.val otherRow.val column.val columns) + scratch.length := by
        simp only [values, UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have target : scratchBound.eval (assignment rows columns) = ((scratch.map SizeExpression.polynomial).sum).eval
          (fun name => assignment rows columns (dimensions name)) + scratch.length := by
        simp [scratchBound, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [source, target]
      exact Nat.add_le_add_right monotone scratch.length
    have headerCost : (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).length ≤ headerBound.eval (assignment rows columns) := by
      simp [headerBound, assignment]
      have rowBound := row.isLt
      have otherBound := otherRow.isLt
      have columnBound := column.isLt
      simp [UnaryMachine.fields_length] at extraBounded ⊢
      omega
    have addressCost : start ≤ capacity.eval (assignment rows columns) := by
      simp only [capacity, SizePolynomial.eval_mul, SizePolynomial.eval_parameter, SizePolynomial.eval_constant, assignment]
      dsimp [start]
      apply Nat.mul_le_mul_right
      calc
        row.val * columns + column.val ≤ row.val * columns + columns := by omega
        _ = (row.val + 1) * columns := by ring
        _ ≤ rows * columns := Nat.mul_le_mul_right columns row.isLt
    refine ⟨readTicks + (3 * field.bitWidth + 2 +
      ((UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra)).length +
        3 * ((UnaryMachine.fields values).length + start) + 8 + 1) + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [Tape.configuration, values, start, scalar, payload, matrixWidth, List.append_assoc] using result

end RetainedHeaderAccess

end Polytime1.Examples.MatrixFrameAccess
