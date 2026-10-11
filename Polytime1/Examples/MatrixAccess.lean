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

import Polytime1.Examples.Matrices
import Polytime1.TupleLookupMachine
import Polytime1.BlockLookupMachine
import Polytime1.BlockWriteMachine
import Polytime1.AddressLookupMachine
import Polytime1.Examples.MatrixAddress
import Polytime1.RetainedLookupMachine
import Polytime1.HeaderReturnMachine
import Polytime1.InPlaceTableMachine

/-! # Indexed access to canonical matrix bits

The same finite controller works for all matrix dimensions. The binary address
is supplied as scratch input; computing and replenishing it are separate routines.
-/

namespace Polytime1.Examples.MatrixAccess

open Matrices TupleMachine

-- scalarLevel: the fixed carrier of matrix entries.
universe scalarLevel

noncomputable section MatrixAccessExamples

/-- Row-major scalar-bit address, using Mathlib's product indexing. -/
def address (field : FixedPresentation.{scalarLevel}) {rows columns : ℕ}
    (row : Fin rows) (column : Fin columns) (offset : Fin field.bitWidth) :
    Fin ((domain field).bitWidth (assignment rows columns)) :=
  (finProdFinEquiv (finProdFinEquiv (row, column), offset)).cast
    (exact_width field rows columns).symm

@[simp] theorem address_value (field : FixedPresentation.{scalarLevel}) {rows columns : ℕ}
    (row : Fin rows) (column : Fin columns) (offset : Fin field.bitWidth) :
    (address field row column offset).val =
      (row.val * columns + column.val) * field.bitWidth + offset.val := by
  simp only [address, Fin.val_cast, finProdFinEquiv]
  change offset.val + field.bitWidth * (column.val + columns * row.val) = _
  ring

/-- Actual polynomially many tape moves/writes read an entry bit and preserve
all canonical matrix bits and both caller-owned contexts. -/
theorem realizes_entry_bit (field : FixedPresentation.{scalarLevel}) (rows columns : ℕ)
    (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
    (row : Fin rows) (column : Fin columns) (offset : Fin field.bitWidth)
    (left right : List Symbol) :
    ∃ ticks, ticks ≤ 128 * (rows * columns * field.bitWidth + 1) ^ 2 ∧
      Tape.Steps TupleLookupMachine.machine ticks
        (configuration false 1 left
          (data false :: word (Binary.digits ((domain field).bitWidth (assignment rows columns))
            ((row.val * columns + column.val) * field.bitWidth + offset.val)) ++ 4 ::
            word (List.ofFn (BoolTuple.fromBits (encode field rows columns matrix))) ++ right))
        (configuration ((field.codec.encode (matrix row column)).getLsbD offset.val) 15
          (List.replicate ((domain field).bitWidth (assignment rows columns)) (data true) ++ 3 :: left)
          (data ((field.codec.encode (matrix row column)).getLsbD offset.val) ::
            word (List.ofFn (BoolTuple.fromBits (encode field rows columns matrix))) ++ right)) := by
  obtain ⟨ticks, bound, trace⟩ := TupleLookupMachine.realizes_bits
    (encode field rows columns matrix) (address field row column offset) left right
  rw [address_value, encode_entry_bit] at trace
  exact ⟨ticks, by simpa only [exact_width] using bound, trace⟩

/-- A nontrivial finite scalar carrier needs at least one encoding bit. -/
theorem scalar_width_positive (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
    0 < field.bitWidth := by
  obtain ⟨first, second, different⟩ := exists_pair_ne field.Carrier
  by_contra zero
  have widthZero : field.bitWidth = 0 := by omega
  apply different
  apply field.codec.injective
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro offset valid
  omega

/-- Read a complete scalar entry from the canonical matrix encoding. The
output window is reusable, and the matrix and both surrounding regions survive
unchanged. The address is a supplied binary scratch field. -/
theorem realizes_entry (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
    (row : Fin rows) (column : Fin columns) (reserved left right : List Symbol)
    (reservedWidth : reserved.length = field.bitWidth) :
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns matrix).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode (matrix row column)).getLsbD offset.val)
    ∃ ticks, ticks ≤ 384 * (rows * columns * field.bitWidth + 1) ^ 2 ∧
      Tape.Steps (BlockLookupMachine.machine (width := field.bitWidth)) ticks
        (Tape.configuration (.inl (false, 1)) (reserved ++ left)
          (data false :: word (Binary.digits matrixWidth
            ((row.val * columns + column.val) * field.bitWidth)) ++ 4 :: (word payload ++ right)))
        (Tape.configuration (.inr (.inr .halt)) left
          (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  dsimp only
  let matrixWidth := (domain field).bitWidth (assignment rows columns)
  let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
  let scalar := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
  let start := (row.val * columns + column.val) * field.bitWidth
  have positive := scalar_width_positive field
  have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
  have partition : payload.take start ++ List.ofFn scalar ++ payload.drop (start + field.bitWidth) = payload ∧
      (payload.take start).length = start ∧
      (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
    encode_entry_partition field rows columns matrix row column
  obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
  have indexFits : start < 2 ^ matrixWidth := (by omega : start < matrixWidth).trans Nat.lt_two_pow_self
  have counterValue : Binary.value (Binary.digits matrixWidth start) = (payload.take start).length := by
    simp only [beforeLength, Binary.digits_value, Nat.mod_eq_of_lt indexFits]
  obtain ⟨ticks, bound, trace⟩ := BlockLookupMachine.lookup scalar (Binary.digits matrixWidth start)
    (payload.take start) (payload.drop (start + field.bitWidth)) reserved left right
    positive reservedWidth counterValue
  refine ⟨ticks, ?_, ?_⟩
  · simp only [Binary.digits_length] at bound
    have frameWidth : matrixWidth + (payload.take start).length + field.bitWidth +
        (payload.drop (start + field.bitWidth)).length + 2 = 2 * (matrixWidth + 1) := by omega
    rw [frameWidth] at bound
    have cost : 96 * (2 * (matrixWidth + 1)) ^ 2 = 384 * (matrixWidth + 1) ^ 2 := by ring
    rw [cost] at bound
    simpa only [matrixWidth, exact_width] using bound
  · have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word payload := by
      rw [← word_append, ← word_append, decomposition]
    simpa only [Binary.digits_length, decomposition, packed, payload, scalar, matrixWidth, start] using trace

/-- Read a canonical entry starting from blank binary scratch and a bounded
unary address. Initialization, conversion, and lookup all contribute to the bound. -/
theorem realizes_entry_from_blank (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
    (row : Fin rows) (column : Fin columns) (left right : List Symbol) :
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let start := (row.val * columns + column.val) * field.bitWidth
    let payload := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns matrix).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode (matrix row column)).getLsbD offset.val)
    ∃ ticks, ticks ≤ 640 * (rows * columns * field.bitWidth + 1) ^ 2 ∧
      Tape.Steps (Tape.sequence AddressMachine.ZeroWindow.machine
        (AddressLookupMachine.machine (width := field.bitWidth)) (.inl (.inl 3))) ticks
        (Tape.configuration (.inl 0)
          (3 :: (List.replicate field.bitWidth 0 ++ UnaryMachine.units start ++ 7 :: left))
          (List.replicate matrixWidth 0 ++ 4 :: (word payload ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr .halt))))
          (List.replicate start 0 ++ 7 :: left)
          (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  dsimp only
  let matrixWidth := (domain field).bitWidth (assignment rows columns)
  let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
  let scalar := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
  let start := (row.val * columns + column.val) * field.bitWidth
  have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
  have partition : payload.take start ++ List.ofFn scalar ++ payload.drop (start + field.bitWidth) = payload ∧
      (payload.take start).length = start ∧
      (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
    encode_entry_partition field rows columns matrix row column
  obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
  obtain ⟨ticks, bound, trace⟩ := AddressLookupMachine.realizes_from_blank scalar
    (payload.take start) (payload.drop (start + field.bitWidth)) left right (scalar_width_positive field)
  refine ⟨ticks, ?_, ?_⟩
  · rw [physicalWidth] at bound
    simpa only [matrixWidth, exact_width] using bound
  · have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word payload := by
      rw [← word_append, ← word_append, decomposition]
    rw [physicalWidth] at trace
    simpa only [beforeLength, decomposition, packed, payload, scalar, matrixWidth, start] using trace

/-- A controller fixed by the scalar presentation computes a runtime row-major
address and reads the canonical matrix entry. The input counters and evaluator
scratch survive. Reserved output and binary windows are the entry requirements. -/
theorem realizes_runtime_entry (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
    ∃ (scratch : List (SizeExpression MatrixAddress.context)) (Controller : Type)
      (_finite : Fintype Controller) (inhabited : Inhabited Controller),
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
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (matrix row column)).getLsbD offset.val)
          let retained := UnaryMachine.fields
            (scratch.map (·.eval (MatrixAddress.assignment row.val column.val columns))) ++
              UnaryMachine.fields [row.val, column.val, columns]
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit
              (retained.reverse ++ 6 :: (List.replicate ((row.val * columns + column.val) * field.bitWidth) 0 ++ [7]))
              (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨scratch, certificate⟩ := MatrixAddress.frame_realization field.bitWidth
  let input : List (SizeExpression MatrixAddress.context) :=
    [.parameter .rowIndex, .parameter .columnIndex, .parameter .columnCount]
  let parameters := scratch ++ input
  obtain ⟨Controller, finite, inhabited, entry, exit, program, arithmeticCost, halt, runs⟩ :=
    RetainedLookupMachine.realizes_computed_address input parameters (MatrixAddress.expression field.bitWidth)
      certificate (scalar_width_positive field)
  let dimensions : MatrixAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let storage : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((parameters.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant parameters.length
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  refine ⟨scratch, Controller, finite, inhabited, entry, exit, program,
    MvPolynomial.rename dimensions arithmeticCost + SizePolynomial.constant 1280 * (capacity + storage + 1) ^ 2 + 1,
    halt, ?_⟩
  · intro rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let scalar := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
    let start := (row.val * columns + column.val) * field.bitWidth
    let retained := UnaryMachine.fields (scratch.map (·.eval (MatrixAddress.assignment row.val column.val columns))) ++
      UnaryMachine.fields [row.val, column.val, columns]
    have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
    have partition : payload.take start ++ List.ofFn scalar ++ payload.drop (start + field.bitWidth) = payload ∧
        (payload.take start).length = start ∧
        (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
      encode_entry_partition field rows columns matrix row column
    obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
    have retainedEquality : retained = UnaryMachine.fields
        (parameters.map (·.eval (MatrixAddress.assignment row.val column.val columns))) := by
      simp [retained, parameters, input, MatrixAddress.assignment]
    have retainedCost : retained.length ≤ storage.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((parameters.map SizeExpression.polynomial).sum)
        (MatrixAddress.assignment row.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have retainedLength : retained.length = ((parameters.map SizeExpression.polynomial).sum).eval
          (MatrixAddress.assignment row.val column.val columns) + parameters.length := by
        rw [retainedEquality]
        simp only [UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have storageValue : storage.eval (assignment rows columns) =
          ((parameters.map SizeExpression.polynomial).sum).eval
            (fun name => assignment rows columns (dimensions name)) + parameters.length := by
        simp [storage, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [retainedLength, storageValue]
      exact Nat.add_le_add_right monotone parameters.length
    obtain ⟨ticks, cost, trace⟩ := runs (MatrixAddress.assignment row.val column.val columns) scalar
      (payload.take start) (payload.drop (start + field.bitWidth)) [] window right inputSymbol
      (by simpa only [start, MatrixAddress.expression, SizeExpression.eval_mul,
        SizeExpression.eval_add, SizeExpression.eval_constant, SizeExpression.eval_parameter,
        MatrixAddress.assignment] using beforeLength)
      windowWidth windowValid inputValid
    simp only [List.append_nil] at cost trace
    rw [physicalWidth] at cost trace
    simp only [beforeLength] at trace
    have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
        word (payload.drop (start + field.bitWidth)) = word payload := by
      rw [← word_append, ← word_append, decomposition]
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
        MatrixAddress.assignment, UnaryMachine.fields_cons, retained, List.append_assoc,
        decomposition, packed, scalar, payload, matrixWidth, start] using trace

/-- Read from runtime counters, optionally apply a fixed scalar operation in
place, and clear evaluator scratch before returning to the header. The matrix
and trailing caller-owned input are preserved. -/
theorem realizes_runtime_entry_restored (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier := id) :
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
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨scratch, ReadState, finite, inhabited, readEntry, readExit, readMachine,
    readBound, readHalt, readRuns⟩ := realizes_runtime_entry field
  let readFinite : Fintype ReadState := finite
  let readInhabited : Inhabited ReadState := inhabited
  let dimensions : MatrixAddress.context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  let scratchBound : SizePolynomial Matrices.context :=
    MvPolynomial.rename dimensions ((scratch.map SizeExpression.polynomial).sum) +
      SizePolynomial.constant scratch.length
  let headerBound : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K +
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 3
  let capacity : SizePolynomial Matrices.context := SizePolynomial.parameter (ctx := Matrices.context) .K *
    SizePolynomial.parameter (ctx := Matrices.context) .L * SizePolynomial.constant field.bitWidth
  let scalarMachine := InPlaceTableMachine.machine (FiniteTableMachine.encodedTable field.codec field.codec operation)
  let finishMachine := Tape.sequence scalarMachine (HeaderReturnMachine.machine 3) (Fin.last 3, 0)
  refine ⟨Sum ReadState (Sum (FiniteTableMachine.State field.bitWidth field.bitWidth)
      (HeaderReturnMachine.State 3)), inferInstance, inferInstance,
    .inl readEntry, .inr (.inr (0, 5)),
    Tape.sequence readMachine finishMachine (.inl (.read 0 (fun _ => false))),
    readBound + headerBound + SizePolynomial.constant 3 * (scratchBound + capacity) +
      SizePolynomial.constant (3 * field.bitWidth + 12),
    ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, finishMachine, HeaderReturnMachine.halt]
  · intro rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth => (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
    let values := scratch.map (·.eval (MatrixAddress.assignment row.val column.val columns))
    let start := (row.val * columns + column.val) * field.bitWidth
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    have transformed := InPlaceTableMachine.realizes_operation field.codec operation (matrix row column)
      ((UnaryMachine.fields values ++ UnaryMachine.fields [row.val, column.val, columns]).reverse ++
        6 :: (List.replicate start 0 ++ [7]))
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have finished := HeaderReturnMachine.restore_blank (count := 3) [row.val, column.val, columns] values start
      (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
      rfl (by simp) (InPlaceTableMachine.halt _) transformed
    have result := Tape.sequence_steps
      (Sum.inl (FiniteTableMachine.State.read 0 (fun _ => false)) :
        Sum (FiniteTableMachine.State field.bitWidth field.bitWidth) (HeaderReturnMachine.State 3))
      read readHalt finished
    have scratchCost : (UnaryMachine.fields values).length ≤ scratchBound.eval (assignment rows columns) := by
      have monotone := SizePolynomial.eval_mono ((scratch.map SizeExpression.polynomial).sum)
        (MatrixAddress.assignment row.val column.val columns)
        (fun name => assignment rows columns (dimensions name)) (by
          intro name; cases name <;> simp only [MatrixAddress.assignment, dimensions, assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      have source : (UnaryMachine.fields values).length = ((scratch.map SizeExpression.polynomial).sum).eval
          (MatrixAddress.assignment row.val column.val columns) + scratch.length := by
        simp only [values, UnaryMachine.fields_length, List.length_map, SizePolynomial.eval_sum,
          List.map_map, Function.comp_def, ← SizeExpression.eval_eq]
      have target : scratchBound.eval (assignment rows columns) = ((scratch.map SizeExpression.polynomial).sum).eval
          (fun name => assignment rows columns (dimensions name)) + scratch.length := by
        simp [scratchBound, SizePolynomial.eval, SizePolynomial.constant, MvPolynomial.eval_rename, Function.comp_def]
      rw [source, target]
      exact Nat.add_le_add_right monotone scratch.length
    have headerCost : (UnaryMachine.fields [row.val, column.val, columns]).length ≤ headerBound.eval (assignment rows columns) := by
      simp [headerBound, assignment]
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
      ((UnaryMachine.fields [row.val, column.val, columns]).length +
        3 * ((UnaryMachine.fields values).length + start) + 8 + 1) + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [Tape.configuration, values, start, scalar, payload, matrixWidth, List.append_assoc] using result

/-- Two complete indexed reads reuse one frame. The second call consumes the
first call's scalar output and all-one counter window, and again restores the
original header and blank left scratch. Both runtime address computations count. -/
theorem realizes_two_runtime_reads (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
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
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (matrix row column)).getLsbD offset.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨ReadState, finite, inhabited, readEntry, readExit, readMachine, readBound, readHalt, readRuns⟩ :=
    realizes_runtime_entry_restored field
  let readFinite : Fintype ReadState := finite
  let readInhabited : Inhabited ReadState := inhabited
  refine ⟨Sum ReadState ReadState, inferInstance, inferInstance,
    .inl readEntry, .inr readExit, Tape.sequence readMachine readMachine readEntry,
    SizePolynomial.constant 2 * readBound + 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, readHalt]
  · intro rows columns matrix row column window inputSymbol right windowWidth windowValid inputValid
    dsimp only
    let scalar := List.ofFn (fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val)
    have scalarWidth : (word scalar).length = field.bitWidth := by simp [word, scalar]
    have scalarValid : ∀ symbol ∈ word scalar, symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol
      cases bit <;> decide
    obtain ⟨firstTicks, firstCost, first⟩ := readRuns rows columns matrix row column
      window inputSymbol right windowWidth windowValid inputValid
    obtain ⟨secondTicks, secondCost, second⟩ := readRuns rows columns matrix row column
      (word scalar) (data true) right scalarWidth scalarValid (by decide)
    have result := Tape.sequence_steps readEntry first readHalt second
    refine ⟨firstTicks + (secondTicks + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_one]
      omega
    · simpa only [Tape.configuration, scalar, Function.id_def] using result

/-- Write a runtime scalar into one canonical matrix entry, preserving every
other entry and both caller-owned contexts. The replacement slot is retained. -/
theorem stores_entry (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
    (row : Fin rows) (column : Fin columns) (replacement : field.Carrier) (left right : List Symbol) :
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns matrix).getLsbD index.val)
    let updated := Function.update matrix row (Function.update (matrix row) column replacement)
    let result := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns updated).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode replacement).getLsbD offset.val)
    ∃ ticks, ticks ≤ 512 * (rows * columns * field.bitWidth + 1) ^ 2 ∧
      Tape.Steps (BlockWriteMachine.machine (width := field.bitWidth)) ticks
        (Tape.configuration (.inl (.read 0 (fun _ => false))) left
          (word scalar ++ data false :: word (Binary.digits matrixWidth
            ((row.val * columns + column.val) * field.bitWidth)) ++ 4 :: (word payload ++ right)))
        (Tape.configuration (.inr (.inr (.inr (.inr (.inr .halt))))) left
          (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  dsimp only
  let matrixWidth := (domain field).bitWidth (assignment rows columns)
  let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
  let original := fun offset : Fin field.bitWidth => (field.codec.encode (matrix row column)).getLsbD offset.val
  let scalar := fun offset : Fin field.bitWidth => (field.codec.encode replacement).getLsbD offset.val
  let updated := Function.update matrix row (Function.update (matrix row) column replacement)
  let result := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns updated).getLsbD index.val)
  let start := (row.val * columns + column.val) * field.bitWidth
  have positive := scalar_width_positive field
  have blockFits : start + field.bitWidth ≤ matrixWidth := entry_block_fits field rows columns row column
  have partition : payload.take start ++ List.ofFn original ++ payload.drop (start + field.bitWidth) = payload ∧
      (payload.take start).length = start ∧
      (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = matrixWidth :=
    encode_entry_partition field rows columns matrix row column
  obtain ⟨decomposition, beforeLength, physicalWidth⟩ := partition
  have indexFits : start < 2 ^ matrixWidth := (by omega : start < matrixWidth).trans Nat.lt_two_pow_self
  have counterValue : Binary.value (Binary.digits matrixWidth start) = (payload.take start).length := by
    simp only [beforeLength, Binary.digits_value, Nat.mod_eq_of_lt indexFits]
  obtain ⟨ticks, bound, trace⟩ := BlockWriteMachine.store scalar original (Binary.digits matrixWidth start)
    (payload.take start) (payload.drop (start + field.bitWidth)) left right positive counterValue
  have packed : word (payload.take start) ++ word (List.ofFn scalar) ++
      word (payload.drop (start + field.bitWidth)) = word result := by
    rw [← word_append, ← word_append]
    apply congrArg word
    simpa only [List.append_assoc] using (encode_update_entry field rows columns matrix row column replacement).symm
  refine ⟨ticks, ?_, ?_⟩
  · simp only [Binary.digits_length] at bound
    have frameWidth : matrixWidth + (payload.take start).length + field.bitWidth +
        (payload.drop (start + field.bitWidth)).length + 2 = 2 * (matrixWidth + 1) := by omega
    rw [frameWidth] at bound
    have cost : 128 * (2 * (matrixWidth + 1)) ^ 2 = 512 * (matrixWidth + 1) ^ 2 := by ring
    rw [cost] at bound
    simpa only [matrixWidth, exact_width] using bound
  · simpa only [Binary.digits_length, decomposition, packed, payload, scalar, matrixWidth, start, result, updated] using trace

end MatrixAccessExamples

/-- Observe the entire output and surrounding right context after lookup. -/
def execute (bits : List Bool) (index : Fin bits.length)
    (left right : List Symbol) : Option (List Symbol) :=
  (Tape.run TupleLookupMachine.machine (128 * (bits.length + 1) ^ 2)
    (configuration false 1 left
      (data false :: word (Binary.digits bits.length index.val) ++ 4 :: word bits ++ right))).map
    fun final => (List.range (bits.length + right.length + 1)).map final.Tape.right₀.nth

#guard execute [true] 0 [7, 3] [4, 7] = some [2, 2, 4, 7]
#guard execute [true, false, true, false] 3 [7, 3] [7, 4] = some [1, 2, 1, 2, 1, 7, 4]
-- Index eight exercises binary borrowing while every stored bit remains unchanged.
#guard execute [false, true, false, true, false, true, false, true, false] 8 [4, 7] [7] =
  some [1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7]

example (width : ℕ) : Fintype (BlockLookupMachine.State width) := inferInstance

/-- Observe the scalar output, preserved array/right context, and left context. -/
def executeField (width : ℕ) (bits : List Bool) (index : Fin bits.length)
    (reserved left right : List Symbol) : Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (BlockLookupMachine.machine (width := width)) (384 * (bits.length + 1) ^ 2)
    (Tape.configuration (.inl (false, 1)) (reserved ++ left)
      (data false :: word (Binary.digits bits.length index.val) ++ 4 :: (word bits ++ right)))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range left.length).map final.Tape.left.nth)

#guard executeField 3 [false, true, false, true, true, false] 0 [6, 7, 0] [7, 3] [4, 7] =
  some ([1, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard executeField 3 [false, true, false, true, true, false] 3 [6, 7, 0] [7, 3] [4, 7] =
  some ([2, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard executeField 3 [false, true, false, true, false, true, false, true, false, true, true]
    8 [6, 7, 0] [4, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7], [4, 3])
#guard executeField 1 [false] 0 [7] [3] [4, 7] = some ([1], [1, 4, 7], [3])

example (width : ℕ) : Fintype (BlockWriteMachine.State width) := inferInstance

/-- Observe the retained replacement, changed array, and caller-owned contexts. -/
def executeWrite (width : ℕ) (replacement : BitVec width) (bits : List Bool) (index : Fin bits.length)
    (left right : List Symbol) : Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (BlockWriteMachine.machine (width := width)) (512 * (bits.length + 1) ^ 2)
    (Tape.configuration (.inl (.read 0 (fun _ => false))) left
      (word (List.ofFn (BoolTuple.fromBits replacement)) ++ data false ::
        word (Binary.digits bits.length index.val) ++ 4 :: (word bits ++ right)))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range left.length).map final.Tape.left.nth)

#guard executeWrite 3 (BitVec.ofNat 3 6) [false, true, false, true, true, false] 0 [7, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 2, 2, 2, 1, 4, 7], [7, 3])
#guard executeWrite 3 (BitVec.ofNat 3 6) [false, true, false, true, true, false] 3 [7, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 1, 2, 2, 4, 7], [7, 3])
#guard executeWrite 3 (BitVec.ofNat 3 5)
    [false, true, false, true, false, true, false, true, false, true, true] 8 [4, 3] [4, 7] =
  some ([2, 1, 2], [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 7], [4, 3])
#guard executeWrite 1 (BitVec.ofNat 1 1) [false] 0 [3] [4, 7] = some ([2], [2, 4, 7], [3])

end Polytime1.Examples.MatrixAccess
