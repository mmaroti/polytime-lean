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

import Polytime1.Examples.MatrixFrameRowAdd
import Polytime1.HeaderColumnSwapMachine
import Polytime1.HeaderScalarMachine
import Polytime1.HeaderMoveMachine

/-! # Pivot normalization retaining caller counters

Read and invert the runtime target pivot, restore the saved column, and scale
the target row. Row indices, the pivot column, and caller counters survive.
-/

namespace Polytime1.Examples.MatrixNormalizeRowSaved

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeNormalization

/-- Normalize the target row from its runtime pivot entry while preserving
both row indices, the saved pivot column, and additional bounded counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.scaleRow matrix target (matrix target column)⁻¹
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (matrix target column ≠ 0 → updated target column = 1 ∧ Matrix.RowEquivalent matrix updated) := by
  classical
  obtain ⟨ReadState, readFinite, readInhabited, readEntry, readExit, reader, readBound,
    readHalt, readRuns⟩ := MatrixFrameAccess.realizes_runtime_entry_restored field Inv.inv (1 + extraCount) (1 + extraBound)
  let readerFinite : Fintype ReadState := readFinite
  let readerInhabited : Inhabited ReadState := readInhabited
  obtain ⟨ScaleState, scaleFinite, scaleInhabited, scaleEntry, scaleExit, scaler, scaleBound,
    scaleHalt, scaleRuns⟩ := MatrixFrameRowAdd.realizes_scale field (1 + extraCount) (SizePolynomial.parameter (ctx := Matrices.context) .L + 1 + extraBound)
  let scalerFinite : Fintype ScaleState := scaleFinite
  let scalerInhabited : Inhabited ScaleState := scaleInhabited
  let swapper := HeaderMoveMachine.machine 1
  let swapEntry : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inl (Fin.last 1, 0)
  let swapExit : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inr (.inr (.inr (0, 7)))
  let columnSwapper := HeaderColumnSwapMachine.machine
  let columnEntry : HeaderColumnSwapMachine.State := .inl (.inl (.inl (.inl (.inl (Fin.last 2, 0)))))
  let columnExit : HeaderColumnSwapMachine.State := .inr (.inr (.inr (.inr (0, 7))))
  let copier := HeaderScalarMachine.machine (5 + extraCount) field.bitWidth
  let copyEntry : HeaderScalarMachine.State (5 + extraCount) field.bitWidth := .inl (Fin.last (5 + extraCount))
  let first := Tape.sequence columnSwapper swapper swapEntry
  let second := Tape.sequence first reader readEntry
  let third := Tape.sequence second swapper swapEntry
  let fourth := Tape.sequence third columnSwapper columnEntry
  let fifth := Tape.sequence fourth copier copyEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 6 + extraBound
  let swapBound := SizePolynomial.constant 128 * headerBound ^ 2
  let columnBound := SizePolynomial.constant 640 * headerBound ^ 2 + SizePolynomial.constant 4
  let copyBound := SizePolynomial.constant 2 * headerBound + SizePolynomial.constant (4 * field.bitWidth + 5)
  refine ⟨Sum (Sum (Sum (Sum (Sum (Sum HeaderColumnSwapMachine.State (HeaderMoveMachine.State 1)) ReadState)
      (HeaderMoveMachine.State 1)) HeaderColumnSwapMachine.State) (HeaderScalarMachine.State (5 + extraCount) field.bitWidth)) ScaleState,
    inferInstance, inferInstance, .inl (.inl (.inl (.inl (.inl (.inl columnEntry))))), .inr scaleExit,
    Tape.sequence fifth scaler scaleEntry,
    readBound + SizePolynomial.constant 2 * columnBound + SizePolynomial.constant 2 * swapBound +
      copyBound + scaleBound + SizePolynomial.constant 6, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, scaleHalt]
  · intro rows columns matrix source target column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let coefficient := (matrix target column)⁻¹
    let bits := BoolTuple.fromBits (field.codec.encode coefficient)
    let initialSuffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let suffix := word (List.ofFn bits) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    obtain ⟨firstColumnTicks, firstColumnCost, columnsReady⟩ :=
      HeaderColumnSwapMachine.realizes source.val target.val 0 columns column.val (UnaryMachine.fields extra ++ initialSuffix)
    obtain ⟨firstSwapTicks, firstSwapCost, swapped⟩ :=
      HeaderMoveMachine.swaps_row_indices source.val target.val column.val columns (UnaryMachine.fields (0 :: extra) ++ initialSuffix)
    have width : (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))).length =
        field.bitWidth := by simp [word]
    have scalarValid : ∀ symbol ∈ word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))),
        symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix target source.castSucc column
      (0 :: extra) (by simp [extraLength, Nat.add_comm])
      (by
        have extraCost := extraBounded
        simp [UnaryMachine.fields_length] at extraCost
        simp [UnaryMachine.fields_cons]; omega) (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))) (data true) right
      width scalarValid (by decide)
    have encoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (matrix target column)⁻¹).getLsbD offset.val) = bits := by
      funext offset; simp [bits, coefficient, BoolTuple.fromBits]
    simp only [Fin.val_castSucc] at read
    rw [encoding] at read
    have read' : Tape.Steps reader readTicks
        (Tape.configuration readEntry [] (UnaryMachine.fields ([target.val, source.val, column.val, columns, 0] ++ extra) ++ initialSuffix))
        (Tape.configuration readExit [] (UnaryMachine.fields ([target.val, source.val, column.val, columns, 0] ++ extra) ++ suffix)) := by
      simpa only [initialSuffix, suffix, matrixWidth, payload, List.cons_append, List.nil_append, List.append_assoc] using read
    obtain ⟨lastSwapTicks, lastSwapCost, restored⟩ :=
      HeaderMoveMachine.swaps_row_indices target.val source.val column.val columns (UnaryMachine.fields (0 :: extra) ++ suffix)
    obtain ⟨lastColumnTicks, lastColumnCost, columnsRestored⟩ :=
      HeaderColumnSwapMachine.realizes source.val target.val column.val columns 0 (UnaryMachine.fields extra ++ suffix)
    have copied := HeaderScalarMachine.realizes ([source.val, target.val, 0, columns, column.val] ++ extra) bits
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have headerLength : ([source.val, target.val, 0, columns, column.val] ++ extra).length = 5 + extraCount := by
      simp [extraLength]; omega
    rw [headerLength] at copied
    have copied' : Tape.Steps copier (2 * (source.val + target.val + columns + column.val + 5 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5)
        (Tape.configuration copyEntry [] (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++ suffix))
        (Tape.configuration (.inr (.inl .halt)) []
          (word (List.ofFn bits) ++ UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++ suffix)) := by
      simpa [copier, copyEntry, suffix, UnaryMachine.fields, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using copied
    obtain ⟨finalScalar, scaleTicks, scaleCost, scaled, equivalent⟩ :=
      scaleRuns rows columns matrix source target (column.val :: extra) (by simp [extraLength, Nat.add_comm])
        (by
          have columnBound := column.isLt
          have extraCost := extraBounded
          simp [UnaryMachine.fields_length] at extraCost
          simp [assignment]; omega) coefficient coefficient right
    have scaled' : Tape.Steps scaler scaleTicks
        (Tape.configuration scaleEntry []
          (word (List.ofFn bits) ++ UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++ suffix))
        (Tape.configuration scaleExit [] (UnaryMachine.fields ([source.val, target.val, 0, columns, column.val] ++ extra) ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 ::
              (word (List.ofFn (fun index : Fin matrixWidth =>
                (encode field rows columns (MatrixOperations.scaleRow matrix target coefficient)).getLsbD index.val)) ++ right)))) := by
      simpa only [suffix, bits, matrixWidth, payload, List.cons_append, List.nil_append, List.append_assoc] using scaled
    have swapHalt (symbol : Symbol) : swapper swapExit symbol = none := by
      simp [swapper, swapExit, HeaderMoveMachine.halt]
    have columnHalt (symbol : Symbol) : columnSwapper columnExit symbol = none := by
      simp [columnSwapper, columnExit, HeaderColumnSwapMachine.halt]
    have swapped' : Tape.Steps swapper firstSwapTicks
        (Tape.configuration swapEntry [] (UnaryMachine.fields ([source.val, target.val, column.val, columns, 0] ++ extra) ++ initialSuffix))
        (Tape.configuration swapExit [] (UnaryMachine.fields ([target.val, source.val, column.val, columns, 0] ++ extra) ++ initialSuffix)) := by
      simpa [swapper, swapEntry, swapExit, UnaryMachine.fields, List.append_assoc] using swapped
    have restored' : Tape.Steps swapper lastSwapTicks
        (Tape.configuration swapEntry [] (UnaryMachine.fields ([target.val, source.val, column.val, columns, 0] ++ extra) ++ suffix))
        (Tape.configuration swapExit [] (UnaryMachine.fields ([source.val, target.val, column.val, columns, 0] ++ extra) ++ suffix)) := by
      simpa [swapper, swapEntry, swapExit, UnaryMachine.fields, List.append_assoc] using restored
    simp only [UnaryMachine.fields_append, List.append_assoc] at swapped' restored' read' copied' scaled'
    have firstTrace := Tape.sequence_steps swapEntry columnsReady columnHalt swapped'
    have firstHalt (symbol : Symbol) : first (.inr swapExit) symbol = none := by
      simp [first, Tape.sequence, swapHalt]
    have secondTrace := Tape.sequence_steps readEntry firstTrace firstHalt read'
    have secondHalt (symbol : Symbol) : second (.inr readExit) symbol = none := by
      simp [second, Tape.sequence, readHalt]
    have thirdTrace := Tape.sequence_steps swapEntry secondTrace secondHalt restored'
    have thirdHalt (symbol : Symbol) : third (.inr swapExit) symbol = none := by
      simp [third, Tape.sequence, swapHalt]
    have fourthTrace := Tape.sequence_steps columnEntry thirdTrace thirdHalt columnsRestored
    have fourthHalt (symbol : Symbol) : fourth (.inr columnExit) symbol = none := by
      simp [fourth, Tape.sequence, columnHalt]
    have fifthTrace := Tape.sequence_steps copyEntry fourthTrace fourthHalt copied'
    have fifthHalt (symbol : Symbol) : fifth (.inr (.inr (.inl .halt))) symbol = none := by
      simp [fifth, copier, Tape.sequence, HeaderScalarMachine.halt]
    have result := Tape.sequence_steps scaleEntry fifthTrace fifthHalt scaled'
    have headerCost : source.val + target.val + column.val + columns + 6 + (UnaryMachine.fields extra).length ≤
        headerBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have targetBound := target.isLt
      have columnBound := column.isLt
      have extraCost := extraBounded
      simp [UnaryMachine.fields_length] at extraCost
      simp [headerBound, assignment]; omega
    have swapCost : firstSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      apply firstSwapCost.trans
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have lastCost : lastSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      apply lastSwapCost.trans
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have firstColumnBound : firstColumnTicks ≤ columnBound.eval (assignment rows columns) := by
      apply firstColumnCost.trans
      simp only [columnBound, SizePolynomial.eval_add, SizePolynomial.eval_mul,
        SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left 640 (Nat.pow_le_pow_left (by omega) 2)
    have lastColumnBound : lastColumnTicks ≤ columnBound.eval (assignment rows columns) := by
      apply lastColumnCost.trans
      simp only [columnBound, SizePolynomial.eval_add, SizePolynomial.eval_mul,
        SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left 640 (Nat.pow_le_pow_left (by omega) 2)
    have copyCost : 2 * (source.val + target.val + columns + column.val + 5 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 ≤
        copyBound.eval (assignment rows columns) := by
      simp only [copyBound, SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    refine ⟨finalScalar, firstColumnTicks + (firstSwapTicks + 1) + (readTicks + 1) +
      (lastSwapTicks + 1) + (lastColumnTicks + 1) +
      (2 * (source.val + target.val + columns + column.val + 5 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 + 1) +
      (scaleTicks + 1), ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, third, fourth, fifth, swapper, swapEntry, swapExit, columnSwapper, columnEntry, columnExit, coefficient,
        initialSuffix, matrixWidth, payload, Tape.configuration, UnaryMachine.fields_append, List.append_assoc] using result
    · intro nonzero
      exact ⟨by simp [MatrixOperations.scaleRow, nonzero], equivalent (inv_ne_zero nonzero)⟩

end RuntimeNormalization

end Polytime1.Examples.MatrixNormalizeRowSaved
