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

import Polytime.Examples.MatrixRowAdd
import Polytime.HeaderScalarMachine
import Polytime.HeaderMoveMachine

/-! # Clearing one target entry using a normalized pivot row

The coefficient is read from the target matrix entry on tape. Negation,
row-counter relocation, column reset, scalar copying, and row addition are
composed as actual tape computations with one polynomial bound.
-/

namespace Polytime.Examples.MatrixClearRow

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeElimination

/-- Subtract the target pivot-column entry times the source row. The source
and target indices are restored and the traversal column counter is reset.
A normalized source pivot clears the target entry; distinct rows preserve row equivalence. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (column : Fin columns) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target
            (fun index => matrix target index + -matrix target column * matrix source index)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, target.val, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (matrix source column = 1 → updated target column = 0) ∧
            (source ≠ target → Matrix.RowEquivalent matrix updated) := by
  classical
  obtain ⟨ReadState, readFinite, readInhabited, readEntry, readExit, reader, readBound,
    readHalt, readRuns⟩ := MatrixPairAccess.realizes_runtime_entry_restored field Neg.neg
  let readerFinite : Fintype ReadState := readFinite
  let readerInhabited : Inhabited ReadState := readInhabited
  obtain ⟨AddState, addFinite, addInhabited, addEntry, addExit, adder, addBound,
    addHalt, addRuns⟩ := MatrixRowAdd.realizes field
  let adderFinite : Fintype AddState := addFinite
  let adderInhabited : Inhabited AddState := addInhabited
  let swapper := HeaderMoveMachine.machine 1
  let swapEntry : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inl (Fin.last 1, 0)
  let swapExit : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inr (.inr (.inr (0, 7)))
  let resetter := HeaderResetMachine.machine 2
  let resetEntry : HeaderResetMachine.State 2 := .inl (Fin.last 2)
  let copier := HeaderScalarMachine.machine 4 field.bitWidth
  let copyEntry : HeaderScalarMachine.State 4 field.bitWidth := .inl (Fin.last 4)
  let first := Tape.sequence swapper reader readEntry
  let second := Tape.sequence first resetter resetEntry
  let third := Tape.sequence second swapper swapEntry
  let fourth := Tape.sequence third copier copyEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 5
  let swapBound := SizePolynomial.constant 128 * headerBound ^ 2
  let resetBound : SizePolynomial Matrices.context :=
    SizePolynomial.parameter (ctx := Matrices.context) .L *
      (SizePolynomial.constant 12 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 4) +
      SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  let copyBound := SizePolynomial.constant 2 * headerBound + SizePolynomial.constant (4 * field.bitWidth + 5)
  refine ⟨Sum (Sum (Sum (Sum (Sum _ ReadState) (HeaderResetMachine.State 2)) _)
      (HeaderScalarMachine.State 4 field.bitWidth)) AddState,
    inferInstance, inferInstance, .inl (.inl (.inl (.inl (.inl swapEntry)))), .inr addExit,
    Tape.sequence fourth adder addEntry,
    readBound + resetBound + SizePolynomial.constant 2 * swapBound + copyBound + addBound + SizePolynomial.constant 5,
    ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, addHalt]
  · intro rows columns matrix source target column initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let coefficient := -matrix target column
    let bits := BoolTuple.fromBits (field.codec.encode coefficient)
    let initialSuffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let suffix := word (List.ofFn bits) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    obtain ⟨firstSwapTicks, firstSwapCost, swapped⟩ :=
      HeaderMoveMachine.swaps_row_indices source.val target.val column.val columns initialSuffix
    have width : (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))).length =
        field.bitWidth := by simp [word]
    have scalarValid : ∀ symbol ∈ word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))),
        symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix target source.castSucc column
      (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))) (data true) right
      width scalarValid (by decide)
    have encoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (-matrix target column)).getLsbD offset.val) = bits := by
      funext offset; simp [bits, coefficient, BoolTuple.fromBits]
    simp only [Fin.val_castSucc] at read
    rw [encoding] at read
    have read' : Tape.Steps reader readTicks
        (Tape.configuration readEntry [] (UnaryMachine.fields [target.val, source.val, column.val, columns] ++ initialSuffix))
        (Tape.configuration readExit [] (UnaryMachine.fields [target.val, source.val, column.val, columns] ++ suffix)) := by
      simpa only [initialSuffix, suffix, matrixWidth, payload, List.append_assoc] using read
    have reset := HeaderResetMachine.realizes [target.val, source.val] column.val
      (UnaryMachine.fields [columns] ++ suffix)
    have reset' : Tape.Steps resetter
        (column.val * (6 * (target.val + source.val + 2) + 4) + 2 * (target.val + source.val + 2) + 2)
        (Tape.configuration resetEntry [] (UnaryMachine.fields [target.val, source.val, column.val, columns] ++ suffix))
        (Tape.configuration (.inr (0, 8)) [] (UnaryMachine.fields [target.val, source.val, 0, columns] ++ suffix)) := by
      simpa [resetter, resetEntry, UnaryMachine.fields, List.append_assoc, Nat.add_assoc] using reset
    obtain ⟨lastSwapTicks, lastSwapCost, restored⟩ :=
      HeaderMoveMachine.swaps_row_indices target.val source.val 0 columns suffix
    have copied := HeaderScalarMachine.realizes [source.val, target.val, 0, columns] bits
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have copied' : Tape.Steps copier (2 * (source.val + target.val + columns + 4) + 4 * field.bitWidth + 5)
        (Tape.configuration copyEntry [] (UnaryMachine.fields [source.val, target.val, 0, columns] ++ suffix))
        (Tape.configuration (.inr (.inl .halt)) []
          (word (List.ofFn bits) ++ UnaryMachine.fields [source.val, target.val, 0, columns] ++ suffix)) := by
      simpa [copier, copyEntry, suffix, UnaryMachine.fields, List.append_assoc, Nat.add_assoc] using copied
    obtain ⟨finalScalar, addTicks, addCost, added, equivalent⟩ :=
      addRuns rows columns matrix source target coefficient coefficient right
    have added' : Tape.Steps adder addTicks
        (Tape.configuration addEntry []
          (word (List.ofFn bits) ++ UnaryMachine.fields [source.val, target.val, 0, columns] ++ suffix))
        (Tape.configuration addExit [] (UnaryMachine.fields [source.val, target.val, 0, columns] ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 ::
              (word (List.ofFn (fun index : Fin matrixWidth =>
                (encode field rows columns (Function.update matrix target
                  (fun index => matrix target index + coefficient * matrix source index))).getLsbD index.val)) ++ right)))) := by
      simpa only [suffix, bits, matrixWidth, payload, List.append_assoc] using added
    have swapHalt (symbol : Symbol) : swapper swapExit symbol = none := by
      simp [swapper, swapExit, HeaderMoveMachine.halt]
    have firstTrace := Tape.sequence_steps readEntry swapped swapHalt read'
    have firstHalt (symbol : Symbol) : first (.inr readExit) symbol = none := by
      simp [first, Tape.sequence, readHalt]
    have secondTrace := Tape.sequence_steps resetEntry firstTrace firstHalt reset'
    have secondHalt (symbol : Symbol) : second (.inr (.inr (0, 8))) symbol = none := by
      simp [second, resetter, Tape.sequence, HeaderResetMachine.halt]
    have thirdTrace := Tape.sequence_steps swapEntry secondTrace secondHalt restored
    have thirdHalt (symbol : Symbol) : third (.inr swapExit) symbol = none := by
      simp [third, Tape.sequence, swapHalt]
    have fourthTrace := Tape.sequence_steps copyEntry thirdTrace thirdHalt copied'
    have fourthHalt (symbol : Symbol) : fourth (.inr (.inr (.inl .halt))) symbol = none := by
      simp [fourth, copier, Tape.sequence, HeaderScalarMachine.halt]
    have result := Tape.sequence_steps addEntry fourthTrace fourthHalt added'
    have headerCost : source.val + target.val + column.val + columns + 5 ≤
        headerBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have targetBound := target.isLt
      have columnBound := column.isLt
      simp [headerBound, assignment]; omega
    have swapCost : firstSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      apply firstSwapCost.trans
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left headerCost 2)
    have lastCost : lastSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      apply lastSwapCost.trans
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_pow]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have resetCost : column.val * (6 * (target.val + source.val + 2) + 4) + 2 * (target.val + source.val + 2) + 2 ≤
        resetBound.eval (assignment rows columns) := by
      have prefixBound : target.val + source.val + 2 ≤ 2 * rows := by
        have sourceBound := source.isLt
        have targetBound := target.isLt
        omega
      have firstCost := Nat.mul_le_mul (Nat.le_of_lt column.isLt)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 6 prefixBound) 4)
      have secondCost := Nat.mul_le_mul_left 2 prefixBound
      simp [resetBound, assignment]; nlinarith
    have copyCost : 2 * (source.val + target.val + columns + 4) + 4 * field.bitWidth + 5 ≤
        copyBound.eval (assignment rows columns) := by
      simp only [copyBound, SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    refine ⟨finalScalar, firstSwapTicks + (readTicks + 1) +
      (column.val * (6 * (target.val + source.val + 2) + 4) + 2 * (target.val + source.val + 2) + 2 + 1) +
      (lastSwapTicks + 1) + (2 * (source.val + target.val + columns + 4) + 4 * field.bitWidth + 5 + 1) +
      (addTicks + 1), ?_, ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, third, fourth, swapper, swapEntry, swapExit, coefficient,
        initialSuffix, matrixWidth, payload, Tape.configuration, List.append_assoc] using result
    · intro normalized; simp [Function.update, normalized]
    · exact equivalent

end RuntimeElimination

end Polytime.Examples.MatrixClearRow
