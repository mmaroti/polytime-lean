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

import Polytime1.Examples.MatrixRowScale
import Polytime1.HeaderScalarMachine

/-! # Pivot normalization from a runtime matrix entry

Compute the pivot address, read its inverse, reset the traversal counter, copy
the inverse to the coefficient input, and scale the row. Every stage is an
actual tape computation and the polynomial bound includes all stages.
-/

namespace Polytime1.Examples.MatrixNormalizeRow

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section PivotNormalization

/-- Normalize a runtime-selected pivot row using its runtime-selected entry.
The resulting pivot is one and row equivalence holds when the entry is nonzero.
The tape routine itself is total on canonical matrix inputs, including zero pivots. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (column : Fin columns) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let normalized := MatrixOperations.scaleRow matrix row (matrix row column)⁻¹
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns normalized).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [row.val, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [row.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (matrix row column ≠ 0 → normalized row column = 1 ∧ Matrix.RowEquivalent matrix normalized) := by
  obtain ⟨ReadState, finiteRead, inhabitedRead, readEntry, readExit, reader, readBound,
    readHalt, readRuns⟩ := MatrixAccess.realizes_runtime_entry_restored field Inv.inv
  let readerFinite : Fintype ReadState := finiteRead
  let readerInhabited : Inhabited ReadState := inhabitedRead
  obtain ⟨ScaleState, finiteScale, inhabitedScale, scaleEntry, scaleExit, scaler, scaleBound,
    scaleHalt, scaleRuns⟩ := MatrixRowScale.realizes field
  let scalerFinite : Fintype ScaleState := finiteScale
  let scalerInhabited : Inhabited ScaleState := inhabitedScale
  let resetter := HeaderResetMachine.machine 1
  let copier := HeaderScalarMachine.machine 3 field.bitWidth
  let resetEntry : HeaderResetMachine.State 1 := .inl (Fin.last 1)
  let copyEntry : HeaderScalarMachine.State 3 field.bitWidth := .inl (Fin.last 3)
  let first := Tape.sequence reader resetter resetEntry
  let second := Tape.sequence first copier copyEntry
  let resetBound : SizePolynomial Matrices.context :=
    SizePolynomial.parameter (ctx := Matrices.context) .L *
      (SizePolynomial.constant 6 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 4) +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  let copyBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * (SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 3) +
      SizePolynomial.constant (4 * field.bitWidth + 5)
  refine ⟨Sum (Sum (Sum ReadState (HeaderResetMachine.State 1))
    (HeaderScalarMachine.State 3 field.bitWidth)) ScaleState, inferInstance, inferInstance,
    .inl (.inl (.inl readEntry)), .inr scaleExit, Tape.sequence second scaler scaleEntry,
    readBound + resetBound + copyBound + scaleBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, scaleHalt]
  · intro rows columns matrix row column initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let coefficient := (matrix row column)⁻¹
    let bits := BoolTuple.fromBits (field.codec.encode coefficient)
    let suffix := word (List.ofFn bits) ++ 3 ::
      (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    have windowWidth : (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))).length =
        field.bitWidth := by simp [word]
    have windowValid : ∀ symbol ∈ word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))),
        symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row column
      (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))) (data true) right
      windowWidth windowValid (by decide)
    have encoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (matrix row column)⁻¹).getLsbD offset.val) = bits := by
      funext offset
      simp [bits, coefficient, BoolTuple.fromBits]
    rw [encoding] at read
    have read' : Tape.Steps reader readTicks
        (Tape.configuration readEntry [] (UnaryMachine.fields [row.val, column.val, columns] ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
        (Tape.configuration readExit [] (UnaryMachine.fields [row.val, column.val, columns] ++ suffix)) := by
      simpa only [suffix, matrixWidth, payload, List.append_assoc] using read
    have reset := HeaderResetMachine.realizes [row.val] column.val (UnaryMachine.fields [columns] ++ suffix)
    have reset' : Tape.Steps resetter
        (column.val * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2)
        (Tape.configuration resetEntry [] (UnaryMachine.fields [row.val, column.val, columns] ++ suffix))
        (Tape.configuration (.inr (0, 8)) [] (UnaryMachine.fields [row.val, 0, columns] ++ suffix)) := by
      simpa [resetter, resetEntry, UnaryMachine.fields, List.append_assoc] using reset
    have copied := HeaderScalarMachine.realizes [row.val, 0, columns] bits
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have copy' : Tape.Steps copier (2 * (row.val + columns + 3) + 4 * field.bitWidth + 5)
        (Tape.configuration copyEntry [] (UnaryMachine.fields [row.val, 0, columns] ++ suffix))
        (Tape.configuration (.inr (.inl .halt)) []
          (word (List.ofFn bits) ++ UnaryMachine.fields [row.val, 0, columns] ++ suffix)) := by
      simpa [copier, copyEntry, suffix, UnaryMachine.fields, List.append_assoc, Nat.add_assoc] using copied
    obtain ⟨finalScalar, scaleTicks, scaleCost, scaled⟩ := scaleRuns rows columns matrix row coefficient coefficient right
    have scaled' : Tape.Steps scaler scaleTicks
        (Tape.configuration scaleEntry [] (word (List.ofFn bits) ++ UnaryMachine.fields [row.val, 0, columns] ++ suffix))
        (Tape.configuration scaleExit [] (UnaryMachine.fields [row.val, 0, columns] ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 ::
              (word (List.ofFn (fun index : Fin matrixWidth =>
                (encode field rows columns (MatrixOperations.scaleRow matrix row coefficient)).getLsbD index.val)) ++ right)))) := by
      simpa only [suffix, bits, matrixWidth, payload, List.append_assoc] using scaled
    have resetTrace := Tape.sequence_steps resetEntry read' readHalt reset'
    have resetHalt (symbol : Symbol) : first (.inr (.inr (0, 8))) symbol = none := by
      simp [first, resetter, Tape.sequence, HeaderResetMachine.halt]
    have copyTrace := Tape.sequence_steps copyEntry resetTrace resetHalt copy'
    have copyHalt (symbol : Symbol) : second (.inr (.inr (.inl .halt))) symbol = none := by
      simp [second, copier, Tape.sequence, HeaderScalarMachine.halt]
    have result := Tape.sequence_steps scaleEntry copyTrace copyHalt scaled'
    have resetCost : column.val * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2 ≤
        resetBound.eval (assignment rows columns) := by
      have firstCost := Nat.mul_le_mul (Nat.le_of_lt column.isLt)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 6 row.isLt) 4)
      have secondCost := Nat.mul_le_mul_left 2 row.isLt
      change column.val * (6 * (row.val + 1) + 4) ≤ columns * (6 * rows + 4) at firstCost
      change 2 * (row.val + 1) ≤ 2 * rows at secondCost
      simp [resetBound, assignment]
      omega
    have copyCost : 2 * (row.val + columns + 3) + 4 * field.bitWidth + 5 ≤
        copyBound.eval (assignment rows columns) := by
      have rowBound := row.isLt
      simp [copyBound, assignment]; omega
    refine ⟨finalScalar, readTicks +
      (column.val * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2 + 1) +
      (2 * (row.val + columns + 3) + 4 * field.bitWidth + 5 + 1) + (scaleTicks + 1), ?_, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, coefficient, matrixWidth, payload, Tape.configuration, List.append_assoc] using result
    · intro nonzero
      exact ⟨by simp [MatrixOperations.scaleRow, nonzero],
        MatrixOperations.scaleRow_rowEquivalent matrix row _ (inv_ne_zero nonzero)⟩

end PivotNormalization

end Polytime1.Examples.MatrixNormalizeRow
