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

import Polytime1.Examples.MatrixPairAccess
import Polytime1.HeaderScalarMachine
import Polytime1.FiniteDispatchMachine

/-! # Testing a runtime matrix entry

Read an entry, copy its canonical scalar to a leading selector, and dispatch
on that fixed-width selector to prepend a Boolean. The matrix is preserved.
Pivot search uses this routine with the predicate that the entry is zero.
-/

namespace Polytime1.Examples.MatrixEntryTest

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeTest

/-- A fixed scalar predicate becomes a Boolean result before the restored
runtime header. All matrix entries and trailing caller storage are preserved. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (predicate : field.Carrier → Bool)
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := matrix row column
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (data (predicate scalar) :: (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))) := by
  classical
  obtain ⟨ReadState, finite, inhabited, readEntry, readExit, reader, readBound,
    readHalt, readRuns⟩ := MatrixFrameAccess.realizes_runtime_entry_restored field id extraCount extraBound
  let readerFinite : Fintype ReadState := finite
  let readerInhabited : Inhabited ReadState := inhabited
  let Bits := Fin field.bitWidth → Bool
  let decoded (bits : Bits) := (field.codec.decode (BoolTuple.toBits bits)).getD 0
  let table (bits : Bits) (_input : Fin 0 → Bool) (_output : Fin 1) := predicate (decoded bits)
  let Branch (_bits : Bits) := FiniteTableMachine.State 0 1
  let branches (bits : Bits) : Turing.TM0.Machine Symbol (Branch bits) := FiniteTableMachine.machine (table bits)
  let entries (_bits : Bits) : Branch _bits := .read 0 (fun _ => false)
  let dispatcher := FiniteDispatchMachine.machine branches entries
  let dispatchEntry : FiniteDispatchMachine.State Branch := .inl (0, (fun _ => false), 0)
  let copier := HeaderScalarMachine.machine (4 + extraCount) field.bitWidth
  let copyEntry : HeaderScalarMachine.State (4 + extraCount) field.bitWidth := .inl (Fin.last (4 + extraCount))
  let first := Tape.sequence reader copier copyEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 4 + extraBound
  let copyBound := SizePolynomial.constant 2 * headerBound + SizePolynomial.constant (4 * field.bitWidth + 5)
  refine ⟨Sum (Sum ReadState (HeaderScalarMachine.State (4 + extraCount) field.bitWidth)) (FiniteDispatchMachine.State Branch),
    inferInstance, inferInstance, .inl (.inl readEntry), .inr (.inr (.inr ())),
    Tape.sequence first dispatcher dispatchEntry,
    readBound + copyBound + SizePolynomial.constant (4 * field.bitWidth + 11), ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, dispatcher, FiniteDispatchMachine.halt]
  · intro rows columns matrix row otherRow column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let selector := BoolTuple.fromBits (field.codec.encode (matrix row column))
    let suffix := word (List.ofFn selector) ++ 3 ::
      (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let frame := UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++ suffix
    have width : (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))).length =
        field.bitWidth := by simp [word]
    have scalarValid : ∀ symbol ∈ word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))),
        symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix row otherRow column extra extraLength extraBounded
      (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))) (data true) right
      width scalarValid (by decide)
    have encoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (id (matrix row column))).getLsbD offset.val) = selector := by
      funext offset; simp [selector, BoolTuple.fromBits]
    rw [encoding] at read
    have read' : Tape.Steps reader readTicks
        (Tape.configuration readEntry [] (UnaryMachine.fields ([row.val, otherRow.val, column.val, columns] ++ extra) ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
        (Tape.configuration readExit [] frame) := by
      simpa only [frame, suffix, matrixWidth, payload, List.append_assoc] using read
    have copied := HeaderScalarMachine.realizes ([row.val, otherRow.val, column.val, columns] ++ extra) selector
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have headerLength : ([row.val, otherRow.val, column.val, columns] ++ extra).length = 4 + extraCount := by
      simp [extraLength]; omega
    rw [headerLength] at copied
    have copied' : Tape.Steps copier
        (2 * (row.val + otherRow.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5)
        (Tape.configuration copyEntry [] frame)
        (Tape.configuration (.inr (.inl .halt)) [] (word (List.ofFn selector) ++ frame)) := by
      simpa [copier, copyEntry, frame, suffix, UnaryMachine.fields, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using copied
    have selected : decoded selector = matrix row column := by
      simp [decoded, selector, field.codec.decode_encode]
    have emitted := FiniteTableMachine.realizes (table selector) (fun _ : Fin 0 => false) frame
    have emitted' : Tape.Steps (branches selector) 5
        (Tape.configuration (entries selector) [] frame)
        (Tape.configuration .halt [] (data (predicate (matrix row column)) :: frame)) := by
      simpa [branches, entries, table, selected, word] using emitted
    have dispatched := FiniteDispatchMachine.realizes branches entries selector .halt 5 frame
      (data (predicate (matrix row column)) :: frame)
      (by intro symbol; rfl) emitted'
    have copiedTrace := Tape.sequence_steps copyEntry read' readHalt copied'
    have copiedHalt (symbol : Symbol) : first (.inr (.inr (.inl .halt))) symbol = none := by
      simp [first, copier, Tape.sequence, HeaderScalarMachine.halt]
    have result := Tape.sequence_steps dispatchEntry copiedTrace copiedHalt dispatched
    have copyCost : 2 * (row.val + otherRow.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 ≤
        copyBound.eval (assignment rows columns) := by
      have rowBound := row.isLt
      have otherBound := otherRow.isLt
      have columnBound := column.isLt
      have extraCost := extraBounded
      simp [UnaryMachine.fields_length] at extraCost
      simp [copyBound, headerBound, assignment]; omega
    refine ⟨readTicks +
      (2 * (row.val + otherRow.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 + 1) +
      (4 * field.bitWidth + 5 + 4 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, copier, copyEntry, dispatcher, dispatchEntry, frame, suffix,
        selector, matrixWidth, payload, Tape.configuration, List.append_assoc] using result

/-- Test an entry with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (predicate : field.Carrier → Bool) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := matrix row column
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (data (predicate scalar) :: (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field predicate 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix row otherRow column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix row otherRow column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeTest

end Polytime1.Examples.MatrixEntryTest
