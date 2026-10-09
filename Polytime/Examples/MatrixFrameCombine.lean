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

import Polytime.Examples.MatrixFrameWrite
import Polytime.FiniteDispatchMachine
import Polytime.HeaderScalarMachine
import Polytime.HeaderIncrementMachine
import Polytime.HeaderMoveMachine

/-! # Combining source and target entries in one runtime column

Read the source, exchange the runtime row counters, copy the source scalar to
a leading selector, compute and store the binary operation at the target,
then restore the original counter order. Additional caller counters survive.
Neither row is a specialization input.
-/

namespace Polytime.Examples.MatrixFrameCombine

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeEntries

/-- Update the target entry using a fixed binary operation on two runtime
entries in the same column, preserving the original header and frame suffix.
For row addition, use `fun source target => target + coefficient * source`;
the coefficient is fixed here, while both entries and row indices are runtime data. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
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
          let replacement := operation (matrix source column) (matrix target column)
          let updated := Function.update matrix target (Function.update (matrix target) column replacement)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  classical
  obtain ⟨ReadState, readFinite, readInhabited, readEntry, readExit, reader, readBound,
    readHalt, readRuns⟩ := MatrixFrameAccess.realizes_runtime_entry_restored field id extraCount extraBound
  let readerFinite : Fintype ReadState := readFinite
  let readerInhabited : Inhabited ReadState := readInhabited
  let Bits := Fin field.bitWidth → Bool
  let decoded (bits : Bits) := (field.codec.decode (BoolTuple.toBits bits)).getD 0
  have realizations := fun bits : Bits => MatrixFrameWrite.realizes_entry_map field (operation (decoded bits)) extraCount extraBound
  choose Branch branchFinite branchInhabited entries exits branches bounds halts runs using realizations
  let familyFinite : ∀ bits, Fintype (Branch bits) := branchFinite
  let familyInhabited : ∀ bits, Inhabited (Branch bits) := branchInhabited
  let uniformBound : SizePolynomial Matrices.context := ∑ bits : Bits, bounds bits
  let swapper := HeaderMoveMachine.machine 1
  let swapEntry : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inl (Fin.last 1, 0)
  let swapExit : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inr (.inr (.inr (0, 7)))
  let copier := HeaderScalarMachine.machine (4 + extraCount) field.bitWidth
  let copyEntry : HeaderScalarMachine.State (4 + extraCount) field.bitWidth := .inl (Fin.last (4 + extraCount))
  let dispatcher := FiniteDispatchMachine.machine branches entries
  let dispatchEntry : FiniteDispatchMachine.State Branch := .inl (0, (fun _ => false), 0)
  let first := Tape.sequence reader swapper swapEntry
  let second := Tape.sequence first copier copyEntry
  let third := Tape.sequence second dispatcher dispatchEntry
  let headerBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 4 + extraBound
  let swapBound := SizePolynomial.constant 128 * (headerBound + 1) ^ 2
  let copyBound := SizePolynomial.constant 2 * headerBound + SizePolynomial.constant (4 * field.bitWidth + 5)
  refine ⟨Sum (Sum (Sum (Sum ReadState _) _) _) _, inferInstance, inferInstance,
    .inl (.inl (.inl (.inl readEntry))), .inr swapExit, Tape.sequence third swapper swapEntry,
    readBound + SizePolynomial.constant 2 * swapBound + copyBound + uniformBound +
      SizePolynomial.constant (4 * field.bitWidth + 8), ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, swapper, swapExit, HeaderMoveMachine.halt]
  · intro rows columns matrix source target column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let selector := BoolTuple.fromBits (field.codec.encode (matrix source column))
    let oldSuffix := word (List.ofFn selector) ++ 3 ::
      (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let replacement := operation (matrix source column) (matrix target column)
    let updated := Function.update matrix target (Function.update (matrix target) column replacement)
    let output := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns updated).getLsbD index.val)
    let newSuffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))) ++ 3 ::
      (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))
    have windowWidth : (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))).length =
        field.bitWidth := by simp [word]
    have scalarValid (bits : Bits) : ∀ symbol ∈ word (List.ofFn bits), symbol ≠ 3 ∧ symbol ≠ 6 := by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol; cases bit <;> decide
    obtain ⟨readTicks, readCost, read⟩ := readRuns rows columns matrix source target.castSucc column
      extra extraLength extraBounded (word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar)))) (data true) right
      windowWidth (scalarValid _) (by decide)
    have encoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (id (matrix source column))).getLsbD offset.val) = selector := by
      funext offset; simp [selector, BoolTuple.fromBits]
    simp only [Fin.val_castSucc] at read
    rw [encoding] at read
    have read' : Tape.Steps reader readTicks
        (Tape.configuration readEntry [] (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++
          word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++ 3 ::
            (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
        (Tape.configuration readExit [] (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++ oldSuffix)) := by
      simpa only [oldSuffix, matrixWidth, payload, List.append_assoc] using read
    obtain ⟨firstSwapTicks, firstSwapCost, swapped⟩ :=
      HeaderMoveMachine.swaps_row_indices source.val target.val column.val columns (UnaryMachine.fields extra ++ oldSuffix)
    have copied := HeaderScalarMachine.realizes ([target.val, source.val, column.val, columns] ++ extra) selector
      (3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))
    have headerLength : ([target.val, source.val, column.val, columns] ++ extra).length = 4 + extraCount := by
      simp [extraLength]; omega
    rw [headerLength] at copied
    have copied' : Tape.Steps copier
        (2 * (target.val + source.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5)
        (Tape.configuration copyEntry [] (UnaryMachine.fields ([target.val, source.val, column.val, columns] ++ extra) ++ oldSuffix))
        (Tape.configuration (.inr (.inl .halt)) []
          (word (List.ofFn selector) ++ UnaryMachine.fields ([target.val, source.val, column.val, columns] ++ extra) ++ oldSuffix)) := by
      simpa [copier, copyEntry, oldSuffix, UnaryMachine.fields, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using copied
    have selected : decoded selector = matrix source column := by
      simp [decoded, selector, field.codec.decode_encode]
    obtain ⟨branchTicks, branchCost, mapped⟩ := runs selector rows columns matrix target source column
      extra extraLength extraBounded (word (List.ofFn selector)) (data true) right (by simp [word]) (scalarValid _) (by decide)
    rw [selected] at mapped
    have resultEncoding : (fun offset : Fin field.bitWidth =>
        (field.codec.encode (operation (matrix source column) (matrix target column))).getLsbD offset.val) =
        BoolTuple.fromBits (field.codec.encode replacement) := by
      funext offset; simp [replacement, BoolTuple.fromBits]
    rw [resultEncoding] at mapped
    have mapped' : Tape.Steps (branches selector) branchTicks
        (Tape.configuration (entries selector) [] (UnaryMachine.fields ([target.val, source.val, column.val, columns] ++ extra) ++ oldSuffix))
        (Tape.configuration (exits selector) [] (UnaryMachine.fields ([target.val, source.val, column.val, columns] ++ extra) ++ newSuffix)) := by
      simpa only [oldSuffix, newSuffix, replacement, updated, output, matrixWidth, payload, List.append_assoc] using mapped
    simp only [UnaryMachine.fields_append, List.append_assoc] at mapped'
    have dispatched := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      branchTicks _ _ (halts selector) mapped'
    simp only [List.append_assoc] at copied'
    obtain ⟨lastSwapTicks, lastSwapCost, restored⟩ :=
      HeaderMoveMachine.swaps_row_indices target.val source.val column.val columns (UnaryMachine.fields extra ++ newSuffix)
    simp only [UnaryMachine.fields_append, List.append_assoc] at read' copied'
    have firstTrace := Tape.sequence_steps swapEntry read' readHalt swapped
    have firstHalt (symbol : Symbol) : first (.inr swapExit) symbol = none := by
      simp [first, swapper, swapExit, Tape.sequence, HeaderMoveMachine.halt]
    have secondTrace := Tape.sequence_steps copyEntry firstTrace firstHalt copied'
    have secondHalt (symbol : Symbol) : second (.inr (.inr (.inl .halt))) symbol = none := by
      simp [second, copier, Tape.sequence, HeaderScalarMachine.halt]
    have thirdTrace := Tape.sequence_steps dispatchEntry secondTrace secondHalt dispatched
    have thirdHalt (symbol : Symbol) : third (.inr (.inr (.inr ()))) symbol = none := by
      simp [third, dispatcher, Tape.sequence, FiniteDispatchMachine.halt]
    have result := Tape.sequence_steps swapEntry thirdTrace thirdHalt restored
    have headerCost : source.val + target.val + column.val + columns + 4 + (UnaryMachine.fields extra).length ≤
        headerBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have targetBound := target.isLt
      have columnBound := column.isLt
      have extraCost := extraBounded
      simp [UnaryMachine.fields_length] at extraCost
      simp [headerBound, assignment]; omega
    have swapCost : 128 * (source.val + target.val + column.val + columns + 5) ^ 2 ≤
        swapBound.eval (assignment rows columns) := by
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_add, SizePolynomial.eval_one]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have copiedCost : 2 * (target.val + source.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 ≤
        copyBound.eval (assignment rows columns) := by
      simp only [copyBound, SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    have uniformCost : branchTicks ≤ uniformBound.eval (assignment rows columns) := by
      have boundValue : uniformBound.eval (assignment rows columns) =
          ∑ bits : Bits, (bounds bits).eval (assignment rows columns) := by
        simp [uniformBound, SizePolynomial.eval, map_sum]
      rw [boundValue]
      exact branchCost.trans (Finset.single_le_sum
        (f := fun bits : Bits => (bounds bits).eval (assignment rows columns))
        (s := Finset.univ) (by intro bits _; exact Nat.zero_le _) (Finset.mem_univ selector))
    have lastCost : lastSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      have lastSwapCost' : lastSwapTicks ≤ 128 * (source.val + target.val + column.val + columns + 5) ^ 2 := by
        simpa only [Nat.add_comm target.val source.val] using lastSwapCost
      exact lastSwapCost'.trans swapCost
    refine ⟨readTicks + (firstSwapTicks + 1) +
      (2 * (target.val + source.val + column.val + columns + 4 + (UnaryMachine.fields extra).length) + 4 * field.bitWidth + 5 + 1) +
      (4 * field.bitWidth + branchTicks + 4 + 1) + (lastSwapTicks + 1), ?_, ?_⟩
    · have firstCost := firstSwapCost.trans swapCost
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [UnaryMachine.fields_append, first, second, third, swapEntry, swapExit, swapper, dispatchEntry, dispatcher,
        matrixWidth, payload, newSuffix, replacement, updated, output, Tape.configuration, List.append_assoc] using result

/-- Combine one pair of entries and advance the runtime column counter. -/
theorem realizes_next_column (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
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
          let replacement := operation (matrix source column) (matrix target column)
          let updated := Function.update matrix target (Function.update (matrix target) column replacement)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields ([source.val, target.val, column.val + 1, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨MapState, finite, inhabited, mapEntry, mapExit, mapMachine,
    mapBound, mapHalt, mapRuns⟩ := realizes field operation extraCount extraBound
  let mapperFinite : Fintype MapState := finite
  let mapperInhabited : Inhabited MapState := inhabited
  refine ⟨Sum MapState (HeaderIncrementMachine.State 2), inferInstance, inferInstance,
    .inl mapEntry, .inr (.inr (0, 2)),
    Tape.sequence mapMachine (HeaderIncrementMachine.machine 2) (.inl (Fin.last 2)),
    mapBound + SizePolynomial.constant 6 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderIncrementMachine.halt]
  · intro rows columns matrix source target column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let replacement := operation (matrix source column) (matrix target column)
    let scalar := List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))
    let updated := Function.update matrix target (Function.update (matrix target) column replacement)
    let output := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns updated).getLsbD index.val)
    obtain ⟨mapTicks, mapCost, mapped⟩ := mapRuns rows columns matrix source target column extra extraLength extraBounded initialScalar right
    have incremented := HeaderIncrementMachine.realizes [source.val, target.val] column.val
      (UnaryMachine.fields ([columns] ++ extra) ++ word scalar ++
        3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))
    have incremented' : Tape.Steps (HeaderIncrementMachine.machine 2)
        (3 * (source.val + target.val + 2) + 2)
        (Tape.configuration (.inl (Fin.last 2)) []
          (UnaryMachine.fields ([source.val, target.val, column.val, columns] ++ extra) ++ word scalar ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))))
        (Tape.configuration (.inr (0, 2)) []
          (UnaryMachine.fields ([source.val, target.val, column.val + 1, columns] ++ extra) ++ word scalar ++
            3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
      simpa [UnaryMachine.fields, List.append_assoc, Nat.add_assoc] using incremented
    have result := Tape.sequence_steps (Sum.inl (Fin.last 2) : HeaderIncrementMachine.State 2)
      mapped mapHalt incremented'
    refine ⟨mapTicks + (3 * (source.val + target.val + 2) + 2 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_parameter, assignment]
      have sourceBound := source.isLt
      have targetBound := target.isLt
      omega
    · simpa only [Tape.configuration, matrixWidth, scalar, replacement, updated, output] using result

end RuntimeEntries

end Polytime.Examples.MatrixFrameCombine
