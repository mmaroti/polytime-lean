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

import Polytime1.Examples.MatrixRowCombine
import Polytime1.HeaderMoveMachine
import Polytime1.Matrix
import Polytime1.HeaderGuardMachine
import Polytime1.FiniteDispatchMachine

/-! # Swapping distinct runtime rows on tape

Three row traversals perform `b := a + b`, `a := b - a`, and `b := b - a`.
The runtime row counters are exchanged between traversals and restored on exit.
-/

namespace Polytime1.Examples.MatrixRowSwap

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeRows

/-- Swap distinct runtime-selected rows, preserving the surrounding frame and
restoring the column counter to zero, with a polynomial tape bound. -/
theorem realizes_distinct_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (_distinct : source ≠ target) (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.swapRows matrix source target
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated := by
  classical
  obtain ⟨FirstState, firstFinite, firstInhabited, firstEntry, firstExit, firstMachine,
    firstBound, firstHalt, firstRuns⟩ := MatrixFrameRowCombine.realizes_reset field (fun source target => source + target) extraCount extraBound
  obtain ⟨SecondState, secondFinite, secondInhabited, secondEntry, secondExit, secondMachine,
    secondBound, secondHalt, secondRuns⟩ := MatrixFrameRowCombine.realizes_reset field (fun source target => source - target) extraCount extraBound
  obtain ⟨ThirdState, thirdFinite, thirdInhabited, thirdEntry, thirdExit, thirdMachine,
    thirdBound, thirdHalt, thirdRuns⟩ := MatrixFrameRowCombine.realizes_reset field (fun source target => target - source) extraCount extraBound
  let firstControllerFinite : Fintype FirstState := firstFinite
  let firstControllerInhabited : Inhabited FirstState := firstInhabited
  let secondControllerFinite : Fintype SecondState := secondFinite
  let secondControllerInhabited : Inhabited SecondState := secondInhabited
  let thirdControllerFinite : Fintype ThirdState := thirdFinite
  let thirdControllerInhabited : Inhabited ThirdState := thirdInhabited
  let swapper := HeaderMoveMachine.machine 1
  let swapEntry : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inl (Fin.last 1, 0)
  let swapExit : Sum (SizeMachine.Copy.State 1)
      (Sum (HeaderResetMachine.State 2) (HeaderMoveMachine.RemoveZero.State 2)) := .inr (.inr (.inr (0, 7)))
  let first := Tape.sequence firstMachine swapper swapEntry
  let second := Tape.sequence first secondMachine secondEntry
  let third := Tape.sequence second swapper swapEntry
  let swapBound : SizePolynomial Matrices.context := SizePolynomial.constant 128 *
    (SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.parameter (ctx := Matrices.context) .L + SizePolynomial.constant 5) ^ 2
  refine ⟨Sum (Sum (Sum (Sum FirstState _) SecondState) _) ThirdState,
    inferInstance, inferInstance, .inl (.inl (.inl (.inl firstEntry))), .inr thirdExit,
    Tape.sequence third thirdMachine thirdEntry,
    firstBound + secondBound + thirdBound + SizePolynomial.constant 2 * swapBound + SizePolynomial.constant 4,
    ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, thirdHalt]
  · intro rows columns matrix source target distinct extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let firstMatrix := Function.update matrix target (fun column => matrix source column + matrix target column)
    let secondMatrix := Function.update firstMatrix source
      (fun column => firstMatrix target column - firstMatrix source column)
    let thirdMatrix := Function.update secondMatrix target
      (fun column => secondMatrix target column - secondMatrix source column)
    have swappedMatrix : thirdMatrix = MatrixOperations.swapRows matrix source target := by
      funext row column
      by_cases atSource : row = source
      · subst row
        simp [thirdMatrix, secondMatrix, firstMatrix, Function.update, distinct,
          Ne.symm distinct, MatrixOperations.swapRows]
      · by_cases atTarget : row = target
        · subst row
          simp [thirdMatrix, secondMatrix, firstMatrix, Function.update, distinct,
            Ne.symm distinct, MatrixOperations.swapRows]
        · simp [thirdMatrix, secondMatrix, firstMatrix, Function.update, atSource, atTarget,
            MatrixOperations.swapRows, Equiv.swap_apply_of_ne_of_ne atSource atTarget]
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
        3 :: (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    obtain ⟨firstScalar, firstTicks, firstCost, firstTrace⟩ := firstRuns rows columns matrix source target extra extraLength extraBounded initialScalar right
    obtain ⟨firstSwapTicks, firstSwapCost, firstSwapTrace⟩ :=
      HeaderMoveMachine.swaps_row_indices source.val target.val 0 columns (UnaryMachine.fields extra ++ suffix firstMatrix firstScalar)
    simp only [UnaryMachine.fields_append, List.append_assoc] at firstTrace
    have firstResult := Tape.sequence_steps swapEntry firstTrace firstHalt firstSwapTrace
    obtain ⟨secondScalar, secondTicks, secondCost, secondTrace⟩ :=
      secondRuns rows columns firstMatrix target source extra extraLength extraBounded firstScalar right
    have firstStops (symbol : Symbol) : first (.inr swapExit) symbol = none := by
      simp [first, swapper, swapExit, Tape.sequence, HeaderMoveMachine.halt]
    simp only [suffix] at firstResult
    simp only [UnaryMachine.fields_append, List.append_assoc] at secondTrace
    have secondResult := Tape.sequence_steps secondEntry firstResult firstStops secondTrace
    obtain ⟨secondSwapTicks, secondSwapCost, secondSwapTrace⟩ :=
      HeaderMoveMachine.swaps_row_indices target.val source.val 0 columns (UnaryMachine.fields extra ++ suffix secondMatrix secondScalar)
    have secondStops (symbol : Symbol) : second (.inr secondExit) symbol = none := by
      simp [second, Tape.sequence, secondHalt]
    have thirdResult := Tape.sequence_steps swapEntry secondResult secondStops secondSwapTrace
    obtain ⟨thirdScalar, thirdTicks, thirdCost, thirdTrace⟩ :=
      thirdRuns rows columns secondMatrix source target extra extraLength extraBounded secondScalar right
    have thirdStops (symbol : Symbol) : third (.inr swapExit) symbol = none := by
      simp [third, swapper, swapExit, Tape.sequence, HeaderMoveMachine.halt]
    simp only [suffix] at thirdResult
    simp only [UnaryMachine.fields_append, List.append_assoc] at thirdTrace
    have result := Tape.sequence_steps thirdEntry thirdResult thirdStops thirdTrace
    have swapCost : 128 * (source.val + target.val + 0 + columns + 5) ^ 2 ≤
        swapBound.eval (assignment rows columns) := by
      have sourceBound := source.isLt
      have targetBound := target.isLt
      simp only [swapBound, SizePolynomial.eval_mul, SizePolynomial.eval_constant,
        SizePolynomial.eval_pow, SizePolynomial.eval_add, SizePolynomial.eval_parameter, assignment]
      exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (by omega) 2)
    have swappedCost : secondSwapTicks ≤ swapBound.eval (assignment rows columns) := by
      have secondSwapCost' : secondSwapTicks ≤ 128 * (source.val + target.val + 0 + columns + 5) ^ 2 := by
        simpa only [Nat.add_comm target.val source.val] using secondSwapCost
      exact secondSwapCost'.trans swapCost
    refine ⟨thirdScalar, firstTicks + (firstSwapTicks + 1) + (secondTicks + 1) +
      (secondSwapTicks + 1) + (thirdTicks + 1), ?_, ?_, ?_⟩
    · have firstSwapBound := firstSwapCost.trans swapCost
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_constant]
      omega
    · simpa only [first, second, third, swapper, swapEntry, swapExit, matrixWidth,
        suffix, firstMatrix, secondMatrix, thirdMatrix, swappedMatrix, Tape.configuration,
        UnaryMachine.fields_append, List.append_assoc] using result

    · exact MatrixOperations.swapRows_rowEquivalent matrix source target

/-- Swap ordered runtime rows, including the identical-row case via a guard. -/
theorem realizes_ordered_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (_ordered : source.val ≤ target.val) (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.swapRows matrix source target
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated := by
  classical
  obtain ⟨SwapState, finite, inhabited, swapEntry, swapExit, swapMachine,
    swapBound, swapHalt, swapRuns⟩ := realizes_distinct_with_counters field extraCount extraBound
  let swapControllerFinite : Fintype SwapState := finite
  let swapControllerInhabited : Inhabited SwapState := inhabited
  let Bits := Fin 1 → Bool
  let Branch (_bits : Bits) := SwapState
  let branches (bits : Bits) : Turing.TM0.Machine Symbol (Branch bits) :=
    if bits 0 then swapMachine else fun _ _ => none
  let entries (_bits : Bits) : SwapState := swapEntry
  let exits (bits : Bits) : SwapState := if bits 0 then swapExit else swapEntry
  have halts (bits : Bits) (symbol : Symbol) : branches bits (exits bits) symbol = none := by
    cases selected : bits 0 <;> simp [branches, exits, selected, swapHalt]
  let guard := HeaderGuardMachine.machine 0
  let guardEntry : HeaderGuardMachine.State 0 := (Fin.last 0, false, 0)
  let guardExit : HeaderGuardMachine.State 0 := (0, false, 14)
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 8
  refine ⟨Sum (HeaderGuardMachine.State 0) (FiniteDispatchMachine.State Branch),
    inferInstance, inferInstance, .inl guardEntry, .inr (.inr (.inr ())),
    Tape.sequence guard (FiniteDispatchMachine.machine branches entries) (.inl (0, (fun _ => false), 0)),
    guardBound + swapBound + SizePolynomial.constant 9, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, FiniteDispatchMachine.halt]
  · intro rows columns matrix source target ordered extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let suffix (value : Matrix (Fin rows) (Fin columns) field.Carrier) (scalar : field.Carrier) :=
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
        3 :: (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value).getLsbD index.val)) ++ right))
    let selector : Bits := fun _ => decide (source.val < target.val)
    have guarded := HeaderGuardMachine.realizes [] source.val target.val
      (UnaryMachine.fields ([0, columns] ++ extra) ++ suffix matrix initialScalar) ordered
    have guarded' : Tape.Steps guard (2 * source.val ^ 2 + 10 * source.val + 8)
        (Tape.configuration guardEntry []
          (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++ suffix matrix initialScalar))
        (Tape.configuration guardExit []
          (word (List.ofFn selector) ++ UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
            suffix matrix initialScalar)) := by
      simpa [guard, guardEntry, guardExit, selector, word, UnaryMachine.fields, List.append_assoc] using guarded
    have branchRun : ∃ (finalScalar : field.Carrier) (ticks : ℕ),
        ticks ≤ swapBound.eval (assignment rows columns) ∧
          Tape.Steps (branches selector) ticks
            (Tape.configuration (entries selector) []
              (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++ suffix matrix initialScalar))
            (Tape.configuration (exits selector) []
              (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                suffix (MatrixOperations.swapRows matrix source target) finalScalar)) := by
      by_cases distinct : source ≠ target
      · have positive : source.val < target.val := by
          have unequal : source.val ≠ target.val := by
            intro equality; exact distinct (Fin.ext equality)
          omega
        obtain ⟨finalScalar, ticks, cost, trace, _⟩ :=
          swapRuns rows columns matrix source target distinct extra extraLength extraBounded initialScalar right
        refine ⟨finalScalar, ticks, cost, ?_⟩
        simpa only [branches, entries, exits, selector, decide_eq_true positive, Bool.true_eq,
          ↓reduceIte, suffix, matrixWidth, Tape.configuration, List.append_assoc] using trace
      · have equal : source = target := by simpa using distinct
        subst target
        refine ⟨initialScalar, 0, Nat.zero_le _, ?_⟩
        simp only [branches, entries, exits, selector, lt_self_iff_false, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        have equalMatrix : MatrixOperations.swapRows matrix source source = matrix := by
          funext row column
          simp [MatrixOperations.swapRows, Equiv.swap_self]
        rw [equalMatrix]
        exact .zero _
    obtain ⟨finalScalar, ticks, cost, trace⟩ := branchRun
    have dispatched := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      ticks _ _ (halts selector) trace
    have result := Tape.sequence_steps
      (Sum.inl (0, (fun _ => false), 0) : FiniteDispatchMachine.State Branch)
      guarded' (by intro symbol; exact HeaderGuardMachine.halt symbol) dispatched
    refine ⟨finalScalar, (2 * source.val ^ 2 + 10 * source.val + 8) + (4 * 1 + ticks + 4 + 1), ?_, ?_, ?_⟩
    · have sourceBound : source.val ≤ rows := Nat.le_of_lt source.isLt
      have square := Nat.pow_le_pow_left sourceBound 2
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      have guardCost : 2 * source.val ^ 2 + 10 * source.val + 8 ≤ guardBound.eval (assignment rows columns) := by
        simp [guardBound, assignment]; nlinarith
      omega
    · simpa only [guard, guardEntry, suffix, matrixWidth, Tape.configuration, List.append_assoc] using result
    · exact MatrixOperations.swapRows_rowEquivalent matrix source target

/-- The row swap with no additional header counters. -/
theorem realizes_distinct (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (_distinct : source ≠ target) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.swapRows matrix source target
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_distinct_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target hypothesis initialScalar right
  simpa only [List.append_nil] using
    runs rows columns matrix source target hypothesis [] rfl
      (by simp [UnaryMachine.fields]) initialScalar right


/-- The row swap with no additional header counters. -/
theorem realizes_ordered (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (_ordered : source.val ≤ target.val) (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := MatrixOperations.swapRows matrix source target
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            Matrix.RowEquivalent matrix updated := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_ordered_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target hypothesis initialScalar right
  simpa only [List.append_nil] using
    runs rows columns matrix source target hypothesis [] rfl
      (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeRows

end Polytime1.Examples.MatrixRowSwap
