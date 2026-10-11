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

import Polytime1.Examples.MatrixFrameCombine
import Polytime1.HeaderGuardMachine
import Polytime1.WhileMachine
import Polytime1.HeaderResetMachine

/-! # Combining two runtime-selected rows while retaining caller counters

A guarded column traversal updates the target from the corresponding source
entry while retaining caller counters, including the separate pivot column.
Previously processed columns do not affect later source reads.
-/

namespace Polytime1.Examples.MatrixFrameRowCombine

open Matrices TupleMachine

-- scalarLevel: the fixed mathematical carrier of matrix entries.
universe scalarLevel

noncomputable section RowTraversal

/-- Combine source and target entries across all columns, preserving other
rows and trailing storage. The two runtime row indices may coincide. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target (fun column => operation (matrix source column) (matrix target column))
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, columns, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨MapState, finite, inhabited, mapEntry, mapExit, mapMachine,
    mapBound, mapHalt, mapRuns⟩ := MatrixFrameCombine.realizes_next_column field operation extraCount extraBound
  let mapperFinite : Fintype MapState := finite
  let mapperInhabited : Inhabited MapState := inhabited
  let guard := HeaderGuardMachine.machine 2
  let guardEntry : HeaderGuardMachine.State 2 := (Fin.last 2, false, 0)
  let guardExit : HeaderGuardMachine.State 2 := (0, false, 14)
  let body := Tape.sequence HeaderGuardMachine.consume mapMachine mapEntry
  let bodyEntry : Sum (Fin 3) MapState := .inl 0
  let bodyExit : Sum (Fin 3) MapState := .inr mapExit
  let loop := WhileMachine.machine guard body guardEntry bodyEntry
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .L +
      SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K +
      SizePolynomial.constant 12
  let loopBound : SizePolynomial Matrices.context :=
    (SizePolynomial.parameter (ctx := Matrices.context) .L + 1) *
      (guardBound + mapBound + SizePolynomial.constant 5)
  refine ⟨Sum (Sum (HeaderGuardMachine.State 2) (Sum (Fin 3) MapState)) (Fin 3),
    inferInstance, inferInstance, .inl (.inl guardEntry), .inr 2,
    Tape.sequence loop HeaderGuardMachine.consume 0, loopBound + SizePolynomial.constant 3, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderGuardMachine.consume_halt]
  · intro rows columns matrix source target extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let Value := ℕ × Matrix (Fin rows) (Fin columns) field.Carrier × field.Carrier
    let frame (value : Value) := UnaryMachine.fields ([source.val, target.val, value.1, columns] ++ extra) ++
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode value.2.2))) ++
        3 :: (List.replicate matrixWidth (data true) ++ 4 ::
          (word (List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns value.2.1).getLsbD index.val)) ++ right))
    let condition (value : Value) := decide (value.1 < columns)
    let entryTape (value : Value) := (Tape.configuration () [] (frame value)).Tape
    let resultTape (value : Value) := (Tape.configuration () [] (data (condition value) :: frame value)).Tape
    let advance (value : Value) : Value := if valid : value.1 < columns then
      let column : Fin columns := ⟨value.1, valid⟩
      let replacement := operation (value.2.1 source column) (value.2.1 target column)
      (value.1 + 1, Function.update value.2.1 target (Function.update (value.2.1 target) column replacement), replacement)
      else value
    let invariant (value : Value) := value.1 ≤ columns ∧ ∀ i j,
      value.2.1 i j = if i = target ∧ j.val < value.1 then operation (matrix source j) (matrix i j) else matrix i j
    let initial : Value := (0, matrix, initialScalar)
    have initialValid : invariant initial := by simp [invariant, initial]
    have preserves : ∀ value, invariant value → condition value = true → invariant (advance value) := by
      intro value valid positive
      simp only [condition, decide_eq_true_eq] at positive
      refine ⟨by simp [advance, positive], ?_⟩
      intro i j
      by_cases sameRow : i = target
      · subst i
        by_cases sameColumn : j.val = value.1
        · have equality : j = (⟨value.1, positive⟩ : Fin columns) := Fin.ext sameColumn
          subst j
          have old := valid.2 target ⟨value.1, positive⟩
          have oldSource := valid.2 source ⟨value.1, positive⟩
          simp only [lt_self_iff_false, and_false, ↓reduceIte] at old oldSource
          simp [advance, positive, old, oldSource, Function.update]
        · have unequal : j ≠ (⟨value.1, positive⟩ : Fin columns) := by
            intro equality; exact sameColumn (congrArg Fin.val equality)
          have cutoff : j.val < value.1 + 1 ↔ j.val < value.1 := by omega
          simpa [advance, positive, unequal, cutoff, Function.update] using valid.2 target j
      · simpa [advance, positive, sameRow, Function.update] using valid.2 i j
    have iterates : ∀ count ≤ columns,
        (advance^[count] initial).1 = count ∧ invariant (advance^[count] initial) := by
      intro count
      induction count with
      | zero => intro _; exact ⟨rfl, initialValid⟩
      | succ count hypothesis =>
        intro bounded
        obtain ⟨index, valid⟩ := hypothesis (by omega)
        have positive : count < columns := by omega
        have active : condition (advance^[count] initial) = true := by simp [condition, index, positive]
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply']
          simp [advance, index, positive]
        · simpa only [Function.iterate_succ_apply'] using preserves _ valid active
    have guardRuns : ∀ value, invariant value → ∃ ticks,
        ticks ≤ guardBound.eval (assignment rows columns) ∧
          Tape.Steps guard ticks ⟨guardEntry, entryTape value⟩ ⟨guardExit, resultTape value⟩ := by
      intro value valid
      have trace := HeaderGuardMachine.realizes [source.val, target.val] value.1 columns
        (UnaryMachine.fields extra ++ word (List.ofFn (BoolTuple.fromBits (field.codec.encode value.2.2))) ++
          3 :: (List.replicate matrixWidth (data true) ++ 4 ::
            (word (List.ofFn (fun index : Fin matrixWidth =>
              (encode field rows columns value.2.1).getLsbD index.val)) ++ right))) valid.1
      refine ⟨2 * value.1 ^ 2 + 10 * value.1 + 2 * (UnaryMachine.fields [source.val, target.val]).length + 8, ?_, ?_⟩
      · have square := Nat.pow_le_pow_left valid.1 2
        have sourceBound := source.isLt
        have targetBound := target.isLt
        simp [guardBound, assignment]
        nlinarith [valid.1]
      · simpa [guard, guardEntry, guardExit, entryTape, resultTape, frame, condition, Tape.configuration,
          UnaryMachine.fields, List.append_assoc] using trace
    have bodyRuns : ∀ value, invariant value → condition value = true → ∃ ticks,
        ticks ≤ mapBound.eval (assignment rows columns) + 3 ∧
          Tape.Steps body ticks ⟨bodyEntry, resultTape value⟩ ⟨bodyExit, entryTape (advance value)⟩ := by
      intro value _ positive
      simp only [condition, decide_eq_true_eq] at positive
      let column : Fin columns := ⟨value.1, positive⟩
      obtain ⟨ticks, cost, mapped⟩ := mapRuns rows columns value.2.1 source target column extra extraLength extraBounded value.2.2 right
      have consumed := HeaderGuardMachine.consumes true (frame value)
      have mapped' : Tape.Steps mapMachine ticks
          ⟨mapEntry, entryTape value⟩ ⟨mapExit, entryTape (advance value)⟩ := by
        simp only [entryTape, frame, advance, dite_eq_left positive]
        simpa only [column, matrixWidth, Tape.configuration] using mapped
      have result := Tape.sequence_steps mapEntry consumed HeaderGuardMachine.consume_halt mapped'
      refine ⟨2 + (ticks + 1), by omega, ?_⟩
      simpa [body, bodyEntry, bodyExit, resultTape, condition, positive, Tape.configuration] using result
    have loopResult := WhileMachine.realizes guard body guardEntry guardExit bodyEntry bodyExit
      entryTape resultTape condition advance invariant (guardBound.eval (assignment rows columns))
      (mapBound.eval (assignment rows columns) + 3)
      (by intro symbol; exact HeaderGuardMachine.halt symbol)
      (by intro symbol; simp [body, bodyExit, Tape.sequence, mapHalt])
      (by intro value _; simp [resultTape, Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk])
      preserves guardRuns bodyRuns initial initialValid columns
      (by intro count earlier; simp [condition, (iterates count (by omega)).1, earlier])
      (by simp [condition, (iterates columns le_rfl).1])
    obtain ⟨loopTicks, loopCost, loopTrace, loopHalt⟩ := loopResult
    let final := advance^[columns] initial
    have finalIndex : final.1 = columns := (iterates columns le_rfl).1
    have finalMatrix : final.2.1 = Function.update matrix target (fun column => operation (matrix source column) (matrix target column)) := by
      funext i j
      have shape := (iterates columns le_rfl).2.2 i j
      rw [finalIndex] at shape
      by_cases sameRow : i = target
      · subst i; simpa [j.isLt, Function.update] using shape
      · simpa [sameRow, Function.update] using shape
    have consumed := HeaderGuardMachine.consumes false (frame final)
    have consumed' : Tape.Steps HeaderGuardMachine.consume 2
        ⟨0, resultTape final⟩ ⟨2, entryTape final⟩ := by
      simpa [resultTape, entryTape, condition, finalIndex, Tape.configuration] using consumed
    have result := Tape.sequence_steps_of_halt 0 loopTrace loopHalt consumed'
    refine ⟨final.2.2, loopTicks + (2 + 1), ?_, ?_⟩
    · have boundValue : loopBound.eval (assignment rows columns) =
          (columns + 1) * (guardBound.eval (assignment rows columns) +
            (mapBound.eval (assignment rows columns) + 3) + 2) := by
        simp [loopBound, assignment]; ring
      simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant, boundValue]
      omega
    · simpa [loop, initial, final, entryTape, frame, finalIndex, finalMatrix, matrixWidth,
        BoolTuple.fromBits, Tape.configuration] using result

/-- Combine rows and restore the zero column counter for another traversal. -/
theorem realizes_reset (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) (extraCount : ℕ)
    (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target (fun column => operation (matrix source column) (matrix target column))
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
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨MapState, finite, inhabited, mapEntry, mapExit, mapMachine,
    mapBound, mapHalt, mapRuns⟩ := realizes field operation extraCount extraBound
  let mapperFinite : Fintype MapState := finite
  let mapperInhabited : Inhabited MapState := inhabited
  let resetBound : SizePolynomial Matrices.context :=
    SizePolynomial.parameter (ctx := Matrices.context) .L *
      (SizePolynomial.constant 12 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 4) +
      SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  refine ⟨Sum MapState (HeaderResetMachine.State 2), inferInstance, inferInstance,
    .inl mapEntry, .inr (.inr (0, 8)),
    Tape.sequence mapMachine (HeaderResetMachine.machine 2) (.inl (Fin.last 2)),
    mapBound + resetBound + SizePolynomial.constant 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderResetMachine.halt]
  · intro rows columns matrix source target extra extraLength extraBounded initialScalar right
    dsimp only
    obtain ⟨finalScalar, ticks, cost, mapped⟩ := mapRuns rows columns matrix source target extra extraLength extraBounded initialScalar right
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let updated := Function.update matrix target
      (fun column => operation (matrix source column) (matrix target column))
    let output := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns updated).getLsbD index.val)
    let suffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))
    have reset := HeaderResetMachine.realizes [source.val, target.val] columns (UnaryMachine.fields ([columns] ++ extra) ++ suffix)
    have reset' : Tape.Steps (HeaderResetMachine.machine 2)
        (columns * (6 * (source.val + target.val + 2) + 4) + 2 * (source.val + target.val + 2) + 2)
        (Tape.configuration (.inl (Fin.last 2)) [] (UnaryMachine.fields ([source.val, target.val, columns, columns] ++ extra) ++ suffix))
        (Tape.configuration (.inr (0, 8)) [] (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++ suffix)) := by
      simpa [UnaryMachine.fields, List.append_assoc, Nat.add_assoc] using reset
    simp only [List.append_assoc] at mapped
    have result := Tape.sequence_steps (Sum.inl (Fin.last 2) : HeaderResetMachine.State 2)
      mapped mapHalt reset'
    have resetCost : columns * (6 * (source.val + target.val + 2) + 4) + 2 * (source.val + target.val + 2) + 2 ≤
        resetBound.eval (assignment rows columns) := by
      have prefixBound : source.val + target.val + 2 ≤ 2 * rows := by
        have sourceBound := source.isLt
        have targetBound := target.isLt
        omega
      have first := Nat.mul_le_mul_left columns
        (Nat.add_le_add_right (Nat.mul_le_mul_left 6 prefixBound) 4)
      have second := Nat.mul_le_mul_left 2 prefixBound
      simp [resetBound, assignment]
      nlinarith [first, second]
    refine ⟨finalScalar, ticks +
      (columns * (6 * (source.val + target.val + 2) + 4) + 2 * (source.val + target.val + 2) + 2 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [matrixWidth, updated, output, suffix, Tape.configuration, List.append_assoc] using result

/-- Traverse a row while retaining the separate runtime pivot-column counter. -/
theorem realizes_preserving_pivot_column (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (pivotColumn : Fin columns)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let updated := Function.update matrix target (fun column => operation (matrix source column) (matrix target column))
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [source.val, target.val, 0, columns, pivotColumn.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val, 0, columns, pivotColumn.val] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_reset field operation 1 (SizePolynomial.parameter (ctx := Matrices.context) .L + 1)
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target pivotColumn initialScalar right
  have storage : (UnaryMachine.fields [pivotColumn.val]).length ≤
      (SizePolynomial.parameter (ctx := Matrices.context) .L + 1).eval (assignment rows columns) := by
    simp [assignment]
  simpa only [List.cons_append, List.nil_append] using runs rows columns matrix source target
    [pivotColumn.val] rfl storage initialScalar right

end RowTraversal

end Polytime1.Examples.MatrixFrameRowCombine
