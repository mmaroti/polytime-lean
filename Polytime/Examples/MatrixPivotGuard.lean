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

import Polytime.Examples.MatrixEntryTest
import Polytime.HeaderGuardMachine

/-! # A short-circuiting pivot-search guard

Compare the candidate row with the runtime row count before testing the matrix
entry. The end sentinel is never used as a matrix index. A true result means
that the candidate exists and its entry is zero, so search must continue.
-/

namespace Polytime.Examples.MatrixPivotGuard

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeGuard

/-- Test whether pivot search should skip the current candidate. At the row
count sentinel, return false without reading beyond the matrix. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (candidate : ℕ) (_bounded : candidate ≤ rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := if valid : candidate < rows then matrix ⟨candidate, valid⟩ column else initialScalar
          let result := if valid : candidate < rows then decide (matrix ⟨candidate, valid⟩ column = 0) else false
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields ([candidate, rows, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (data result :: (UnaryMachine.fields ([candidate, rows, column.val, columns] ++ extra) ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))) := by
  classical
  obtain ⟨TestState, finite, inhabited, testEntry, testExit, tester, testBound,
    testHalt, testRuns⟩ := MatrixEntryTest.realizes_with_counters field (fun value => decide (value = 0)) extraCount extraBound
  let testerFinite : Fintype TestState := finite
  let testerInhabited : Inhabited TestState := inhabited
  let Bits := Fin 1 → Bool
  let Branch (_bits : Bits) := Sum TestState (FiniteTableMachine.State 0 1)
  let falseTable (_input : Fin 0 → Bool) (_output : Fin 1) := false
  let branches (_bits : Bits) : Turing.TM0.Machine Symbol (Branch _bits) := fun state symbol =>
    match state with
    | .inl next => (tester next symbol).map (fun (state, action) => (Sum.inl state, action))
    | .inr next => (FiniteTableMachine.machine falseTable next symbol).map
        (fun (state, action) => (Sum.inr state, action))
  let entries (bits : Bits) : Branch bits :=
    if bits 0 then .inl testEntry else .inr (.read 0 (fun _ => false))
  let exits (bits : Bits) : Branch bits := if bits 0 then .inl testExit else .inr .halt
  have halts (bits : Bits) (symbol : Symbol) : branches bits (exits bits) symbol = none := by
    cases selected : bits 0 <;> simp [branches, exits, selected, testHalt, FiniteTableMachine.machine]
  let guard := HeaderGuardMachine.machine 0
  let guardEntry : HeaderGuardMachine.State 0 := (Fin.last 0, false, 0)
  let guardExit : HeaderGuardMachine.State 0 := (0, false, 14)
  let guardBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 8
  let dispatcher := FiniteDispatchMachine.machine branches entries
  let dispatchEntry : FiniteDispatchMachine.State Branch := .inl (0, (fun _ => false), 0)
  refine ⟨Sum (HeaderGuardMachine.State 0) (FiniteDispatchMachine.State Branch),
    inferInstance, inferInstance, .inl guardEntry, .inr (.inr (.inr ())),
    Tape.sequence guard dispatcher dispatchEntry,
    guardBound + testBound + SizePolynomial.constant 14, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, dispatcher, FiniteDispatchMachine.halt]
  · intro rows columns matrix candidate bounded column extra extraLength extraBounded initialScalar right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let payload := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let frame (scalar : field.Carrier) := UnaryMachine.fields ([candidate, rows, column.val, columns] ++ extra) ++
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
        (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))
    let scalar := if valid : candidate < rows then matrix ⟨candidate, valid⟩ column else initialScalar
    let result := if valid : candidate < rows then decide (matrix ⟨candidate, valid⟩ column = 0) else false
    let selector : Bits := fun _ => decide (candidate < rows)
    have guarded := HeaderGuardMachine.realizes [] candidate rows
      (UnaryMachine.fields ([column.val, columns] ++ extra) ++
        word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++ 3 ::
          (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))) bounded
    have guarded' : Tape.Steps guard (2 * candidate ^ 2 + 10 * candidate + 8)
        (Tape.configuration guardEntry [] (frame initialScalar))
        (Tape.configuration guardExit [] (word (List.ofFn selector) ++ frame initialScalar)) := by
      simpa [guard, guardEntry, guardExit, selector, frame, word, UnaryMachine.fields, List.append_assoc] using guarded
    have branchRun : ∃ ticks, ticks ≤ testBound.eval (assignment rows columns) + 5 ∧
        Tape.Steps (branches selector) ticks
          (Tape.configuration (entries selector) [] (frame initialScalar))
          (Tape.configuration (exits selector) [] (data result :: frame scalar)) := by
      by_cases valid : candidate < rows
      · obtain ⟨ticks, cost, trace⟩ := testRuns rows columns matrix ⟨candidate, valid⟩
          (Fin.last rows) column extra extraLength extraBounded initialScalar right
        have renamed := trace.rename Sum.inl (targetMachine := branches selector)
          (by intro state symbol next action transition; simp [branches, transition])
        refine ⟨ticks, by omega, ?_⟩
        simpa [entries, exits, selector, valid, frame, scalar, result, matrixWidth, payload,
          Tape.configuration, List.append_assoc] using renamed
      · have emitted := FiniteTableMachine.realizes falseTable (fun _ : Fin 0 => false) (frame initialScalar)
        have renamed := emitted.rename Sum.inr (targetMachine := branches selector)
          (by intro state symbol next action transition; simp [branches, transition])
        refine ⟨5, by omega, ?_⟩
        simpa [entries, exits, selector, valid, frame, scalar, result, falseTable, word,
          Tape.configuration] using renamed
    obtain ⟨ticks, cost, trace⟩ := branchRun
    have dispatched := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      ticks _ _ (halts selector) trace
    have computation := Tape.sequence_steps dispatchEntry guarded'
      (by intro symbol; exact HeaderGuardMachine.halt symbol) dispatched
    have guardCost : 2 * candidate ^ 2 + 10 * candidate + 8 ≤ guardBound.eval (assignment rows columns) := by
      have square := Nat.pow_le_pow_left bounded 2
      simp [guardBound, assignment]; nlinarith
    refine ⟨(2 * candidate ^ 2 + 10 * candidate + 8) + (4 * 1 + ticks + 4 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [guard, guardEntry, dispatcher, dispatchEntry, frame, scalar, result,
        matrixWidth, payload, Tape.configuration] using computation

/-- The search routine with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (candidate : ℕ) (_bounded : candidate ≤ rows) (column : Fin columns)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := if valid : candidate < rows then matrix ⟨candidate, valid⟩ column else initialScalar
          let result := if valid : candidate < rows then decide (matrix ⟨candidate, valid⟩ column = 0) else false
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [candidate, rows, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (data result :: (UnaryMachine.fields [candidate, rows, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix candidate bounded column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix candidate bounded column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeGuard

end Polytime.Examples.MatrixPivotGuard
