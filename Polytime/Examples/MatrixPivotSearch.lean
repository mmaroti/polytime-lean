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

import Polytime.Examples.MatrixSearch

/-! # Pivot search by a guarded runtime row traversal

The loop skips zero entries, stops at the first nonzero entry or the row-count
sentinel, erases the final guard bit, and preserves the matrix and column.
The iteration count appears only in the proof, never as execution fuel.
-/

namespace Polytime.Examples.MatrixPivotSearch

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeSearch

/-- Search a column from a runtime starting row. The returned counter is the
first eligible nonzero row, or the row count if every eligible entry is zero.
The mathematical contract includes minimality and a polynomial tape bound. -/
theorem realizes_with_counters (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (start : ℕ) (_bounded : start ≤ rows) (column : Fin columns)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          ∃ (candidate : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields ([start, rows, column.val, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([candidate, rows, column.val, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) ∧
            start ≤ candidate ∧ candidate ≤ rows ∧
            (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
            (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
            GaussJordan.findPivot matrix start column =
              (if valid : candidate < rows then some ⟨candidate, valid⟩ else none) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixSearch.contract field extraCount extraBound
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix start bounded column extra extraLength extraBounded initialScalar right
  let sizes := assignment rows columns
  let caller : MatrixSearch.Environment extraCount extraBound sizes :=
    (⟨extra, extraLength, extraBounded⟩, right)
  let initial : MatrixSearch.Value field sizes := (start, column, matrix)
  obtain ⟨final, finalTape, ticks, cost, trace, correct, represented⟩ :=
    runs sizes caller initial _ bounded ⟨initialScalar, rfl⟩
  obtain ⟨finalScalar, equal⟩ := represented
  rw [equal] at trace
  refine ⟨final.1, finalScalar, ticks, cost, ?_, correct.2⟩
  dsimp only [MatrixSearch.frame] at trace
  rw [correct.1] at trace
  dsimp only [initial, sizes, caller, assignment, Tape.configuration] at trace
  simpa only [Tape.configuration, List.append_assoc] using trace

/-- The search routine with no additional header counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (start : ℕ) (_bounded : start ≤ rows) (column : Fin columns)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          ∃ (candidate : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [start, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [candidate, rows, column.val, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) ∧
            start ≤ candidate ∧ candidate ≤ rows ∧
            (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
            (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
            GaussJordan.findPivot matrix start column =
              (if valid : candidate < rows then some ⟨candidate, valid⟩ else none) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_with_counters field 0 0
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix start bounded column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix start bounded column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeSearch

end Polytime.Examples.MatrixPivotSearch
