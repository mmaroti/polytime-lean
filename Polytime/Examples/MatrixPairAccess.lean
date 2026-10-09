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

import Polytime.Examples.MatrixFrameAccess

/-! # Indexed scalar reads retaining two runtime row indices

The first row counter selects the entry. The second row counter is preserved
across address evaluation, lookup, scalar transformation, and scratch cleanup.
-/

namespace Polytime.Examples.MatrixPairAccess

open Matrices TupleMachine

-- scalarLevel: the fixed mathematical carrier of matrix entries.
universe scalarLevel

noncomputable section PairedRowAccess

/-- A controller fixed by the scalar presentation computes a runtime row-major
address and reads the canonical matrix entry. The retained second counter may
equal the row count. The input counters and evaluator
scratch survive. Reserved output and binary windows are the entry requirements. -/
theorem realizes_runtime_entry (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
    ∃ (scratch : List (SizeExpression MatrixPairAddress.context)) (Controller : Type)
      (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns) (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (matrix row column)).getLsbD offset.val)
          let retained := UnaryMachine.fields
            (scratch.map (·.eval (MatrixPairAddress.assignment row.val otherRow.val column.val columns))) ++
              UnaryMachine.fields [row.val, otherRow.val, column.val, columns]
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit
              (retained.reverse ++ 6 :: (List.replicate ((row.val * columns + column.val) * field.bitWidth) 0 ++ [7]))
              (word scalar ++ 3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨scratch, Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameAccess.realizes_runtime_entry field 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨scratch, Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix row otherRow column window inputSymbol right windowWidth windowValid inputValid
  simpa only [List.append_nil] using runs rows columns matrix row otherRow column []
    (by simp [UnaryMachine.fields]) window inputSymbol right windowWidth windowValid inputValid

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
          (row : Fin rows) (otherRow : Fin (rows + 1)) (column : Fin columns) (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode (operation (matrix row column))).getLsbD offset.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameAccess.realizes_runtime_entry_restored field operation 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix row otherRow column window inputSymbol right windowWidth windowValid inputValid
  simpa only [List.append_nil] using runs rows columns matrix row otherRow column [] rfl
    (by simp [UnaryMachine.fields]) window inputSymbol right windowWidth windowValid inputValid

end PairedRowAccess

end Polytime.Examples.MatrixPairAccess
