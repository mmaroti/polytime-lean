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
import Polytime.Examples.MatrixPairAccess

/-! # Matrix-entry updates retaining a second runtime row index

The first row counter selects the entry; the second row counter survives the
update for subsequent source/target operations in the same frame.
-/

namespace Polytime.Examples.MatrixPairWrite

open Matrices TupleMachine

-- scalarLevel: the fixed mathematical carrier of matrix entries.
universe scalarLevel

noncomputable section PairedRowWrites

/-- Compute the address, read the runtime replacement, update one canonical
matrix entry, clear evaluation scratch, and restore the counter header. The
controller is fixed before dimensions, indices, and replacement values vary. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row otherRow : Fin rows) (column : Fin columns) (replacement : field.Carrier)
          (inputSymbol : Symbol) (right : List Symbol) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode replacement).getLsbD offset.val)
          let updated := Function.update matrix row (Function.update (matrix row) column replacement)
          let result := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameWrite.realizes field 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix row otherRow column replacement inputSymbol right inputValid
  simpa only [List.append_nil] using runs rows columns matrix row otherRow column [] rfl
    (by simp [UnaryMachine.fields]) replacement inputSymbol right inputValid

/-- Read, transform, and write one entry in a shared frame. Both addresses are
computed from runtime counters; the scalar operation is a fixed table. -/
theorem realizes_entry_map (field : FixedPresentation.{scalarLevel}) [Nontrivial field.Carrier]
    (operation : field.Carrier → field.Carrier) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row otherRow : Fin rows) (column : Fin columns) (window : List Symbol) (inputSymbol : Symbol)
          (right : List Symbol) (_windowWidth : window.length = field.bitWidth)
          (_windowValid : ∀ symbol ∈ window, symbol ≠ 3 ∧ symbol ≠ 6) (_inputValid : inputSymbol ≠ 4),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let replacement := operation (matrix row column)
          let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
            (field.codec.encode replacement).getLsbD offset.val)
          let updated := Function.update matrix row (Function.update (matrix row) column replacement)
          let result := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ window ++
                3 :: (List.replicate matrixWidth inputSymbol ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [row.val, otherRow.val, column.val, columns] ++ word scalar ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word result ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameWrite.realizes_entry_map field operation 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix row otherRow column window inputSymbol right windowWidth windowValid inputValid
  simpa only [List.append_nil] using runs rows columns matrix row otherRow column [] rfl
    (by simp [UnaryMachine.fields]) window inputSymbol right windowWidth windowValid inputValid

end PairedRowWrites

end Polytime.Examples.MatrixPairWrite
