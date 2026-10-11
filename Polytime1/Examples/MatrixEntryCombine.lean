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
import Polytime1.Examples.MatrixPairWrite

/-! # Combining source and target entries in one runtime column -/

namespace Polytime1.Examples.MatrixEntryCombine

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeEntries

/-- Combine runtime entries and restore both row counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) :
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
          let replacement := operation (matrix source column) (matrix target column)
          let updated := Function.update matrix target (Function.update (matrix target) column replacement)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [source.val, target.val, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [source.val, target.val, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameCombine.realizes field operation 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix source target column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

/-- Combine runtime entries and advance the column counter. -/
theorem realizes_next_column (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier) :
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
          let replacement := operation (matrix source column) (matrix target column)
          let updated := Function.update matrix target (Function.update (matrix target) column replacement)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns updated).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry []
              (UnaryMachine.fields [source.val, target.val, column.val, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
            (Tape.configuration exit []
              (UnaryMachine.fields [source.val, target.val, column.val + 1, columns] ++
                word (List.ofFn (BoolTuple.fromBits (field.codec.encode replacement))) ++
                3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameCombine.realizes_next_column field operation 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target column initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix source target column [] rfl
    (by simp [UnaryMachine.fields]) initialScalar right

end RuntimeEntries

end Polytime1.Examples.MatrixEntryCombine
