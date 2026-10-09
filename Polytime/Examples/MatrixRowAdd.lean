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

import Polytime.Examples.MatrixFrameRowAdd
import Polytime.Examples.MatrixRowCombine
import Polytime.Matrix
import Polytime.FiniteDispatchMachine

/-! # Row addition with a coefficient read from the tape

All bit-pattern branches are compiled into a single finite controller before
the coefficient, matrix dimensions, or row index are supplied. Summing their
polynomial bounds gives one bound independent of the runtime coefficient.
-/

namespace Polytime.Examples.MatrixRowAdd

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeCoefficient

/-- Add a runtime multiple of the source row to the target row. The leading
coefficient slot is consumed and the column counter is reset to zero.
Zero coefficients and zero-column matrices are included; distinct source and
target rows preserve row equivalence. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows) (coefficient initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (Function.update matrix target (fun column => matrix target column + coefficient * matrix source column))).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (word (List.ofFn (BoolTuple.fromBits (field.codec.encode coefficient))) ++
                  UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [source.val, target.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (source ≠ target → Matrix.RowEquivalent matrix (Function.update matrix target
              (fun column => matrix target column + coefficient * matrix source column))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixFrameRowAdd.realizes field 0 0
  let controllerFinite : Fintype Controller := finite
  let controllerInhabited : Inhabited Controller := inhabited
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target coefficient initialScalar right
  simpa only [List.append_nil] using runs rows columns matrix source target [] rfl
    (by simp [UnaryMachine.fields]) coefficient initialScalar right

end RuntimeCoefficient

end Polytime.Examples.MatrixRowAdd
