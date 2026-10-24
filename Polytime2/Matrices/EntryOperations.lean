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

import Polytime2.Computation.Conditional
import Polytime2.Arrays.Operations
import Polytime2.Matrices.RowsPresentation
import Polytime2.Computation.Reindex

/-! # Row-and-column access to ordinary mathematical matrices -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open StandardMatrixRows

noncomputable section PublicCoordinates

/-- Two dimensions, valid row and column coordinates, and an immutable matrix
suffice for lookup. Every mathematical argument is admissible. -/
def matrixEntry (scalar : EncodedDomain Empty) : Computation (Fin 2) (Fin 3) where
  inputDomains
    | 0 => coordinateDomain 0
    | 1 => coordinateDomain 1
    | 2 => (matrixDomain scalar).withInternalSize
  outputDomain := scalar.constant.withInternalSize
  precondition _ _ := True
  compute _ arguments := arguments.val 2 (arguments.val 0) (arguments.val 1)

/-- Replace exactly the selected mathematical coordinate without a public
counter capacity or an implementation-dependent precondition. -/
def matrixReplace (scalar : EncodedDomain Empty) : Computation (Fin 2) (Fin 4) where
  inputDomains
    | 0 => coordinateDomain 0
    | 1 => coordinateDomain 1
    | 2 => (matrixDomain scalar).withInternalSize
    | 3 => scalar.constant.withInternalSize
  outputDomain := (matrixDomain scalar).withInternalSize
  precondition _ _ := True
  compute _ arguments := Function.update (arguments.val 2) (arguments.val 0)
    (Function.update (arguments.val 2 (arguments.val 0)) (arguments.val 1) (arguments.val 3))

private theorem coordinate_value (dimension : Fin 2) (sizes : Fin 2 → ℕ)
    (index : (coordinateDomain dimension).Carrier sizes) :
    Binary.value (EncodedDomain.ArrayEncoding.bits ((coordinateDomain dimension).encode sizes index)) = index.val :=
  EncodedDomain.boundedIndexOfWidth_value _ _ _ sizes index

/-- Read a whole row through the same generic runtime-width array accessor. -/
private def matrixRow (scalar : EncodedDomain Empty) : Computation (Fin 2) Bool where
  inputDomains | false => coordinateDomain 0 | true => (matrixDomain scalar).withInternalSize
  outputDomain := (scalar.constant.withInternalSize).array 1
  precondition _ _ := True
  compute _ arguments := arguments.val true (arguments.val false)

private theorem matrixRow_realizable (scalar : EncodedDomain Empty) : (matrixRow scalar).Realizable := by
  exact (arrayLookupAtParameter_realizable ((scalar.constant.withInternalSize).array 1)
    (coordinateDomain 0) 0 (fun _ value => value) (coordinate_value 0)).reinterpretInputs
    (matrixRow scalar).inputDomains (fun name _ => match name with | false => id | true => id)
    (by intro name sizes; cases name; rfl; exact matrixDomain_rows_width scalar sizes)
    (by intro name sizes value; cases name; rfl; exact matrixDomain_rows_bits scalar sizes value)
    (fun _ _ => True) (by intros; trivial)

private def replaceMatrixRow (scalar : EncodedDomain Empty) : Computation (Fin 2) (Fin 3) where
  inputDomains | 0 => coordinateDomain 0 | 1 => (matrixDomain scalar).withInternalSize
               | 2 => (scalar.constant.withInternalSize).array 1
  outputDomain := (matrixDomain scalar).withInternalSize
  precondition _ _ := True
  compute _ arguments := Function.update (arguments.val 1) (arguments.val 0) (arguments.val 2)

private theorem replaceMatrixRow_realizable (scalar : EncodedDomain Empty) :
    (replaceMatrixRow scalar).Realizable := by
  have prepared := (arrayUpdateAtParameter_realizable ((scalar.constant.withInternalSize).array 1)
    (coordinateDomain 0) 0 (fun _ value => value) (coordinate_value 0)).reinterpretInputs
    (replaceMatrixRow scalar).inputDomains
    (fun name _ => match name with | 0 => id | 1 => id | 2 => id)
    (by intro name sizes; fin_cases name; rfl; exact matrixDomain_rows_width scalar sizes; rfl)
    (by intro name sizes value; fin_cases name
        rfl
        exact matrixDomain_rows_bits scalar sizes value
        rfl)
    (fun _ _ => True) (by intros; trivial)
  exact prepared.reinterpretOutput (replaceMatrixRow scalar).outputDomain (fun _ value => value)
    (matrixDomain_rows_width scalar) (matrixDomain_rows_bits scalar)

theorem matrixEntry_realizable (scalar : EncodedDomain Empty) : (matrixEntry scalar).Realizable := by
  let computation := matrixEntry scalar
  have row := (matrixRow_realizable scalar).onArguments computation.inputDomains computation.precondition
    (fun choice => match choice with | false => 0 | true => 2) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  exact (arrayLookupAtParameter_realizable scalar.constant.withInternalSize (coordinateDomain 1)
    1 (fun _ value => value) (coordinate_value 1)).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 1 | true => arguments.val 2 (arguments.val 0))
    (by intros; trivial) (by
      intro choice; cases choice
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact row)

theorem matrixReplace_realizable (scalar : EncodedDomain Empty) : (matrixReplace scalar).Realizable := by
  let computation := matrixReplace scalar
  have row := (matrixRow_realizable scalar).onArguments computation.inputDomains computation.precondition
    (fun choice => match choice with | false => 0 | true => 2) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have replaced := (arrayUpdateAtParameter_realizable scalar.constant.withInternalSize (coordinateDomain 1)
    1 (fun _ value => value) (coordinate_value 1)).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 1 | 1 => arguments.val 2 (arguments.val 0) | 2 => arguments.val 3)
    (by intros; trivial) (by
      intro name; fin_cases name
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact row
      · exact Realizable.argument computation.inputDomains 3 computation.precondition)
  exact (replaceMatrixRow_realizable scalar).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 0 | 1 => arguments.val 2
      | 2 => Function.update (arguments.val 2 (arguments.val 0)) (arguments.val 1) (arguments.val 3))
    (by intros; trivial) (by
      intro name; fin_cases name
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact replaced)

end PublicCoordinates
end Polytime2.Computation
