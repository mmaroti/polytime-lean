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

import Polytime2.Matrices.IntegerRowPair
import Polytime2.Matrices.BezoutCoefficients

/-! # Shared coefficient preparation and application for integer elimination

These internal computations separate coefficient preparation from application.
A caller can retain one coefficient record and apply it to matrices with the
same rows and different column counts, including an accumulated left basis.
-/

namespace Polytime2.Computation.Realizable.Internal.BezoutRows

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def coefficients (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) where
  inputDomains name := match name with
    | 0 | 1 => boundedIndex rows
    | 2 => boundedIndex columns
    | 3 => integerMatrices rows columns width
  outputDomain := BezoutCoefficients.domain width
  precondition _ _ := True
  compute sizes arguments := (BezoutCoefficients.computation width).compute sizes
    ⟨(fun choice => ⟨(arguments.val 3).val (if choice then arguments.val 1 else arguments.val 0)
      (arguments.val 2), (arguments.val 3).property _ _⟩), trivial⟩

theorem coefficients_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (coefficients rows columns width).Realizable := by
  classical
  let computation := coefficients rows columns width
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  let element (choice : Bool) sizes (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :
      (binaryIntegers width).Carrier sizes :=
    ⟨(arguments.val 3).val (if choice then arguments.val 1 else arguments.val 0) (arguments.val 2),
      (arguments.val 3).property _ _⟩
  have elementReady (choice : Bool) : (Computation.mk inputs (binaryIntegers width) allowed (element choice)).Realizable := by
    exact (integerMatrixEntry_realizable rows columns width).onResults inputs allowed
      (fun name _ arguments => match name with
        | 0 => if choice then arguments.val 1 else arguments.val 0
        | 1 => arguments.val 2
        | 2 => arguments.val 3) (by intros; trivial) (by
          intro name
          fin_cases name
          · cases choice
            · exact Realizable.argument inputs 0 allowed
            · exact Realizable.argument inputs 1 allowed
          · exact Realizable.argument inputs 2 allowed
          · exact Realizable.argument inputs 3 allowed)
  exact (Realizable.Internal.BezoutCoefficients.realizable width).onResults inputs allowed element
    (by intros; trivial) elementReady

noncomputable def application (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) := by
  let capacity := 2 * width + 1
  have widthEqual : capacity = width + (width + 1) := by dsimp [capacity]; ring
  let inputs : Fin 4 → EncodedDomain Parameter := fun name => match name with
    | 0 | 1 => boundedIndex rows
    | 2 => BezoutCoefficients.domain width
    | 3 => integerMatrices rows columns width
  exact (integerRowPair rows columns capacity).onResults inputs
    (fun _ arguments => arguments 0 ≠ arguments 1)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2 0
      | 3 => arguments.val 2 1
      | 4 => arguments.val 2 2
      | 5 => arguments.val 2 3
      | 6 => (integerMatrixWiden rows columns width (width + 1) capacity widthEqual).compute sizes
          ⟨(fun _ => arguments.val 3), trivial⟩)
    (fun _ arguments => arguments.property)

theorem application_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (application rows columns width).Realizable := by
  classical
  let computation := application rows columns width
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  let capacity := 2 * width + 1
  have widthEqual : capacity = width + (width + 1) := by dsimp [capacity]; ring
  have widened := ((integerMatrixWiden_realizable rows columns width (width + 1)
    capacity widthEqual).withArguments inputs (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition allowed
      (by intros; trivial)
  have coefficient (index : Fin 4) := ((recordProjection_realizable 4 (fun _ => binaryIntegers capacity) index).withArguments
    inputs (MultiTape.oneTape 2) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  apply (integerRowPair_realizable rows columns capacity).onResults inputs allowed
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2 0
      | 3 => arguments.val 2 1
      | 4 => arguments.val 2 2
      | 5 => arguments.val 2 3
      | 6 => (integerMatrixWiden rows columns width (width + 1) capacity widthEqual).compute sizes
          ⟨(fun _ => arguments.val 3), trivial⟩)
    (fun _ arguments => arguments.property)
  intro name
  fin_cases name
  · exact Realizable.argument inputs 0 allowed
  · exact Realizable.argument inputs 1 allowed
  · exact coefficient 0
  · exact coefficient 1
  · exact coefficient 2
  · exact coefficient 3
  · exact widened

end Polytime2.Computation.Realizable.Internal.BezoutRows
