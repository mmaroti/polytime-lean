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

import Polytime2.Matrices.IntegerSystemFeasible

/-! # Quotient coordinates from the complete Smith reduction

The returned cyclic/free coordinates agree with the cokernel isomorphism
obtained from the same deterministic Smith reduction.
-/

set_option backward.isDefEq.respectTransparency true

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

set_option maxHeartbeats 16000000 in
/-- The executable result is the mathematical Smith quotient coordinate map. -/
theorem integerSystemQuotientCoordinates_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : ∀ choice : Bool,
      (if choice then (binaryIntegers targetWidth).arrayOfLength rows
        else integerMatrices rows columns matrixWidth).Carrier sizes) :
    let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
      ⟨fun _ => arguments false, trivial⟩
    let form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
      ⟨fun _ => arguments false, trivial⟩
    let result := (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩
    ∀ row, ∃ modulusEq : (result row).1.val =
        IntegerMatrix.diagonalModulus smith.2.1.val smith.1.val form.2.2.2.1 row,
      ZMod.ringEquivCongr modulusEq (result row).2.val =
        IntegerMatrix.diagonalCoordinates smith.2.1.val smith.1.val form.2.2.2.1
          (smith.2.2.1.val.mulVec (fun row => (arguments true row).val)) row := by
  let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
    ⟨fun _ => arguments false, trivial⟩
  have form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
    ⟨fun _ => arguments false, trivial⟩
  have coordinates := integerMatrixCyclicCoordinates_correct rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (smithReductionLeftWidth rows columns matrixWidth) targetWidth sizes
    (fun name => match name with | 0 => smith.2.1 | 1 => smith.2.2.1 | 2 => arguments true)
    smith.1.val form.2.2.2
  exact coordinates

set_option maxHeartbeats 16000000 in
/-- The computed coordinates vanish exactly for targets in the integer image. -/
theorem integerSystemQuotientCoordinates_zero_iff
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ choice : Bool,
      (if choice then (binaryIntegers targetWidth).arrayOfLength rows
        else integerMatrices rows columns matrixWidth).Carrier sizes) :
    (∀ row, ((integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ row).2.val = 0) ↔
      ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  let result := (integerSmithReduction rows columns matrixWidth).compute sizes
    ⟨fun _ => arguments false, trivial⟩
  have form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
    ⟨fun _ => arguments false, trivial⟩
  have normalized := integerMatrixCyclicCoordinates_zero_iff rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (smithReductionLeftWidth rows columns matrixWidth) targetWidth sizes
    (fun name => match name with | 0 => result.2.1 | 1 => result.2.2.1 | 2 => arguments true)
  have diagonal := IntegerMatrix.diagonalFeasible_iff_rowDiagonal result.2.1.val result.1.val form.2.2.2
    (result.2.2.1.val.mulVec (fun row => (arguments true row).val))
  have equivalent := IntegerMatrix.smithFeasible_iff (arguments false).val result.2.1.val
    result.2.2.1.val result.2.2.2.val result.1.val form (fun row => (arguments true row).val)
  have criterion := normalized.trans (diagonal.symm.trans equivalent.symm)
  exact criterion

end Polytime2.Computation
