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

import Polytime2.Matrices.IntegerMultiplyRealizable

/-! # Composing accumulated integer bases

For an old presentation and a subsequent change of basis, the accumulated
left basis is newLeft * oldLeft and the right basis is oldRight * newRight.
The four input widths are independent, and multiplication derives the two
output widths. Initial stabilization and alternating accumulation share this
operation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def basisInputs
    (rows columns oldLeft oldRight newLeft newRight : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter
  | 0 => integerMatrices rows rows oldLeft
  | 1 => integerMatrices columns columns oldRight
  | 2 => integerMatrices rows rows newLeft
  | 3 => integerMatrices columns columns newRight

/-- Compose the two bases in their mathematical presentation order. -/
noncomputable def integerBasisCompose
    (rows columns oldLeft oldRight newLeft newRight : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) where
  inputDomains := basisInputs rows columns oldLeft oldRight newLeft newRight
  outputDomain := (integerMatrices rows rows (rows + newLeft + oldLeft)).prod
    (integerMatrices columns columns (columns + oldRight + newRight))
  precondition _ _ := True
  compute sizes arguments :=
    ((integerMatrixMultiply rows rows rows newLeft oldLeft).compute sizes
      ⟨fun choice => match choice with | false => arguments.val 2 | true => arguments.val 0, trivial⟩,
    (integerMatrixMultiply columns columns columns oldRight newRight).compute sizes
      ⟨fun choice => match choice with | false => arguments.val 1 | true => arguments.val 3, trivial⟩)

/-- Both accumulated bases reuse the certified rectangular multiplication operation. -/
theorem integerBasisCompose_realizable
    (rows columns oldLeft oldRight newLeft newRight : MvPolynomial Parameter ℕ) :
    (integerBasisCompose rows columns oldLeft oldRight newLeft newRight).Realizable := by
  let computation := integerBasisCompose rows columns oldLeft oldRight newLeft newRight
  have left := (integerMatrixMultiply_realizable rows rows rows newLeft oldLeft).onResults
    computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 2 | true => arguments.val 0)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 0 computation.precondition)
  have right := (integerMatrixMultiply_realizable columns columns columns oldRight newRight).onResults
    computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 1 | true => arguments.val 3)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact Realizable.argument computation.inputDomains 3 computation.precondition)
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ left right

/-- The returned bases are exactly the two ordinary matrix products. -/
theorem integerBasisCompose_correct
    (rows columns oldLeft oldRight newLeft newRight : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerBasisCompose rows columns oldLeft oldRight newLeft newRight).Arguments sizes //
      (integerBasisCompose rows columns oldLeft oldRight newLeft newRight).precondition sizes arguments}) :
    let result := (integerBasisCompose rows columns oldLeft oldRight newLeft newRight).compute sizes arguments
    (result.1.val, result.2.val) =
      ((arguments.val 2).val * (arguments.val 0).val, (arguments.val 1).val * (arguments.val 3).val) := rfl

end Polytime2.Computation
