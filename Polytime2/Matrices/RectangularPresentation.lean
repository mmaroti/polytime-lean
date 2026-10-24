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

import Polytime2.Matrices.IntegerRectangularDiagonal
import Polytime2.Matrices.ExtendIntegerBasis

/-! # Building a full rectangular diagonal presentation

Construct the rectangular diagonal and extend both supplied active bases by
identity. The diagonal and basis magnitude widths are independent. Hermite
lifting and divisibility cleanup share this certified assembly operation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Build the full matrix and identity-extended bases at their derived widths. -/
noncomputable def integerRectangularDiagonalWithBases (rows columns rank diagonalWidth basisWidth : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := ((binaryNaturalsOfWidth diagonalWidth).arrayOfLength rank).prod
    ((integerMatrices rank rank basisWidth).prod (integerMatrices rank rank basisWidth))
  outputDomain := (integerMatrices rows columns ((diagonalWidth) + 1)).prod
    ((integerMatrices rows rows (basisWidth + 1)).prod
      (integerMatrices columns columns (basisWidth + 1)))
  precondition sizes _ := MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
    MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns
  compute sizes arguments :=
    ((integerRectangularDiagonal rows columns rank (diagonalWidth)).compute sizes
      ⟨(fun _ => (arguments.val ()).1), trivial⟩,
     ((extendIntegerBasis rows rank (basisWidth)).compute sizes
        ⟨(fun _ => (arguments.val ()).2.1), arguments.property.1⟩,
      (extendIntegerBasis columns rank (basisWidth)).compute sizes
        ⟨(fun _ => (arguments.val ()).2.2), arguments.property.2⟩))

theorem integerRectangularDiagonalWithBases_realizable (rows columns rank diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (integerRectangularDiagonalWithBases rows columns rank diagonalWidth basisWidth).Realizable := by
  let computation := integerRectangularDiagonalWithBases rows columns rank diagonalWidth basisWidth
  let diagonal := (binaryNaturalsOfWidth (diagonalWidth)).arrayOfLength rank
  let matrix := integerMatrices rank rank (basisWidth)
  have entries := (pairProjection_realizable diagonal (matrix.prod matrix) false).withPrecondition computation.precondition
    (by intros; trivial)
  have bases := (pairProjection_realizable diagonal (matrix.prod matrix) true).withPrecondition computation.precondition
    (by intros; trivial)
  have first := (bases.followedBy (pairProjection_realizable matrix matrix false) rfl (by intros; trivial)).followedBy
    (extendIntegerBasis_realizable rows rank (basisWidth)) rfl (by
      intro sizes arguments valid
      exact valid.1)
  have second := (bases.followedBy (pairProjection_realizable matrix matrix true) rfl (by intros; trivial)).followedBy
    (extendIntegerBasis_realizable columns rank (basisWidth)) rfl (by
      intro sizes arguments valid
      exact valid.2)
  have fullDiagonal := entries.followedBy
    (integerRectangularDiagonal_realizable rows columns rank (diagonalWidth)) rfl (by intros; trivial)
  have fullBases := Realizable.pairOutputs computation.inputDomains
    (integerMatrices rows rows (basisWidth + 1))
    (integerMatrices columns columns (basisWidth + 1)) computation.precondition _ _ first second
  have complete := Realizable.pairOutputs computation.inputDomains
    (integerMatrices rows columns ((diagonalWidth) + 1))
    ((integerMatrices rows rows (basisWidth + 1)).prod
      (integerMatrices columns columns (basisWidth + 1)))
    computation.precondition _ _ fullDiagonal fullBases
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

end Polytime2.Computation
