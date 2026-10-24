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

import Polytime2.Matrices.HermiteAlternatingAdvance
import Polytime2.TM0.Computation

/-! # Certified conditional alternating pairs

The whole pair has a standalone machine certificate. For positive lower
triangular input, the returned matrix is diagonal or strictly decreases the
mathematical bit measure used by the bounded schedule.
-/

namespace Polytime2.Examples.IntegerHermiteAlternatingStep

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingStepRaw dimension width).TM0Realizable :=
  (integerHermiteAlternatingStepRaw_realizable dimension width).tm0

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingStepRaw dimension width).Arguments sizes //
      (integerHermiteAlternatingStepRaw dimension width).precondition sizes arguments})
    (lower : (arguments.val ()).val.IsLowerTriangular)
    (positive : ∀ index, 0 < (arguments.val ()).val index index) :
    let result := (integerHermiteAlternatingStepRaw dimension width).compute sizes arguments
    (∀ row column, row ≠ column → result.1.val row column = 0) ∨
      (Polytime2.IntegerMatrix.diagonalPotential (fun row => (result.1.val row row).natAbs)).size <
        (Polytime2.IntegerMatrix.diagonalPotential (fun row => ((arguments.val ()).val row row).natAbs)).size := by
  have progress := Polytime2.IntegerMatrix.hermiteAlternatingStep_diagonal_or_progress
    (arguments.val ()).val lower positive
  rw [← integerHermiteAlternatingStepRaw_correct dimension width sizes arguments] at progress
  exact progress

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingStep dimension width).TM0Realizable :=
  (integerHermiteAlternatingStep_realizable dimension width).tm0

example {Parameter : Type} [Fintype Parameter]
    (dimension width budget : MvPolynomial Parameter ℕ) :
    (Polytime2.Computation.Realizable.Internal.integerHermiteAlternatingAdvance dimension width budget).TM0Realizable :=
  (Polytime2.Computation.Realizable.Internal.integerHermiteAlternatingAdvance_realizable dimension width budget).tm0

end Polytime2.Examples.IntegerHermiteAlternatingStep
