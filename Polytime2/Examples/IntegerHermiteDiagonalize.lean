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

import Polytime2.Matrices.IntegerHermiteDiagonalize
import Polytime2.TM0.Computation

/-! # Complete bounded alternating diagonalization

The public polynomial-budget operation and arbitrary-budget run have standalone
machine certificates. Zero budget retains the input and both identity bases;
empty dimensions stop for every budget.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteDiagonalize

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteDiagonalize dimension width).TM0Realizable :=
  (integerHermiteDiagonalize_realizable dimension width).tm0

example {Parameter : Type} [Fintype Parameter] (dimension width budget : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingRun dimension width budget).TM0Realizable :=
  (integerHermiteAlternatingRun_realizable dimension width budget).tm0

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingRun dimension width 0).Arguments sizes //
      (integerHermiteAlternatingRun dimension width 0).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingRun dimension width 0).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) = ((arguments.val ()).val, 1, 1) := by
  dsimp only
  rw [integerHermiteAlternatingRun_correct]
  simp [Polytime2.IntegerMatrix.hermiteAlternatingRun]

example {Parameter : Type} [Fintype Parameter] (width budget : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingRun 0 width budget).Arguments sizes //
      (integerHermiteAlternatingRun 0 width budget).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingRun 0 width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) = ((arguments.val ()).val, 1, 1) := by
  dsimp only
  rw [integerHermiteAlternatingRun_correct]
  apply Polytime2.IntegerMatrix.hermiteAlternatingRun_of_diagonal
  simp

end Polytime2.Examples.IntegerHermiteDiagonalize
