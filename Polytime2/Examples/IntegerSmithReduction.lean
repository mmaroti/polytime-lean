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

import Polytime2.Matrices.IntegerSmithReduction
import Polytime2.TM0.Computation

/-! # Full rectangular Smith reduction

The whole operation accepts arbitrary bounded signed input and has a standalone
machine certificate. Zero input retains a zero output matrix and reports rank
zero, including either empty dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerSmithReduction

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerSmithReduction rows columns width).TM0Realizable :=
  (integerSmithReduction_realizable rows columns width).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerSmithReduction rows columns width).Arguments sizes //
      (integerSmithReduction rows columns width).precondition sizes arguments})
    (zeroMatrix : (arguments.val ()).val = 0) :
    ((integerSmithReduction rows columns width).compute sizes arguments).2.1.val = 0 := by
  have equation := (integerSmithReduction_isSmithForm rows columns width sizes arguments).1
  rw [zeroMatrix, Matrix.mul_zero, Matrix.zero_mul] at equation
  exact equation.symm

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerSmithReduction rows columns width).Arguments sizes //
      (integerSmithReduction rows columns width).precondition sizes arguments})
    (zeroMatrix : (arguments.val ()).val = 0) :
    ((integerSmithReduction rows columns width).compute sizes arguments).1.val = 0 := by
  rw [integerSmithReduction_rank, zeroMatrix, Matrix.rank_zero]

end Polytime2.Examples.IntegerSmithReduction
