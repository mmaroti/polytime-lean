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

import Polytime2.Matrices.DiagonalCleanupController
import Polytime2.TM0.Computation

/-! # Generic bounded controller checks

The low-level controller supports zero budgets and empty states. Worked
positive-diagonal examples use the specialized input preparation interface.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.DiagonalCleanupController

open Polytime2.Computation
open Polytime2.Computation.Realizable.Internal
open Polytime2.IntegerMatrix

variable {Parameter : Type} [Fintype Parameter]

example (length productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) :
    (diagonalCleanupController length productWidth steps initialBasisWidth).TM0Realizable :=
  (diagonalCleanupController_realizable length productWidth steps initialBasisWidth).tm0

example (length productWidth initialBasisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalCleanupController length productWidth 0 initialBasisWidth).Arguments sizes //
      (diagonalCleanupController length productWidth 0 initialBasisWidth).precondition sizes arguments}) :
    let result := (diagonalCleanupController length productWidth 0 initialBasisWidth).compute sizes arguments
    ((fun index => (result.1 index).val), (result.2.1.val, result.2.2.val)) =
      ((fun index => ((arguments.val ()).1 index).val), ((arguments.val ()).2.1.val, (arguments.val ()).2.2.val)) := by
  simpa only [map_zero, diagonalCleanupWithBases] using
    diagonalCleanupController_correct length productWidth 0 initialBasisWidth sizes arguments

example (productWidth steps initialBasisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (diagonalCleanupController 0 productWidth steps initialBasisWidth).Arguments sizes) :
    (diagonalCleanupController 0 productWidth steps initialBasisWidth).precondition sizes arguments := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index; have bound := index.isLt; norm_num at bound
  · have empty : IsEmpty (Fin (MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ))) := by
      have zero : MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ) = 0 := by simp
      rw [zero]
      infer_instance
    simp
    exact Nat.one_le_two_pow
  · intro row column; have bound := row.isLt; norm_num at bound
  · intro row column; have bound := row.isLt; norm_num at bound

end Polytime2.Examples.DiagonalCleanupController
