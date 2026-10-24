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

import Polytime2.Matrices.IntegerDiagonalPair
import Polytime2.TM0.Computation

/-! # Certified diagonal-pair examples

The complete pair operation returns actual diagonal entries and both integer
transformation matrices. Standalone machine certificates cover arbitrary size
assignments. Concrete examples exercise positive and negative entries, a zero
entry, and the zero pair at input width zero.
-/

namespace Polytime2.Examples.DiagonalPair

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (width : MvPolynomial Parameter ℕ) : (integerGcdLcm width).TM0Realizable :=
  (integerGcdLcm_realizable width).tm0

example (width : MvPolynomial Parameter ℕ) : (integerDiagonalPair width).TM0Realizable :=
  (integerDiagonalPair_realizable width).tm0

private def arguments (first second : ℤ) (firstBound : first.natAbs < 32) (secondBound : second.natAbs < 32) :
    (integerDiagonalPair (Parameter := Empty) 5).Arguments Empty.elim
  | false => ⟨first, by simpa using firstBound⟩
  | true => ⟨second, by simpa using secondBound⟩

example :
    let result := (integerDiagonalPair (Parameter := Empty) 5).compute Empty.elim
      ⟨arguments 30 18 (by decide) (by decide), trivial⟩
    result.1.1.val = 6 ∧ result.1.2.val = 90 ∧ result.2.1.val = !![2, -3; -3, 5] ∧
      result.2.2.val = !![1, 9; 1, 10] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals ext row column; fin_cases row <;> fin_cases column <;> decide +kernel

example :
    let result := (integerDiagonalPair (Parameter := Empty) 5).compute Empty.elim
      ⟨arguments (-30) 18 (by decide) (by decide), trivial⟩
    result.1.1.val = 6 ∧ result.1.2.val = -90 := by
  constructor <;> decide +kernel

example :
    let result := (integerDiagonalPair (Parameter := Empty) 5).compute Empty.elim
      ⟨arguments 0 18 (by decide) (by decide), trivial⟩
    result.1.1.val = 18 ∧ result.1.2.val = 0 ∧ result.2.1.val = !![0, 1; -1, 0] ∧
      result.2.2.val = !![1, -1; 1, 0] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals ext row column; fin_cases row <;> fin_cases column <;> decide +kernel

example :
    let result := (integerDiagonalPair (0 : MvPolynomial Unit ℕ)).compute (fun _ => 0)
      ⟨(fun _ => ⟨0, by simp⟩), trivial⟩
    result.1.1.val = 0 ∧ result.1.2.val = 0 ∧ result.2.1.val = 1 ∧
      result.2.2.val = !![1, 0; 1, 1] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals ext row column; fin_cases row <;> fin_cases column <;> decide +kernel

end Polytime2.Examples.DiagonalPair
