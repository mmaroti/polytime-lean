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

import Polytime2.Arithmetic.DivisionOperations

/-! # Quotient and remainder through the public mathematical interface -/

namespace Polytime2.Examples.Division

open Polytime2.Computation

example : binaryDivision.Realizable := binaryDivision_realizable

example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (13 : Fin 16) | true => (5 : Fin 16)), by change 0 < 5; decide⟩ :
      Fin 16 × Fin 16) = ((2 : Fin 16), (3 : Fin 16)) := rfl

-- Dividing by one retains the maximal quotient at the original width.
example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (15 : Fin 16) | true => (1 : Fin 16)), by change 0 < 1; decide⟩ :
      Fin 16 × Fin 16) = ((15 : Fin 16), (0 : Fin 16)) := rfl

example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (3 : Fin 16) | true => (5 : Fin 16)), by change 0 < 5; decide⟩ :
      Fin 16 × Fin 16) = ((0 : Fin 16), (3 : Fin 16)) := rfl

example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (12 : Fin 16) | true => (3 : Fin 16)), by change 0 < 3; decide⟩ :
      Fin 16 × Fin 16) = ((4 : Fin 16), (0 : Fin 16)) := rfl

-- A divisor using the highest bit needs no public spare-bit hypothesis.
example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (15 : Fin 16) | true => (8 : Fin 16)), by change 0 < 8; decide⟩ :
      Fin 16 × Fin 16) = ((1 : Fin 16), (7 : Fin 16)) := rfl

example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun _ => (15 : Fin 16)), by change 0 < 15; decide⟩ :
      Fin 16 × Fin 16) = ((1 : Fin 16), (0 : Fin 16)) := rfl

example : (binaryDivision.compute (fun _ => 4)
    ⟨(fun | false => (0 : Fin 16) | true => (15 : Fin 16)), by change 0 < 15; decide⟩ :
      Fin 16 × Fin 16) = ((0 : Fin 16), (0 : Fin 16)) := rfl

example : (binaryDivision.compute (fun _ => 1)
    ⟨(fun _ => (1 : Fin 2)), by change 0 < 1; decide⟩ :
      Fin 2 × Fin 2) = ((1 : Fin 2), (0 : Fin 2)) := rfl

example (sizes : Unit → ℕ) (arguments : binaryDivision.Arguments sizes)
    (valid : binaryDivision.precondition sizes arguments) :
    let answer := binaryDivision.compute sizes ⟨arguments, valid⟩
    (arguments false).val = (arguments true).val * answer.1.val + answer.2.val ∧
      answer.2.val < (arguments true).val := binaryDivision_correct sizes arguments valid

-- Width zero has no admissible positive divisor.
example (arguments : binaryDivision.Arguments (fun _ => 0)) :
    ¬ binaryDivision.precondition (fun _ => 0) arguments := by
  change ¬ 0 < (arguments true).val
  have bound := (arguments true).isLt
  norm_num at bound
  omega

end Polytime2.Examples.Division
