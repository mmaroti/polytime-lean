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

import Polytime2.Matrices.DiagonalBasisNarrow
import Polytime2.TM0.Computation

/-! # Coupled cleanup with actual nonidentity bases

The pair coefficients are computed from the supplied diagonal entries, then
applied to two different nonidentity bases. A zero-pair example exercises the
no-division branch. The public operation has a standalone machine certificate.
-/

namespace Polytime2.Examples.DiagonalBasisStep

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalBasisStep length diagonalWidth basisWidth).TM0Realizable :=
  (integerDiagonalBasisStep_realizable length diagonalWidth basisWidth).tm0

private def basisValue (chooseRight : Bool) (row column : ℕ) : ℤ :=
  if row = column then 1 else if chooseRight then
    (if row = 1 ∧ column = 0 then 1 else 0)
  else if row = 0 ∧ column = 1 then 2 else 0

private noncomputable def arguments :
    (integerDiagonalBasisStep (Parameter := Empty) 3 5 2).Arguments Empty.elim
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨1, by norm_num⟩
  | 2 => ⟨30, by norm_num⟩
  | 3 => ⟨18, by norm_num⟩
  | 4 => ⟨fun row column => basisValue false row.val column.val, by
      intro row column
      dsimp only [basisValue]
      split_ifs <;> norm_num⟩
  | 5 => ⟨fun row column => basisValue true row.val column.val, by
      intro row column
      dsimp only [basisValue]
      split_ifs <;> norm_num⟩

private theorem arguments_valid :
    (integerDiagonalBasisStep (Parameter := Empty) 3 5 2).precondition Empty.elim arguments := by
  intro equal
  have values := congrArg Fin.val equal
  norm_num [integerDiagonalBasisStep, arguments] at values

example :
    let result := (integerDiagonalBasisStep (Parameter := Empty) 3 5 2).compute Empty.elim ⟨arguments, arguments_valid⟩
    result.1.1.val = 6 ∧ result.1.2.val = 90 ∧
      result.2.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
      result.2.1.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 1 ∧
      result.2.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = -3 ∧
      result.2.1.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = -1 ∧
      result.2.1.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 ∧
      result.2.2.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1 ∧
      result.2.2.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 9 ∧
      result.2.2.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
      result.2.2.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = 19 ∧
      result.2.2.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 := by
  decide +kernel

private noncomputable def zeroArguments :
    (integerDiagonalBasisStep (Parameter := Empty) 3 0 2).Arguments Empty.elim
  | 0 => arguments 0
  | 1 => arguments 1
  | 2 | 3 => ⟨0, by norm_num⟩
  | 4 => arguments 4
  | 5 => arguments 5

private theorem zeroArguments_valid :
    (integerDiagonalBasisStep (Parameter := Empty) 3 0 2).precondition Empty.elim zeroArguments := by
  intro equal
  have values := congrArg Fin.val equal
  norm_num [integerDiagonalBasisStep, zeroArguments, arguments] at values

example :
    let result := (integerDiagonalBasisStep (Parameter := Empty) 3 0 2).compute Empty.elim ⟨zeroArguments, zeroArguments_valid⟩
    result.1.1.val = 0 ∧ result.1.2.val = 0 ∧
      result.2.1.val ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = 2 ∧
      result.2.2.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
      result.2.2.val ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = 1 := by
  decide +kernel

example (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (Realizable.Internal.diagonalBasisNarrow length diagonalWidth basisWidth).TM0Realizable :=
  (Realizable.Internal.diagonalBasisNarrow_realizable length diagonalWidth basisWidth).tm0

private noncomputable def zeroResult :=
  (integerDiagonalBasisStep (Parameter := Empty) 3 0 2).compute Empty.elim
    ⟨zeroArguments, zeroArguments_valid⟩

private theorem zeroResult_fits :
    (Realizable.Internal.diagonalBasisNarrow (Parameter := Empty) 3 0 2).precondition
      Empty.elim (fun _ => zeroResult) := by
  have entries : ∀ row column : Fin 3,
      (zeroResult.2.1.val ⟨row.val, by simpa using row.isLt⟩
        ⟨column.val, by simpa using column.isLt⟩).natAbs < 4 ∧
      (zeroResult.2.2.val ⟨row.val, by simpa using row.isLt⟩
        ⟨column.val, by simpa using column.isLt⟩).natAbs < 4 := by
    decide +kernel
  constructor <;> intro row column
  · simpa using (entries ⟨row.val, by simpa using row.isLt⟩
      ⟨column.val, by simpa using column.isLt⟩).1
  · simpa using (entries ⟨row.val, by simpa using row.isLt⟩
      ⟨column.val, by simpa using column.isLt⟩).2

example :
    let result := (Realizable.Internal.diagonalBasisNarrow (Parameter := Empty) 3 0 2).compute
      Empty.elim ⟨(fun _ => zeroResult), zeroResult_fits⟩
    result.2.1.val = zeroResult.2.1.val ∧ result.2.2.val = zeroResult.2.2.val := ⟨rfl, rfl⟩

private noncomputable def workspaceArguments (workspaceWidth : MvPolynomial Empty ℕ)
    (fits : 2 ≤ MvPolynomial.eval Empty.elim workspaceWidth) :
    (integerDiagonalBasisStep (Parameter := Empty) 3 5 workspaceWidth).Arguments Empty.elim
  | 0 => arguments 0
  | 1 => arguments 1
  | 2 => arguments 2
  | 3 => arguments 3
  | 4 => ⟨(arguments 4).val, by
      intro row column
      exact ((arguments 4).property row column).trans_le
        (pow_le_pow_right₀ (by decide) (by simpa using fits))⟩
  | 5 => ⟨(arguments 5).val, by
      intro row column
      exact ((arguments 5).property row column).trans_le
        (pow_le_pow_right₀ (by decide) (by simpa using fits))⟩

private theorem workspaceArguments_valid (workspaceWidth : MvPolynomial Empty ℕ)
    (fits : 2 ≤ MvPolynomial.eval Empty.elim workspaceWidth) :
    (integerDiagonalBasisStep (Parameter := Empty) 3 5 workspaceWidth).precondition Empty.elim
      (workspaceArguments workspaceWidth fits) := arguments_valid

private noncomputable def workspaceResult :=
  (integerDiagonalBasisStep (Parameter := Empty) 3 5 5).compute Empty.elim
    ⟨workspaceArguments 5 (by norm_num), workspaceArguments_valid 5 (by norm_num)⟩

private theorem workspaceResult_fits :
    (Realizable.Internal.diagonalBasisNarrow (Parameter := Empty) 3 5 5).precondition
      Empty.elim (fun _ => workspaceResult) := by
  have entries : ∀ row column : Fin 3,
      (workspaceResult.2.1.val ⟨row.val, by simpa using row.isLt⟩
        ⟨column.val, by simpa using column.isLt⟩).natAbs < 32 ∧
      (workspaceResult.2.2.val ⟨row.val, by simpa using row.isLt⟩
        ⟨column.val, by simpa using column.isLt⟩).natAbs < 32 := by
    decide +kernel
  constructor <;> intro row column
  · simpa using (entries ⟨row.val, by simpa using row.isLt⟩
      ⟨column.val, by simpa using column.isLt⟩).1
  · simpa using (entries ⟨row.val, by simpa using row.isLt⟩
      ⟨column.val, by simpa using column.isLt⟩).2

example :
    let result := (Realizable.Internal.diagonalBasisNarrow (Parameter := Empty) 3 5 5).compute
      Empty.elim ⟨(fun _ => workspaceResult), workspaceResult_fits⟩
    result.1.1.val = 6 ∧ result.1.2.val = 90 ∧
      result.2.1.val = workspaceResult.2.1.val ∧
      result.2.2.val = workspaceResult.2.2.val := by
  exact ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩

example (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (Realizable.Internal.diagonalBasisStepWithin length diagonalWidth basisWidth).TM0Realizable :=
  (Realizable.Internal.diagonalBasisStepWithin_realizable length diagonalWidth basisWidth).tm0

private theorem withinAllowed :
    (Realizable.Internal.diagonalBasisStepWithin (Parameter := Empty) 3 5 25).precondition Empty.elim
      (workspaceArguments 25 (by norm_num)) := by
  refine ⟨workspaceArguments_valid 25 (by norm_num), 2, ?_, ?_, ?_⟩
  · intro row column
    change ((arguments 4).val row column).natAbs < 2 ^ 2
    simpa only [map_ofNat] using (arguments 4).property row column
  · intro row column
    change ((arguments 5).val row column).natAbs < 2 ^ 2
    simpa only [map_ofNat] using (arguments 5).property row column
  · norm_num

example :
    let result := (Realizable.Internal.diagonalBasisStepWithin (Parameter := Empty) 3 5 25).compute Empty.elim
      ⟨workspaceArguments 25 (by norm_num), withinAllowed⟩
    result.1.1.val = 6 ∧ result.1.2.val = 90 ∧
      result.2.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = -3 ∧
      result.2.2.val ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = 19 := by
  decide +kernel

end Polytime2.Examples.DiagonalBasisStep
