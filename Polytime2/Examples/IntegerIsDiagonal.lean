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

import Polytime2.Matrices.IntegerIsDiagonal
import Polytime2.TM0.Computation

/-! # Diagonal stopping guards

The matrix test has a standalone machine certificate.
An empty matrix passes; a negative off-diagonal entry fails.
-/

namespace Polytime2.Examples.IntegerIsDiagonal

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (dimension width : MvPolynomial Parameter ℕ) :
    (integerMatrixIsDiagonal dimension width).TM0Realizable :=
  (integerMatrixIsDiagonal_realizable dimension width).tm0

example {Parameter : Type} [Fintype Parameter] (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (matrix : (integerMatrices 0 0 width).Carrier sizes) :
    (integerMatrixIsDiagonal 0 width).compute sizes ⟨fun _ => matrix, trivial⟩ = true := by
  apply (integerMatrixIsDiagonal_correct 0 width sizes matrix).mpr
  simp

private noncomputable def offDiagonal :
    (integerMatrices (2 : MvPolynomial Empty ℕ) 2 1).Carrier Empty.elim :=
  ⟨fun row column => if row.val = 0 ∧ column.val = 1 then -1 else 0,
    by intro row column; dsimp only; split_ifs <;> norm_num⟩

example : (integerMatrixIsDiagonal (2 : MvPolynomial Empty ℕ) 1).compute Empty.elim
    ⟨fun _ => offDiagonal, trivial⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have diagonal := (integerMatrixIsDiagonal_correct 2 1 Empty.elim offDiagonal).mp accepted
  have entry := diagonal ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by intro same; have := congrArg Fin.val same; norm_num at this)
  norm_num [offDiagonal] at entry

end Polytime2.Examples.IntegerIsDiagonal
