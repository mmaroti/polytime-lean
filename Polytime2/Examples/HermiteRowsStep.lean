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

import Polytime2.Matrices.HermiteRowsStep
import Polytime2.TM0.Computation

/-! # Fixed-workspace outer Hermite insertion

A signed first-row state is admitted as the empty prefix of its original input.
The generic certificate returns the next state to the same workspace width.
-/

namespace Polytime2.Examples.HermiteRowsStep

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRowsStep rows columns width).TM0Realizable :=
  (integerHermiteRowsStep_realizable rows columns width).tm0

private noncomputable def original : (integerMatrices (1 : MvPolynomial Empty ℕ) 1 2).Carrier Empty.elim :=
  ⟨fun _ _ => -3, by intro row column; norm_num⟩

private noncomputable def arguments : (integerHermiteRowsStep (1 : MvPolynomial Empty ℕ) 1 2).Arguments Empty.elim :=
  let initial := (Polytime2.IntegerMatrix.hermiteRowsPrefix original.val 0 (Nat.zero_le _)).val
  let bounds := hermiteRowsWorkspace_bound 1 1 2 Empty.elim original.val original.property 0 (Nat.zero_le _)
  fun _ name => match name with
    | 0 => (initial.2, ⟨0, by norm_num⟩)
    | 1 => ⟨initial.1.1, bounds.1⟩
    | 2 => ⟨initial.1.2, bounds.2⟩

example : (integerHermiteRowsStep (1 : MvPolynomial Empty ℕ) 1 2).precondition Empty.elim arguments :=
  ⟨original, rfl⟩

end Polytime2.Examples.HermiteRowsStep
