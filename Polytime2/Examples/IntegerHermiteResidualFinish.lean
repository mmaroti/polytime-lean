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

import Polytime2.Matrices.IntegerHermiteResidualFinish
import Polytime2.TM0.Computation

/-! # Dependent and independent residual branches

A zero source row returns no pivot and keeps both matrices. A negative nonzero
source entry returns its actual column and takes the extension branch.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteResidualFinish

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteResidualFinish rows columns width length).TM0Realizable :=
  (integerHermiteResidualFinish_realizable rows columns width length).tm0

private noncomputable def arguments (nonzero : Bool) :
    (integerHermiteResidualFinish (Parameter := Empty) 2 1 3 1).Arguments Empty.elim
  | 0 => ⟨1, by norm_num⟩
  | 1 => ⟨fun row _ => if row.val = 0 then 5 else if nonzero then -3 else 0, by
      intro row column; dsimp only; split_ifs <;> norm_num⟩
  | 2 => ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num⟩
  | 3 => fun _ => ⟨0, by norm_num⟩

private theorem valid (nonzero : Bool) :
    (integerHermiteResidualFinish (Parameter := Empty) 2 1 3 1).precondition Empty.elim (arguments nonzero) := by
  constructor
  · apply List.nodup_ofFn.mpr
    intro first second same
    apply Fin.ext
    have firstBound := first.isLt
    have secondBound := second.isLt
    norm_num at firstBound secondBound
    omega
  · intro member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    have values := congrArg Fin.val same
    norm_num [arguments] at values

example : ((integerHermiteResidualFinish (Parameter := Empty) 2 1 3 1).compute Empty.elim
    ⟨arguments false, valid false⟩).2 = none := by
  rw [integerHermiteResidualFinish_pivot]
  apply (IntegerMatrix.hermiteResidualPivot_none _ _).mpr
  funext column
  norm_num [arguments]

example : ((integerHermiteResidualFinish (Parameter := Empty) 2 1 3 1).compute Empty.elim
    ⟨arguments true, valid true⟩).2 = some ⟨0, by norm_num⟩ := by
  rw [integerHermiteResidualFinish_pivot]
  apply (ArraySearch.firstFalse_some_iff _ _).mpr
  norm_num [IntegerMatrix.hermiteResidualPivot, arguments, List.ofFn]
  decide +kernel

example (nonzero : Bool) :
    let result := (integerHermiteResidualFinish (Parameter := Empty) 2 1 3 1).compute Empty.elim
      ⟨arguments nonzero, valid nonzero⟩
    result.1.2.val * (arguments nonzero 1).val = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have preserved := integerHermiteResidualFinish_preserves 2 1 3 1 Empty.elim
    ⟨arguments nonzero, valid nonzero⟩ (arguments nonzero 1).val 1
    (by simp [arguments]) (by simp [arguments])
  simpa only [Matrix.mul_one] using preserved

end Polytime2.Examples.IntegerHermiteResidualFinish
