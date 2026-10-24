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

import Polytime2.Matrices.HermiteIncomingController
import Polytime2.TM0.Computation

/-! # Certified incoming-row traversal examples

One old pivot performs a gcd update on a two-row matrix. A zero-pivot traversal
retains its initial matrices, including an empty column dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.HermiteIncomingController

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter]
    (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingController rows columns width pivots).TM0Realizable :=
  (hermiteIncomingController_realizable rows columns width pivots).tm0

private noncomputable def selectedRows : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ) + 1) ↪
    Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)) where
  toFun index := ⟨index.val, by have bounded := index.isLt; norm_num at bounded ⊢; exact bounded⟩
  inj' := by
    intro first second same
    have values := congrArg Fin.val same
    exact Fin.ext values

private noncomputable def pivotColumns : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)) ↪
    Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)) := Function.Embedding.refl _

private noncomputable def arguments :
    (hermiteIncomingController (Parameter := Empty) 2 1 3 1).Arguments Empty.elim
  | .inl false => fun index => ⟨index.val, by simpa using index.isLt⟩
  | .inl true => id
  | .inr () =>
    (⟨fun row _ => if row.val = 0 then 6 else 2, by
      intro row column; dsimp only; split_ifs <;> norm_num [hermiteIncomingWorkspace, hermiteIncomingWorkspaceExtra]⟩,
      ⟨1, by intro row column; simp only [Matrix.one_apply]; split_ifs <;> norm_num [hermiteIncomingWorkspace, hermiteIncomingWorkspaceExtra]⟩)

private theorem valid : (hermiteIncomingController (Parameter := Empty) 2 1 3 1).precondition
    Empty.elim arguments := by
  apply hermiteIncomingController_permitted 2 1 3 1 Empty.elim arguments selectedRows pivotColumns
  · funext index; rfl
  · rfl
  · intro index
    have zero : index.val = 0 := by have bounded := index.isLt; norm_num at bounded; omega
    norm_num [arguments, selectedRows, zero]
  · intro row column before
    have rowBound := row.isLt
    have columnBound := column.isLt
    norm_num at rowBound columnBound
    exact False.elim (by omega)
  · intro row column
    dsimp only [arguments]
    split_ifs <;> norm_num
  · intro row column
    simp only [arguments, Matrix.one_apply]
    split_ifs <;> norm_num

private noncomputable def result :=
  (hermiteIncomingController (Parameter := Empty) 2 1 3 1).compute Empty.elim ⟨arguments, valid⟩

example : result.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 2 ∧
    result.1.val ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 0 := by
  have correct := hermiteIncomingController_correct 2 1 3 1 Empty.elim ⟨arguments, valid⟩
    selectedRows pivotColumns (by funext index; rfl) rfl
  have first := congrArg Prod.fst correct
  change result.1.val = _ at first
  have advanced := IntegerMatrix.hermiteIncomingPrefix_succ_forward selectedRows pivotColumns
    (⟨0, by norm_num⟩ : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
    (arguments (.inr ())).1.val (arguments (.inr ())).2.val
  have advancedFirst := congrArg Prod.fst advanced
  norm_num at first
  have final := first.trans advancedFirst
  rw [final]
  dsimp only [selectedRows, pivotColumns]
  norm_num only [arguments, map_ofNat, map_one, Fin.last]
  change (IntegerMatrix.hermiteRowStage (⟨0, _⟩ : Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    ⟨1, _⟩ (⟨0, _⟩ : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ))) []
    (fun row _ => if row.val = 0 then 6 else 2) 1).1 ⟨0, _⟩ ⟨0, _⟩ = 2 ∧ _
  decide +kernel

example (arguments : {arguments : (hermiteIncomingController (Parameter := Empty) 1 0 1 0).Arguments Empty.elim //
    (hermiteIncomingController (Parameter := Empty) 1 0 1 0).precondition Empty.elim arguments}) :
    (hermiteIncomingController (Parameter := Empty) 1 0 1 0).compute Empty.elim arguments =
      arguments.val (.inr ()) := by
  simp only [hermiteIncomingController, map_zero, ArrayFold.prefix_zero]

end Polytime2.Examples.HermiteIncomingController
