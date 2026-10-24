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

import Polytime2.Matrices.HermiteRowsController
import Polytime2.TM0.Computation

/-! # Certified complete Hermite row sweeps

The runtime sweep has no admissibility requirement beyond its bounded matrix
input. Concrete results are obtained through its mathematical output contract,
including a signed singular rectangle and either empty dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerHermiteRows

open Polytime2.Computation Polytime2.EncodedDomain

example {Parameter : Type} [Fintype Parameter] (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRows rows columns width).TM0Realizable :=
  (integerHermiteRows_realizable rows columns width).tm0

private noncomputable def singular : (integerMatrices (3 : MvPolynomial Empty ℕ) 2 4).Carrier Empty.elim :=
  ⟨fun row column => if row.val = 0 then 0 else if row.val = 1 then (if column.val = 0 then 6 else 1)
    else if column.val = 0 then -12 else -2, by intro row column; dsimp only; split_ifs <;> norm_num⟩

example : (((integerHermiteRows (3 : MvPolynomial Empty ℕ) 2 4).compute Empty.elim
    ⟨(fun _ => singular), trivial⟩).2).1 = 1 := by
  have actual := congrArg (fun state => state.2.1)
    (integerHermiteRows_correct 3 2 4 Empty.elim ⟨(fun _ => singular), trivial⟩)
  let concrete : Matrix (Fin 3) (Fin 2) ℤ := fun row column =>
    if row.val = 0 then 0 else if row.val = 1 then (if column.val = 0 then 6 else 1)
    else if column.val = 0 then -12 else -2
  have transported := Polytime2.IntegerMatrix.hermiteRowsSweep_congr
    (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)
    (show MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ) = 2 by norm_num)
    singular.val concrete (by
      intro firstRow secondRow firstColumn secondColumn rowValues columnValues
      dsimp only [singular, concrete]
      rw [rowValues, columnValues])
  exact actual.trans (transported.1.trans (by decide +kernel))

example :
    let result := (integerHermiteRows (3 : MvPolynomial Empty ℕ) 2 4).compute Empty.elim
      ⟨(fun _ => singular), trivial⟩
    result.1.2.val * singular.val = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have valid := integerHermiteRows_specification 3 2 4 Empty.elim ⟨(fun _ => singular), trivial⟩
  exact ⟨valid.1, valid.2.1⟩

private noncomputable def negative : (integerMatrices (1 : MvPolynomial Empty ℕ) 1 2).Carrier Empty.elim :=
  ⟨fun _ _ => -3, by intro _row _column; norm_num⟩

example : ((integerHermiteRows (1 : MvPolynomial Empty ℕ) 1 2).compute Empty.elim
    ⟨(fun _ => negative), trivial⟩).1.1.val ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 3 := by
  have actual := congrArg (fun state => state.1.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩)
    (integerHermiteRows_correct 1 1 2 Empty.elim ⟨(fun _ => negative), trivial⟩)
  have transported := Polytime2.IntegerMatrix.hermiteRowsSweep_congr
    (show MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ) = 1 by norm_num)
    (show MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ) = 1 by norm_num)
    negative.val (fun _ _ => -3) (by intros; rfl)
  have entry := transported.2.1 ⟨0, by norm_num⟩ (0 : Fin 1) ⟨0, by norm_num⟩ (0 : Fin 1) rfl rfl
  exact actual.trans (entry.trans (by decide +kernel))

private noncomputable def zeroInput (rows columns : MvPolynomial Empty ℕ) :
    (integerMatrices rows columns 2).Carrier Empty.elim :=
  ⟨0, by intro _row _column; norm_num⟩

example : (((integerHermiteRows (0 : MvPolynomial Empty ℕ) 3 2).compute Empty.elim
    ⟨(fun _ => zeroInput 0 3), trivial⟩).2).1 = 0 := by
  have actual := congrArg (fun state => state.2.1)
    (integerHermiteRows_correct 0 3 2 Empty.elim ⟨(fun _ => zeroInput 0 3), trivial⟩)
  norm_num only [map_zero, map_ofNat] at actual
  exact actual.trans rfl

example : (((integerHermiteRows (3 : MvPolynomial Empty ℕ) 0 2).compute Empty.elim
    ⟨(fun _ => zeroInput 3 0), trivial⟩).2).1 = 0 := by
  have actual := congrArg (fun state => state.2.1)
    (integerHermiteRows_correct 3 0 2 Empty.elim ⟨(fun _ => zeroInput 3 0), trivial⟩)
  have transported := Polytime2.IntegerMatrix.hermiteRowsSweep_congr
    (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)
    (show MvPolynomial.eval Empty.elim (0 : MvPolynomial Empty ℕ) = 0 by norm_num)
    (zeroInput 3 0).val (0 : Matrix (Fin 3) (Fin 0) ℤ) (by intros; rfl)
  exact actual.trans (transported.1.trans (by decide +kernel))

end Polytime2.Examples.IntegerHermiteRows
