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

import Polytime2.Matrices.IntegerSystemSolve
import Polytime2.TM0.Computation

/-! # Smith feasibility components

Standalone machine certificates cover the diagonal feasibility criterion and
matrix-vector products. Concrete divisibility checks include negative inputs,
zero divisors, and empty arrays.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerFeasibility

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalFeasible rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerDiagonalFeasible_realizable rows columns matrixWidth targetWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixMulVec rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerMatrixMulVec_realizable rows columns matrixWidth targetWidth).tm0

example : (integerArrayDivides (Parameter := Empty) 1 3 3).compute Empty.elim
    ⟨(fun choice => match choice with | false => fun _ => ⟨-2, by norm_num⟩ | true => fun _ => ⟨4, by norm_num⟩), trivial⟩ = true := by
  apply (integerArrayDivides_correct _ _ _ Empty.elim _).mpr
  intro index
  norm_num

example : (integerArrayDivides (Parameter := Empty) 1 3 3).compute Empty.elim
    ⟨(fun choice => match choice with | false => fun _ => ⟨0, by norm_num⟩ | true => fun _ => ⟨-1, by norm_num⟩), trivial⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have every := (integerArrayDivides_correct _ _ _ Empty.elim _).mp accepted
  have impossible := every ⟨0, by norm_num⟩
  norm_num at impossible

example : (integerArrayDivides (Parameter := Empty) 0 0 0).compute Empty.elim
    ⟨(fun choice => match choice with | false => fun _ => ⟨0, by norm_num⟩ | true => fun _ => ⟨0, by norm_num⟩), trivial⟩ = true := by
  apply (integerArrayDivides_correct _ _ _ Empty.elim _).mpr
  intro index
  have impossible := index.isLt
  norm_num at impossible

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemFeasible rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerSystemFeasible_realizable rows columns matrixWidth targetWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemFeasible rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroTarget : ∀ row, (arguments true row).val = 0) :
    (integerSystemFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true := by
  apply (integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments).mpr
  exact ⟨0, by ext row; simp [zeroTarget]⟩

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemFeasible rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroMatrix : (arguments false).val = 0)
    (nonzeroTarget : ∃ row, (arguments true row).val ≠ 0) :
    (integerSystemFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨values, equation⟩ := (integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments).mp accepted
  obtain ⟨row, nonzero⟩ := nonzeroTarget
  have entry := congrFun equation row
  rw [zeroMatrix, Matrix.zero_mulVec] at entry
  exact nonzero entry.symm

example {Parameter : Type} [Fintype Parameter] (width : MvPolynomial Parameter ℕ) :
    (integerTotalQuotient width).TM0Realizable :=
  (integerTotalQuotient_realizable width).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalSolution rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerDiagonalSolution_realizable rows columns matrixWidth targetWidth).tm0

example : ((integerTotalQuotient (Parameter := Empty) 3).compute Empty.elim
    ⟨(fun choice => if choice then ⟨3, by norm_num⟩ else ⟨-7, by norm_num⟩), trivial⟩).val = -3 := by
  change (-7 : ℤ) / 3 = -3
  norm_num

example : ((integerTotalQuotient (Parameter := Empty) 0).compute Empty.elim
    ⟨(fun _ => ⟨0, by norm_num⟩), trivial⟩).val = 0 := by
  change (0 : ℤ) / 0 = 0
  norm_num

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerDiagonalSolution rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroMatrix : (arguments false).val = 0) :
    (fun column => ((integerDiagonalSolution rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ column).val) = 0 := by
  rw [integerDiagonalSolution_correct, zeroMatrix]
  ext column
  simp [Polytime2.IntegerMatrix.diagonalQuotientSolution]

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemWitness rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerSystemWitness_realizable rows columns matrixWidth targetWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemSolve rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerSystemSolve_realizable rows columns matrixWidth targetWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroTarget : ∀ row, (arguments true row).val = 0) :
    ∃ values, (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values := by
  cases returned : (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ with
  | none =>
    have impossible := (integerSystemSolve_none_iff rows columns matrixWidth targetWidth sizes arguments).mp returned
    exact (impossible ⟨0, by ext row; simp [zeroTarget]⟩).elim
  | some values => exact ⟨values, rfl⟩

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroMatrix : (arguments false).val = 0)
    (nonzeroTarget : ∃ row, (arguments true row).val ≠ 0) :
    (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none := by
  apply (integerSystemSolve_none_iff rows columns matrixWidth targetWidth sizes arguments).mpr
  rintro ⟨values, equation⟩
  obtain ⟨row, nonzero⟩ := nonzeroTarget
  have entry := congrFun equation row
  rw [zeroMatrix, Matrix.zero_mulVec] at entry
  exact nonzero entry.symm

end Polytime2.Examples.IntegerFeasibility
