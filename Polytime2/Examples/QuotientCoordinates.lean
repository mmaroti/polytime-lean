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

import Polytime2.Matrices.IntegerSystemCoordinates
import Polytime2.Matrices.AugmentedRank
import Polytime2.TM0.Computation

/-! # Actual quotient-coordinate encoding and arithmetic

Machine certificates cover scalar and vector transport. Concrete examples
check a positive modulus with a negative input and preserve a negative free
integer at modulus zero. Empty coordinate vectors vanish vacuously.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.QuotientCoordinates

open Polytime2.Computation

example {Parameter : Type} [Fintype Parameter] (modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicCoordinate modulusWidth valueWidth).TM0Realizable :=
  (integerCyclicCoordinate_realizable modulusWidth valueWidth).tm0

example {Parameter : Type} [Fintype Parameter] (length modulusWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicCoordinates length modulusWidth valueWidth).TM0Realizable :=
  (integerCyclicCoordinates_realizable length modulusWidth valueWidth).tm0

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).TM0Realizable :=
  (integerSystemQuotientCoordinates_realizable rows columns matrixWidth targetWidth).tm0

private noncomputable def freeInput : (integerCyclicCoordinate (Parameter := Empty) 0 3).Arguments Empty.elim
  | false => ⟨0, by norm_num⟩
  | true => ⟨-7, by norm_num⟩

example : (ZMod.cast ((integerCyclicCoordinate (Parameter := Empty) 0 3).compute Empty.elim
    ⟨freeInput, trivial⟩).2.val : ℤ) = -7 := by
  change (Int.cast (-7) : ℤ) = -7
  exact Int.cast_id

private noncomputable def finiteInput : (integerCyclicCoordinate (Parameter := Empty) 3 4).Arguments Empty.elim
  | false => ⟨5, by norm_num⟩
  | true => ⟨-7, by norm_num⟩

example : ZMod.val ((integerCyclicCoordinate (Parameter := Empty) 3 4).compute Empty.elim
    ⟨finiteInput, trivial⟩).2.val = 3 := by
  change (3 : ℕ) = 3
  rfl

example {Parameter : Type} [Fintype Parameter] (modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerCyclicCoordinates 0 modulusWidth valueWidth).Arguments sizes) :
    ∀ index, ((integerCyclicCoordinates 0 modulusWidth valueWidth).compute sizes ⟨arguments, trivial⟩ index).2.val = 0 := by
  intro index
  have impossible := index.isLt
  simp at impossible


example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroTarget : ∀ row, (arguments true row).val = 0) :
    ∀ row, ((integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ row).2.val = 0 := by
  apply (integerSystemQuotientCoordinates_zero_iff rows columns matrixWidth targetWidth sizes arguments).mpr
  exact ⟨0, by ext row; simp [zeroTarget]⟩

example {Parameter : Type} [Fintype Parameter]
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).Arguments sizes)
    (zeroMatrix : (arguments false).val = 0)
    (nonzeroTarget : ∃ row, (arguments true row).val ≠ 0) :
    ¬ ∀ row, ((integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ row).2.val = 0 := by
  intro vanished
  obtain ⟨values, equation⟩ :=
    (integerSystemQuotientCoordinates_zero_iff rows columns matrixWidth targetWidth sizes arguments).mp vanished
  obtain ⟨row, nonzero⟩ := nonzeroTarget
  have entry := congrFun equation row
  rw [zeroMatrix, Matrix.zero_mulVec] at entry
  exact nonzero entry.symm

end Polytime2.Examples.QuotientCoordinates
