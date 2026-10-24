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

import Polytime2.Matrices.IntegerOperations

/-! # Integer matrix products with derived output bounds

Multiply ordinary rectangular matrices with independent magnitude widths.
The inner dimension plus the two input widths bounds every output entry.
Empty inner dimensions produce the zero matrix. No overflow premise or
caller-supplied scratch width is part of the mathematical interface.
-/

namespace Polytime2.IntegerMatrix

/-- Any partial dot product fits the same dimension-derived magnitude width. -/
theorem partial_dotProduct_bound {length : ℕ} (leftWidth rightWidth : ℕ)
    (left right : Fin length → ℤ) (indices : Finset (Fin length))
    (leftBound : ∀ index, (left index).natAbs < 2 ^ leftWidth)
    (rightBound : ∀ index, (right index).natAbs < 2 ^ rightWidth) :
    (∑ index ∈ indices, left index * right index).natAbs <
      2 ^ (length + leftWidth + rightWidth) := by
  have entry (index : Fin length) : (left index * right index).natAbs ≤ 2 ^ (leftWidth + rightWidth) := by
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (leftBound index).le (rightBound index).le
  calc
    _ ≤ ∑ index ∈ indices, (left index * right index).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _index ∈ indices, 2 ^ (leftWidth + rightWidth) := Finset.sum_le_sum (fun index _ => entry index)
    _ = indices.card * 2 ^ (leftWidth + rightWidth) := by simp
    _ ≤ length * 2 ^ (leftWidth + rightWidth) := Nat.mul_le_mul_right _ (by
      simpa using Finset.card_le_univ indices)
    _ < 2 ^ length * 2 ^ (leftWidth + rightWidth) :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity)
    _ = 2 ^ (length + leftWidth + rightWidth) := by rw [← pow_add]; congr 1; omega

end Polytime2.IntegerMatrix

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Exact rectangular multiplication; dimensions and input bounds derive the output width. -/
noncomputable def integerMatrixMultiply
    (rows inner columns leftWidth rightWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then integerMatrices inner columns rightWidth else integerMatrices rows inner leftWidth
  outputDomain := integerMatrices rows columns (inner + leftWidth + rightWidth)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val false).val * (arguments.val true).val, by
    intro row column
    simpa only [map_add, Matrix.mul_apply] using
      IntegerMatrix.partial_dotProduct_bound (MvPolynomial.eval sizes leftWidth) (MvPolynomial.eval sizes rightWidth)
        (fun index => (arguments.val false).val row index) (fun index => (arguments.val true).val index column)
        Finset.univ (fun index => (arguments.val false).property row index)
        (fun index => (arguments.val true).property index column)⟩

/-- The output is the ordinary integer matrix product. -/
theorem integerMatrixMultiply_correct
    (rows inner columns leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerMatrixMultiply rows inner columns leftWidth rightWidth).Arguments sizes //
      (integerMatrixMultiply rows inner columns leftWidth rightWidth).precondition sizes arguments}) :
    ((integerMatrixMultiply rows inner columns leftWidth rightWidth).compute sizes arguments).val =
      (arguments.val false).val * (arguments.val true).val := rfl

end Polytime2.Computation
