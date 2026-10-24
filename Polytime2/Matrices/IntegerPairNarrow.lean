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

import Polytime2.Matrices.IntegerNarrow

/-! # Narrowing a pair of bounded integer matrices

For two ordinary matrices with independently sized shapes and source widths,
preserve both values at a common target width when every entry fits. The
realization composes the existing scalar-derived matrix narrowings.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Narrow both matrices, retaining their mathematical values. -/
noncomputable def integerMatrixPairNarrow
    (firstRows firstColumns secondRows secondColumns firstWidth secondWidth targetWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (integerMatrices firstRows firstColumns firstWidth).prod
    (integerMatrices secondRows secondColumns secondWidth)
  outputDomain := (integerMatrices firstRows firstColumns targetWidth).prod
    (integerMatrices secondRows secondColumns targetWidth)
  precondition sizes arguments :=
    (∀ row column, ((arguments ()).1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes targetWidth) ∧
    (∀ row column, ((arguments ()).2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes targetWidth)
  compute _ arguments := (⟨(arguments.val ()).1.val, arguments.property.1⟩,
    ⟨(arguments.val ()).2.val, arguments.property.2⟩)

theorem integerMatrixPairNarrow_realizable
    (firstRows firstColumns secondRows secondColumns firstWidth secondWidth targetWidth : MvPolynomial Parameter ℕ)
    (firstFits : ∀ sizes, MvPolynomial.eval sizes targetWidth ≤ MvPolynomial.eval sizes firstWidth)
    (secondFits : ∀ sizes, MvPolynomial.eval sizes targetWidth ≤ MvPolynomial.eval sizes secondWidth) :
    (integerMatrixPairNarrow firstRows firstColumns secondRows secondColumns firstWidth secondWidth targetWidth).Realizable := by
  exact (integerMatrixNarrow_realizable firstRows firstColumns firstWidth targetWidth firstFits).prodMap
    (integerMatrixNarrow_realizable secondRows secondColumns secondWidth targetWidth secondFits)

end Polytime2.Computation
