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

import Polytime2.Encoding.PolynomialEvaluator
import Polytime2.Encoding.EncodedArray

/-! # Width evaluation with runtime sizes

These specializations include repeated variables, zero dimensions, no size
parameters, and a nested array whose row width varies at runtime.
-/

namespace Polytime2.Examples.PolynomialEvaluator

noncomputable section Examples

private def polynomial : MvPolynomial (Fin 2) ℕ :=
  (MvPolynomial.X 0 + 2) * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 0

/-- A single finite machine handles all assignments, including zero factors. -/
example : Polytime2.PolynomialEvaluator.Computable
    (fun sizes : Fin 2 → ℕ => (sizes 0 + 2) * sizes 1 + sizes 0 * sizes 0) := by
  simpa [polynomial] using Polytime2.PolynomialEvaluator.computable polynomial

example : Polytime2.PolynomialEvaluator.Computable (fun _ : Empty → ℕ => 0) := by
  simpa using Polytime2.PolynomialEvaluator.computable (0 : MvPolynomial Empty ℕ)

example : Polytime2.PolynomialEvaluator.Computable (fun _ : Empty → ℕ => 3) := by
  simpa using Polytime2.PolynomialEvaluator.computable (MvPolynomial.C 3 : MvPolynomial Empty ℕ)

/-- Evaluating a row's width requires no constant-element-width hypothesis. -/
example (scalar : EncodedDomain Empty) :
    Polytime2.PolynomialEvaluator.Computable
      (fun sizes : Fin 2 → ℕ => sizes 1 * scalar.width Empty.elim) := by
  have widthEq : (scalar.constant.array (1 : Fin 2)).width =
      (fun sizes => sizes 1 * scalar.width Empty.elim) := by
    funext sizes
    simp [EncodedDomain.array, EncodedDomain.constant, EncodedDomain.ofCodec]
  rw [← widthEq]
  exact (scalar.constant.array (1 : Fin 2)).width_computable

/-- Nested arrays have directly computable exact widths as well. -/
example (scalar : EncodedDomain Empty) :
    Polytime2.PolynomialEvaluator.Computable
      (fun sizes : Fin 2 → ℕ => sizes 0 * (sizes 1 * scalar.width Empty.elim)) := by
  have widthEq : ((scalar.constant.array (1 : Fin 2)).array 0).width =
      (fun sizes => sizes 0 * (sizes 1 * scalar.width Empty.elim)) := by
    funext sizes
    simp [EncodedDomain.array, EncodedDomain.constant, EncodedDomain.ofCodec]
  rw [← widthEq]
  exact ((scalar.constant.array (1 : Fin 2)).array 0).width_computable

end Examples
end Polytime2.Examples.PolynomialEvaluator
