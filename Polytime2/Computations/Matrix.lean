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

import Polytime2.Computation.Reindex
import Polytime2.Computations.Array

/-! # Matrix access derived from array computations

Indices are flat row-major coordinates. Matrix dimensions are polynomial
expressions in the runtime size parameters.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable section MatrixAccess

private def matrixLookupDomains (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => EncodedDomain.binaryNaturals indexCapacity
  | true => EncodedDomain.matrix element rows columns

private def matrixLookupEquivalence (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (name : Bool) (sizes : Parameter → ℕ) :
    (matrixLookupDomains element indexCapacity rows columns name).Carrier sizes ≃
      ((arrayLookup element indexCapacity (rows * columns)).inputDomains name).Carrier sizes :=
  match name with
  | false => Equiv.refl _
  | true => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes

/-- Read a row-major coordinate of an ordinary mathematical matrix. -/
def matrixLookup (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (arrayLookup element indexCapacity (rows * columns)).reindexDomains
    (matrixLookupDomains element indexCapacity rows columns) element
    (matrixLookupEquivalence element indexCapacity rows columns) (fun _ => Equiv.refl _)

theorem matrixLookup_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (elementWidth : ℕ)
    (fixedWidth : ∀ sizes, element.width sizes = elementWidth) :
    (matrixLookup element indexCapacity rows columns).Realizable := by
  exact (arrayLookup_realizable element indexCapacity (rows * columns) elementWidth fixedWidth).reindexDomains
    _ _ _ _
    (by intro name sizes; cases name <;> rfl)
    (by intro sizes; rfl)
    (by intro name sizes value; cases name <;> rfl)
    (by intro sizes value; rfl)

private def matrixUpdateDomains (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Fin 3 → EncodedDomain Parameter
  | 0 => EncodedDomain.binaryNaturals indexCapacity
  | 1 => EncodedDomain.matrix element rows columns
  | 2 => element

private def matrixUpdateEquivalence (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (name : Fin 3) (sizes : Parameter → ℕ) :
    (matrixUpdateDomains element indexCapacity rows columns name).Carrier sizes ≃
      ((arrayUpdate element indexCapacity (rows * columns)).inputDomains name).Carrier sizes :=
  match name with
  | 0 => Equiv.refl _
  | 1 => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes
  | 2 => Equiv.refl _

/-- Update one row-major coordinate, returning an ordinary matrix of the same shape. -/
def matrixUpdate (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  (arrayUpdate element indexCapacity (rows * columns)).reindexDomains
    (matrixUpdateDomains element indexCapacity rows columns)
    (EncodedDomain.matrix element rows columns)
    (matrixUpdateEquivalence element indexCapacity rows columns)
    (fun sizes => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes)

theorem matrixUpdate_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (elementWidth : ℕ)
    (fixedWidth : ∀ sizes, element.width sizes = elementWidth) :
    (matrixUpdate element indexCapacity rows columns).Realizable := by
  exact (arrayUpdate_realizable element indexCapacity (rows * columns) elementWidth fixedWidth).reindexDomains
    _ _ _ _
    (by intro name sizes; fin_cases name <;> rfl)
    (by intro sizes; rfl)
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro sizes value; rfl)

end MatrixAccess
end Polytime2.Computation
