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
import Polytime2.Arrays.Operations

/-! # Matrix access derived from array computations

Indices are mathematical row and column pairs. Matrix dimensions are polynomial
expressions in the runtime size parameters.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable section MatrixAccess

private def matrixLookupDomains (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => EncodedDomain.matrixCoordinates rows columns
  | true => EncodedDomain.matrix element rows columns

private def matrixLookupEquivalence (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (name : Bool) (sizes : Parameter → ℕ) :
    (matrixLookupDomains element rows columns name).Carrier sizes ≃
      ((arrayLookup element (rows * columns)).inputDomains name).Carrier sizes :=
  match name with
  | false => EncodedDomain.matrixCoordinateEquiv rows columns sizes
  | true => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes

/-- Read a row-major coordinate of an ordinary mathematical matrix. -/
def matrixLookup (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (arrayLookup element (rows * columns)).reindexDomains
    (matrixLookupDomains element rows columns) element
    (matrixLookupEquivalence element rows columns) (fun _ => Equiv.refl _)

theorem matrixLookup_realizable (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) :
    (matrixLookup element rows columns).Realizable := by
  exact (arrayLookup_realizable element (rows * columns)).reindexDomains
    _ _ _ _
    (by intro name sizes; cases name <;> rfl)
    (by intro sizes; rfl)
    (by intro name sizes value; cases name <;> rfl)
    (by intro sizes value; rfl)

private def matrixUpdateDomains (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Fin 3 → EncodedDomain Parameter
  | 0 => EncodedDomain.matrixCoordinates rows columns
  | 1 => EncodedDomain.matrix element rows columns
  | 2 => element

private def matrixUpdateEquivalence (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) (name : Fin 3) (sizes : Parameter → ℕ) :
    (matrixUpdateDomains element rows columns name).Carrier sizes ≃
      ((arrayUpdate element (rows * columns)).inputDomains name).Carrier sizes :=
  match name with
  | 0 => EncodedDomain.matrixCoordinateEquiv rows columns sizes
  | 1 => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes
  | 2 => Equiv.refl _

/-- Update one row-major coordinate, returning an ordinary matrix of the same shape. -/
def matrixUpdate (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  (arrayUpdate element (rows * columns)).reindexDomains
    (matrixUpdateDomains element rows columns)
    (EncodedDomain.matrix element rows columns)
    (matrixUpdateEquivalence element rows columns)
    (fun sizes => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes)

theorem matrixUpdate_realizable (element : EncodedDomain Parameter)
    (rows columns : MvPolynomial Parameter ℕ) :
    (matrixUpdate element rows columns).Realizable := by
  exact (arrayUpdate_realizable element (rows * columns)).reindexDomains
    _ _ _ _
    (by intro name sizes; fin_cases name <;> rfl)
    (by intro sizes; rfl)
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro sizes value; rfl)

end MatrixAccess
end Polytime2.Computation
