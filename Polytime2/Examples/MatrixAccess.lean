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

import Polytime2.Computations.Matrix

/-! # Rectangular matrix access through mathematical certificates -/

namespace Polytime2.Examples.MatrixAccess

open Polytime2.Computation

noncomputable section MatrixExamples

private def element : EncodedDomain Unit := EncodedDomain.booleans
private def rows : MvPolynomial Unit ℕ := 2
private def columns : MvPolynomial Unit ℕ := 3
private def sizes : Unit → ℕ := fun _ => 3
private def lookup := matrixLookup element () rows columns
private def update := matrixUpdate element () rows columns

example : lookup.Realizable := matrixLookup_realizable element () rows columns
example : update.Realizable := matrixUpdate_realizable element () rows columns

private def lookupArguments : lookup.Arguments sizes
  | false => (4 : Fin 8)
  | true => fun _ _ => true
private theorem lookupAdmissible : lookup.precondition sizes lookupArguments := by
  change 4 < MvPolynomial.eval sizes (rows * columns)
  norm_num [rows, columns]

example : lookup.compute sizes ⟨lookupArguments, lookupAdmissible⟩ = true := rfl

private def updateArguments : update.Arguments sizes
  | 0 => (4 : Fin 8)
  | 1 => fun _ _ => false
  | 2 => true
private theorem updateAdmissible : update.precondition sizes updateArguments := by
  change 4 < MvPolynomial.eval sizes (rows * columns)
  norm_num [rows, columns]

-- Update is the ordinary function update on row-major coordinates.
example : update.compute sizes ⟨updateArguments, updateAdmissible⟩ =
    (EncodedDomain.MatrixEncoding.flattenPolynomial (Carrier := Bool) rows columns sizes).symm
      (Function.update (fun _ => false) ⟨4, updateAdmissible⟩ true) := rfl

-- Another coordinate retains its original value.
example : EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes
    (update.compute sizes ⟨updateArguments, updateAdmissible⟩)
    ⟨0, by norm_num [rows, columns]⟩ = false := by
  change (EncodedDomain.MatrixEncoding.flattenPolynomial (Carrier := Bool) rows columns sizes)
    ((EncodedDomain.MatrixEncoding.flattenPolynomial rows columns sizes).symm
      (Function.update (fun _ => false) ⟨4, updateAdmissible⟩ true)) _ = false
  rw [Equiv.apply_symm_apply]
  rw [Function.update_of_ne (by decide)]

-- A singleton scalar domain still supports zero-bit matrix storage.
example : (matrixLookup (EncodedDomain.fixed (Equiv.refl (Fin 1))) () rows columns).Realizable :=
  matrixLookup_realizable _ _ _ _
example : (matrixUpdate (EncodedDomain.fixed (Equiv.refl (Fin 1))) () rows columns).Realizable :=
  matrixUpdate_realizable _ _ _ _

end MatrixExamples
end Polytime2.Examples.MatrixAccess
