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

import Polytime2.Matrices.Operations

/-! # Rectangular matrix access through mathematical certificates -/

namespace Polytime2.Examples.MatrixAccess

open Polytime2.Computation

noncomputable section MatrixExamples

private def element : EncodedDomain Unit := EncodedDomain.booleans
private def rows : MvPolynomial Unit ℕ := 2
private def columns : MvPolynomial Unit ℕ := 3
private def sizes : Unit → ℕ := fun _ => 3
private def lookup := matrixLookup element rows columns
private def update := matrixUpdate element rows columns

example : lookup.Realizable := matrixLookup_realizable element rows columns
example : update.Realizable := matrixUpdate_realizable element rows columns

private def lookupArguments : lookup.Arguments sizes
  | false => (⟨1, by norm_num [rows]⟩, ⟨1, by norm_num [columns]⟩)
  | true => fun _ _ => true
example : lookup.compute sizes ⟨lookupArguments, trivial⟩ = true := rfl

private def updateArguments : update.Arguments sizes
  | 0 => (⟨1, by norm_num [rows]⟩, ⟨1, by norm_num [columns]⟩)
  | 1 => fun _ _ => false
  | 2 => true
-- Update changes exactly the selected mathematical row and column.
example : update.compute sizes ⟨updateArguments, trivial⟩
    ⟨1, by norm_num [rows]⟩ ⟨1, by norm_num [columns]⟩ = true := by
  change Function.update (fun _ => false)
    (EncodedDomain.matrixCoordinateEquiv rows columns sizes
      (⟨1, by norm_num [rows]⟩, ⟨1, by norm_num [columns]⟩)) true
    (EncodedDomain.matrixCoordinateEquiv rows columns sizes
      (⟨1, by norm_num [rows]⟩, ⟨1, by norm_num [columns]⟩)) = true
  simp

example : update.compute sizes ⟨updateArguments, trivial⟩
    ⟨0, by norm_num [rows]⟩ ⟨0, by norm_num [columns]⟩ = false := by
  change Function.update (fun _ => false)
    (EncodedDomain.matrixCoordinateEquiv rows columns sizes
      (⟨1, by norm_num [rows]⟩, ⟨1, by norm_num [columns]⟩)) true
    (EncodedDomain.matrixCoordinateEquiv rows columns sizes
      (⟨0, by norm_num [rows]⟩, ⟨0, by norm_num [columns]⟩)) = false
  apply Function.update_of_ne
  intro equal
  have same := (EncodedDomain.matrixCoordinateEquiv rows columns sizes).injective equal
  have := congrArg (fun coordinate => coordinate.1.val) same
  contradiction

-- A singleton scalar domain still supports zero-bit matrix storage.
example : (matrixLookup (EncodedDomain.fixed (Equiv.refl (Fin 1))) rows columns).Realizable :=
  matrixLookup_realizable _ _ _
example : (matrixUpdate (EncodedDomain.fixed (Equiv.refl (Fin 1))) rows columns).Realizable :=
  matrixUpdate_realizable _ _ _

end MatrixExamples
end Polytime2.Examples.MatrixAccess
