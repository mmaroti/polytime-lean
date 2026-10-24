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

import Polytime2.Matrices.HermiteColumnController

/-! # Certified integer column reduction with internal storage preparation

Given a bounded rectangular integer matrix, a bounded accumulated left basis,
and a positive pivot at a selected source row and column, clear that column
outside the source. Derive the polynomial workspace from the input width and
row count and prepare both matrices internally. No rank or invertibility
condition is imposed on the working matrix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter
  | 0 => boundedIndex rows | 1 => boundedIndex columns
  | 2 => integerMatrices rows columns width | 3 => integerMatrices rows rows width

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width name).Carrier sizes) :=
  0 < (arguments 2).val (arguments 0) (arguments 1)

private noncomputable def prepared (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerMatrixWiden rows columns width (rows * (2 * width + 2)) (hermiteColumnWorkspace rows width) rfl,
   integerMatrixWiden rows rows width (rows * (2 * width + 2)) (hermiteColumnWorkspace rows width) rfl)

private noncomputable def preparedValues (rows columns width : MvPolynomial Parameter ℕ) (name : Bool ⊕ Unit)
    (sizes : Parameter → ℕ) (arguments : {arguments : ∀ name, (inputs rows columns width name).Carrier sizes //
      allowed rows columns width sizes arguments}) :
    ((hermiteColumnController rows columns width).inputDomains name).Carrier sizes :=
  match name with
  | .inl false => arguments.val 0
  | .inl true => arguments.val 1
  | .inr () => ((prepared rows columns width).1.compute sizes ⟨(fun _ => arguments.val 2), trivial⟩,
      (prepared rows columns width).2.compute sizes ⟨(fun _ => arguments.val 3), trivial⟩)

private theorem prepared_valid (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width name).Carrier sizes // allowed rows columns width sizes arguments}) :
    (hermiteColumnController rows columns width).precondition sizes (fun name => preparedValues rows columns width name sizes arguments) := by
  exact ⟨arguments.property, (arguments.val 2).property, (arguments.val 3).property⟩

/-- Clear a positive-pivot column and return the actual matrix and left basis. -/
noncomputable def integerHermiteColumn (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) :=
  (hermiteColumnController rows columns width).onResults (inputs rows columns width) (allowed rows columns width)
    (preparedValues rows columns width) (prepared_valid rows columns width)

theorem integerHermiteColumn_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteColumn rows columns width).Realizable := by
  apply (hermiteColumnController_realizable rows columns width).onResults (inputs rows columns width)
    (allowed rows columns width) (preparedValues rows columns width) (prepared_valid rows columns width)
  intro name
  rcases name with choice | singleton
  · cases choice
    · exact Realizable.argument (inputs rows columns width) 0 (allowed rows columns width)
    · exact Realizable.argument (inputs rows columns width) 1 (allowed rows columns width)
  · cases singleton
    have first := ((integerMatrixWiden_realizable rows columns width (rows * (2 * width + 2))
      (hermiteColumnWorkspace rows width) rfl).withArguments (inputs rows columns width)
      (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition (allowed rows columns width) (by intros; trivial)
    have second := ((integerMatrixWiden_realizable rows rows width (rows * (2 * width + 2))
      (hermiteColumnWorkspace rows width) rfl).withArguments (inputs rows columns width)
      (MultiTape.oneTape 3) (by intros; rfl)).withPrecondition (allowed rows columns width) (by intros; trivial)
    exact first.prodMk second

/-- The prepared runtime traversal is precisely the mathematical column prefix. -/
theorem integerHermiteColumn_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteColumn rows columns width).Arguments sizes //
      (integerHermiteColumn rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteColumn rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteColumnPrefix
      (rows := MvPolynomial.eval sizes rows) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (MvPolynomial.eval sizes rows) (arguments.val 2).val (arguments.val 3).val := by
  exact hermiteColumnController_correct rows columns width sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), prepared_valid rows columns width sizes arguments⟩

end Polytime2.Computation
