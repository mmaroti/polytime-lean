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

import Polytime2.Matrices.IntegerHermiteColumn
import Polytime2.Matrices.IntegerPairTranspose

/-! # Certified integer row reduction by transposition

For a positive pivot in a selected row, clear every other entry in that row,
retaining the actual right basis. Reuse the complete column reducer on the
transposed matrix and right basis. The workspace depends on column count and
original word width; callers supply no storage or controller parameters.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter
  | 0 => boundedIndex columns | 1 => boundedIndex rows
  | 2 => integerMatrices rows columns width | 3 => integerMatrices columns columns width

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width name).Carrier sizes) :=
  0 < (arguments 2).val (arguments 1) (arguments 0)

private noncomputable def preparedValues (rows columns width : MvPolynomial Parameter ℕ) (name : Fin 4)
    (sizes : Parameter → ℕ) (arguments : {arguments : ∀ name, (inputs rows columns width name).Carrier sizes //
      allowed rows columns width sizes arguments}) :
    ((integerHermiteColumn columns rows width).inputDomains name).Carrier sizes :=
  match name with
  | 0 => arguments.val 0
  | 1 => arguments.val 1
  | 2 => (integerMatrixTranspose rows columns width).compute sizes ⟨(fun _ => arguments.val 2), trivial⟩
  | 3 => (integerMatrixTranspose columns columns width).compute sizes ⟨(fun _ => arguments.val 3), trivial⟩

private noncomputable def prepared (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerHermiteColumn columns rows width).onResults (inputs rows columns width) (allowed rows columns width)
    (preparedValues rows columns width) (fun _ arguments => arguments.property)

private theorem prepared_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (prepared rows columns width).Realizable := by
  apply (integerHermiteColumn_realizable columns rows width).onResults (inputs rows columns width)
    (allowed rows columns width) (preparedValues rows columns width) (fun _ arguments => arguments.property)
  intro name
  fin_cases name
  · exact Realizable.argument (inputs rows columns width) 0 (allowed rows columns width)
  · exact Realizable.argument (inputs rows columns width) 1 (allowed rows columns width)
  · exact ((integerMatrixTranspose_realizable rows columns width).withArguments (inputs rows columns width)
      (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition (allowed rows columns width) (by intros; trivial)
  · exact ((integerMatrixTranspose_realizable columns columns width).withArguments (inputs rows columns width)
      (MultiTape.oneTape 3) (by intros; rfl)).withPrecondition (allowed rows columns width) (by intros; trivial)

/-- Clear a positive-pivot row and retain the accumulated right transformation. -/
noncomputable def integerHermiteRow (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) :=
  (prepared rows columns width).followedBy
    (integerMatrixPairTranspose columns rows columns columns (hermiteColumnWorkspace columns width)) rfl (by intros; trivial)

theorem integerHermiteRow_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRow rows columns width).Realizable :=
  (prepared_realizable rows columns width).followedBy
    (integerMatrixPairTranspose_realizable columns rows columns columns (hermiteColumnWorkspace columns width)) rfl (by intros; trivial)

/-- The dual computation agrees exactly with the mathematical right-basis traversal. -/
theorem integerHermiteRow_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRow rows columns width).Arguments sizes //
      (integerHermiteRow rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRow rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowPrefix
      (Row := Fin (MvPolynomial.eval sizes rows)) (columns := MvPolynomial.eval sizes columns)
      (arguments.val 0) (arguments.val 1) (MvPolynomial.eval sizes columns) (arguments.val 2).val (arguments.val 3).val := by
  have result := integerHermiteColumn_correct columns rows width sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩
  exact congrArg (fun matrices => (matrices.1.transpose, matrices.2.transpose)) result

/-- The selected row has a positive pivot and is zero outside the source column. -/
theorem integerHermiteRow_entries (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRow rows columns width).Arguments sizes //
      (integerHermiteRow rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRow rows columns width).compute sizes arguments
    0 < result.1.val (arguments.val 1) (arguments.val 0) ∧
      ∀ column, column ≠ arguments.val 0 → result.1.val (arguments.val 1) column = 0 := by
  exact integerHermiteColumn_entries columns rows width sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩

/-- Right-basis accumulation preserves the equation with the original matrix. -/
theorem integerHermiteRow_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRow rows columns width).Arguments sizes //
      (integerHermiteRow rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (equation : left * original * (arguments.val 3).val = (arguments.val 2).val)
    (unit : IsUnit (arguments.val 3).val.det) :
    let result := (integerHermiteRow rows columns width).compute sizes arguments
    left * original * result.2.val = result.1.val ∧ IsUnit result.2.val.det := by
  have transposed : (arguments.val 3).val.transpose * original.transpose * left.transpose = (arguments.val 2).val.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose equation
  have result := integerHermiteColumn_preserves columns rows width sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩
    original.transpose left.transpose transposed (by
      change IsUnit (arguments.val 3).val.transpose.det
      simpa only [Matrix.det_transpose] using unit)
  let changed := (integerHermiteColumn columns rows width).compute sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩
  change left * original * changed.2.val.transpose = changed.1.val.transpose ∧ IsUnit changed.2.val.transpose.det
  constructor
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using congrArg Matrix.transpose result.1
  · simpa only [Matrix.det_transpose] using result.2

/-- The dual traversal preserves completed blocks and their right-basis columns. -/
theorem integerHermiteRow_protected (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRow rows columns width).Arguments sizes //
      (integerHermiteRow rows columns width).precondition sizes arguments})
    (protectedRows : Set (Fin (MvPolynomial.eval sizes rows)))
    (protectedColumns : Set (Fin (MvPolynomial.eval sizes columns)))
    (sourceOutside : arguments.val 0 ∉ protectedColumns)
    (selectedZeros : ∀ column ∈ protectedColumns, (arguments.val 2).val (arguments.val 1) column = 0)
    (earlierZeros : ∀ column ∉ protectedColumns, ∀ row ∈ protectedRows, (arguments.val 2).val row column = 0) :
    let result := (integerHermiteRow rows columns width).compute sizes arguments
    (∀ column ∈ protectedColumns, (∀ row, result.1.val row column = (arguments.val 2).val row column) ∧
      (∀ other, result.2.val other column = (arguments.val 3).val other column)) ∧
    (∀ row ∈ protectedRows, result.1.val row = (arguments.val 2).val row) := by
  have result := integerHermiteColumn_protected columns rows width sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩
    protectedColumns protectedRows sourceOutside selectedZeros earlierZeros
  let changed := (integerHermiteColumn columns rows width).compute sizes
    ⟨(fun name => preparedValues rows columns width name sizes arguments), arguments.property⟩
  change (∀ column ∈ protectedColumns, (∀ row, changed.1.val column row = (arguments.val 2).val row column) ∧
    (∀ other, changed.2.val column other = (arguments.val 3).val other column)) ∧
    (∀ row ∈ protectedRows, (fun column => changed.1.val column row) = (arguments.val 2).val row)
  constructor
  · intro column inside
    exact ⟨fun row => congrFun (result.1 column inside).1 row,
      fun other => congrFun (result.1 column inside).2 other⟩
  · intro row inside
    funext column
    exact result.2 row inside column

end Polytime2.Computation
