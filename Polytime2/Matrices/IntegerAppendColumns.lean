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

import Polytime2.Arrays.Append
import Polytime2.Arrays.ZipWith
import Polytime2.Matrices.IntegerOperations

/-! # Appending rectangular integer matrix columns

Input two ordinary integer matrices with the same row count and magnitude
width. Return their horizontal concatenation at the sum of the column counts.
Row pairing and the bit-preserving array concatenation supply the realization.
This constructor prepares the augmented matrices used for cyclic membership.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def nested (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ) :=
  (arrayZipWith (Empty.elim : Empty → EncodedDomain Parameter)
    ((binaryIntegers width).arrayOfLength firstColumns) ((binaryIntegers width).arrayOfLength secondColumns)
    ((binaryIntegers width).arrayOfLength (firstColumns + secondColumns)) rows
    (fun sizes _ first second => (arrayAppend (binaryIntegers width) firstColumns secondColumns).compute sizes
      ⟨fun _ => (first, second), trivial⟩)).onResults
    (fun choice : Bool => ((binaryIntegers width).arrayOfLength (if choice then secondColumns else firstColumns)).arrayOfLength rows)
    (fun _ _ => True)
    (fun name _ arguments => match name with | .inl impossible => nomatch impossible | .inr false => arguments.val false | .inr true => arguments.val true)
    (by intros; trivial)

private theorem nested_realizable (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ) :
    (nested rows firstColumns secondColumns width).Realizable := by
  let first := (binaryIntegers width).arrayOfLength firstColumns
  let second := (binaryIntegers width).arrayOfLength secondColumns
  let target := (binaryIntegers width).arrayOfLength (firstColumns + secondColumns)
  let operation sizes (_context : ∀ name : Empty, (Empty.elim name : EncodedDomain Parameter).Carrier sizes)
      (left : first.Carrier sizes) (right : second.Carrier sizes) :=
    (arrayAppend (binaryIntegers width) firstColumns secondColumns).compute sizes ⟨fun _ => (left, right), trivial⟩
  let step := arrayZipWithStep (Empty.elim : Empty → EncodedDomain Parameter) first second target operation
  have paired := Realizable.pairOutputs step.inputDomains first second step.precondition
    (fun _ arguments => arguments.val (.inr false)) (fun _ arguments => arguments.val (.inr true))
    (Realizable.argument step.inputDomains (.inr false) step.precondition)
    (Realizable.argument step.inputDomains (.inr true) step.precondition)
  have scalar : step.Realizable := paired.followedBy (arrayAppend_realizable (binaryIntegers width) firstColumns secondColumns)
    rfl (by intros; trivial)
  apply (arrayZipWith_realizable (Empty.elim : Empty → EncodedDomain Parameter) first second target rows operation scalar).onResults _ _ _ (by intros; trivial)
  intro name
  rcases name with impossible | choice
  · exact impossible.elim
  · cases choice
    · exact Realizable.argument _ false _
    · exact Realizable.argument _ true _

/-- Append the columns of two equally bounded rectangular integer matrices. -/
noncomputable def integerMatrixAppendColumns (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  ((nested rows firstColumns secondColumns width).reinterpretInputs
    (fun choice => integerMatrices rows (if choice then secondColumns else firstColumns) width)
    (fun choice sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (fun _ _ => True) (by intros; trivial)).reinterpretOutput
      (integerMatrices rows (firstColumns + secondColumns) width)
      (fun sizes => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm)

/-- Existing mathematical matrix views and rowwise concatenation preserve canonical encodings. -/
theorem integerMatrixAppendColumns_realizable (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ) :
    (integerMatrixAppendColumns rows firstColumns secondColumns width).Realizable := by
  have viewed := (nested_realizable rows firstColumns secondColumns width).reinterpretInputs
    (fun choice => integerMatrices rows (if choice then secondColumns else firstColumns) width)
    (fun choice sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (by intro choice sizes; cases choice <;> exact integerMatrices_nested_width _ _ _ sizes)
    (by intro choice sizes value; cases choice <;> exact integerMatrices_nested_encode_bits _ _ _ sizes value)
    (fun _ _ => True) (by intros; trivial)
  apply viewed.reinterpretOutput
    (integerMatrices rows (firstColumns + secondColumns) width)
    (fun sizes => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm)
  · intro sizes
    exact integerMatrices_nested_width _ _ _ sizes
  · intro sizes value
    change ArrayEncoding.bits ((integerMatrices rows (firstColumns + secondColumns) width).encode sizes
      ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)) =
      ArrayEncoding.bits ((((binaryIntegers width).arrayOfLength (firstColumns + secondColumns)).arrayOfLength rows).encode sizes value)
    rw [arrayOfLength_encode_bits]
    simpa using integerMatrices_nested_encode_bits rows (firstColumns + secondColumns) width sizes
      ((IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)

/-- The result is ordinary rowwise horizontal concatenation in the summed column dimension. -/
theorem integerMatrixAppendColumns_correct (rows firstColumns secondColumns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerMatrixAppendColumns rows firstColumns secondColumns width).Arguments sizes) :
    ((integerMatrixAppendColumns rows firstColumns secondColumns width).compute sizes ⟨arguments, trivial⟩).val =
      fun row column => Fin.append ((arguments false).val row) ((arguments true).val row)
        (Fin.cast (map_add (MvPolynomial.eval sizes) firstColumns secondColumns) column) := by
  funext row column
  let first : Fin (MvPolynomial.eval sizes firstColumns) → (binaryIntegers width).Carrier sizes :=
    fun index => ⟨(arguments false).val row index, (arguments false).property _ _⟩
  let second : Fin (MvPolynomial.eval sizes secondColumns) → (binaryIntegers width).Carrier sizes :=
    fun index => ⟨(arguments true).val row index, (arguments true).property _ _⟩
  change (Fin.append first second (Fin.cast (map_add (MvPolynomial.eval sizes) firstColumns secondColumns) column)).val = _
  generalize Fin.cast (map_add (MvPolynomial.eval sizes) firstColumns secondColumns) column = index
  cases index using Fin.addCases <;> simp [first, second]

end Polytime2.Computation
