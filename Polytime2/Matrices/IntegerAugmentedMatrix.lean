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

import Polytime2.Matrices.IntegerAppendColumns
import Polytime2.Matrices.IntegerRectangularDiagonal
import Polytime2.Matrices.AugmentedMath

/-! # Constructing cyclic-query augmented matrices

Input an ordinary integer generator matrix and a bounded natural modulus for
each row. Append the diagonal modulus block, deriving a common entry width
internally. The construction is total; positive moduli are required only when
interpreting all cyclic coordinates as finite groups.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Entry capacity for the generator and natural-modulus blocks. -/
noncomputable def integerAugmentedWidth (generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :=
  generatorWidth + (modulusWidth + 1)

private noncomputable def inputs (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    Bool → EncodedDomain Parameter :=
  fun choice => if choice then (binaryNaturalsOfWidth modulusWidth).arrayOfLength rows
    else integerMatrices rows generators generatorWidth

private noncomputable def left (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :=
  (integerMatrixWiden rows generators generatorWidth (modulusWidth + 1)
    (integerAugmentedWidth generatorWidth modulusWidth) rfl).withArguments
    (inputs rows generators generatorWidth modulusWidth) (MultiTape.oneTape false) (by intros; rfl)

private noncomputable def right (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :=
  ((integerRectangularDiagonal rows rows rows modulusWidth).withArguments
    (inputs rows generators generatorWidth modulusWidth) (MultiTape.oneTape true) (by intros; rfl)).followedBy
    (integerMatrixWiden rows rows (modulusWidth + 1) generatorWidth
      (integerAugmentedWidth generatorWidth modulusWidth) (by unfold integerAugmentedWidth; ring)) rfl (by intros; trivial)

private theorem left_realizable (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    (left rows generators generatorWidth modulusWidth).Realizable :=
  (integerMatrixWiden_realizable rows generators generatorWidth (modulusWidth + 1)
    (integerAugmentedWidth generatorWidth modulusWidth) rfl).withArguments _ (MultiTape.oneTape false) (by intros; rfl)

private theorem right_realizable (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    (right rows generators generatorWidth modulusWidth).Realizable :=
  ((integerRectangularDiagonal_realizable rows rows rows modulusWidth).withArguments
    (inputs rows generators generatorWidth modulusWidth) (MultiTape.oneTape true) (by intros; rfl)).followedBy
    (integerMatrixWiden_realizable rows rows (modulusWidth + 1) generatorWidth
      (integerAugmentedWidth generatorWidth modulusWidth) (by unfold integerAugmentedWidth; ring)) rfl (by intros; trivial)

/-- Append the modulus diagonal without discarding any generator columns. -/
noncomputable def integerAugmentedMatrix (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (integerMatrixAppendColumns rows generators rows (integerAugmentedWidth generatorWidth modulusWidth)).onResults
    (inputs rows generators generatorWidth modulusWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (left rows generators generatorWidth modulusWidth).compute sizes arguments
      | true => (right rows generators generatorWidth modulusWidth).compute sizes arguments) (by intros; trivial)

/-- Diagonal construction, widening, and horizontal concatenation are realized. -/
theorem integerAugmentedMatrix_realizable (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ) :
    (integerAugmentedMatrix rows generators generatorWidth modulusWidth).Realizable := by
  apply (integerMatrixAppendColumns_realizable rows generators rows (integerAugmentedWidth generatorWidth modulusWidth)).onResults
    (inputs rows generators generatorWidth modulusWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact left_realizable rows generators generatorWidth modulusWidth
  · exact right_realizable rows generators generatorWidth modulusWidth

/-- The result is exactly the ordinary augmented matrix in its summed column indexing. -/
theorem integerAugmentedMatrix_correct (rows generators generatorWidth modulusWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerAugmentedMatrix rows generators generatorWidth modulusWidth).Arguments sizes) :
    ((integerAugmentedMatrix rows generators generatorWidth modulusWidth).compute sizes ⟨arguments, trivial⟩).val =
      (IntegerMatrix.augmentedMatrix (arguments false).val (fun row => ((arguments true row).val : ℤ))).submatrix id
        (fun column => finSumFinEquiv.symm (Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column)) := by
  have appended := integerMatrixAppendColumns_correct rows generators rows (integerAugmentedWidth generatorWidth modulusWidth)
    sizes (fun choice => match choice with
      | false => (left rows generators generatorWidth modulusWidth).compute sizes ⟨arguments, trivial⟩
      | true => (right rows generators generatorWidth modulusWidth).compute sizes ⟨arguments, trivial⟩)
  apply appended.trans
  have diagonal : IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes rows)
      (fun row => (arguments true row).val) = Matrix.diagonal (fun row => ((arguments true row).val : ℤ)) := by
    ext row column
    by_cases same : row = column
    · subst column
      simp [IntegerMatrix.rectangularDiagonal, row.isLt]
    · have different : row.val ≠ column.val := fun equal => same (Fin.ext equal)
      simp [IntegerMatrix.rectangularDiagonal, different, Matrix.diagonal_apply_ne _ same]
  change (fun row column => Fin.append ((arguments false).val row)
    (IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes rows)
      (fun row => (arguments true row).val) row) (Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column)) = _
  rw [diagonal]
  funext row column
  change Fin.append ((arguments false).val row) (Matrix.diagonal (fun row => ((arguments true row).val : ℤ)) row)
    (Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column) =
      (Matrix.fromCols (arguments false).val (Matrix.diagonal (fun row => ((arguments true row).val : ℤ)))) row
        (finSumFinEquiv.symm (Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column))
  generalize Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column = index
  cases index using Fin.addCases <;> simp

end Polytime2.Computation
