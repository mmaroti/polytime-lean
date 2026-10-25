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

import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.Tabulate
import Polytime2.Arrays.BoundedPositions
import Polytime2.Arrays.AllTrue
import Polytime2.Arrays.Transform
import Polytime2.Computation.Equality
import Polytime2.Computation.Specification

/-! # Certified diagonality testing for integer matrices

A square matrix is diagonal precisely when every off-diagonal entry is zero.
Tabulate these entry conditions, then reduce each row and the row results by
Boolean conjunction. Empty dimensions satisfy the universal condition.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def diagonalFlags (dimension width : MvPolynomial Parameter ℕ) :=
  matrixTabulate (fun _ : Unit => integerMatrices dimension dimension width) booleans dimension dimension
    (fun _ arguments row column => decide (row = column) || decide ((arguments ()).val row column = 0))

private theorem diagonalFlags_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (diagonalFlags dimension width).Realizable := by
  classical
  let context : Unit → EncodedDomain Parameter := fun _ => integerMatrices dimension dimension width
  let operation sizes (arguments : ∀ name, (context name).Carrier sizes)
      (row column : Fin (MvPolynomial.eval sizes dimension)) :=
    decide (row = column) || decide ((arguments ()).val row column = 0)
  let step := matrixTabulateStep context booleans dimension dimension operation
  have equal := (elementsEqual_realizable (arrayPosition dimension)).withArguments step.inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name <;> rfl)
  have row := (arrayPositionToIndex_realizable dimension).withArguments step.inputDomains
    (MultiTape.oneTape (.inr false)) (by intros; rfl)
  have column := (arrayPositionToIndex_realizable dimension).withArguments step.inputDomains
    (MultiTape.oneTape (.inr true)) (by intros; rfl)
  have entry := (integerMatrixEntry_realizable dimension dimension width).onResults
    step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inr false) | 1 => arguments.val (.inr true) | 2 => arguments.val (.inl ()))
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact row
      · exact column
      · exact Realizable.argument step.inputDomains (.inl ()) step.precondition)
  have zero := entry.followedBy (integerIsZero_realizable width) rfl (by intros; trivial)
  have combined := (booleanOperation_realizable (fun values : Bool → Bool => values false || values true)).onResults
    step.inputDomains step.precondition
    (fun choice _ arguments => match choice with
      | false => decide (arguments.val (.inr false) = arguments.val (.inr true))
      | true => decide ((arguments.val (.inl ())).val (arguments.val (.inr false)) (arguments.val (.inr true)) = 0))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact equal
      · exact zero)
  have scalar : step.Realizable := combined.withSpecification step.precondition step.compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Bool.eq_iff_iff.mpr
      simp [Computation.onResults, booleanOperation, step, matrixTabulateStep, operation])
  exact matrixTabulate_realizable context booleans dimension dimension operation scalar

private noncomputable def nestedDiagonalFlags (dimension width : MvPolynomial Parameter ℕ) :=
  (diagonalFlags dimension width).reinterpretOutput
    ((booleans.arrayOfLength dimension).arrayOfLength dimension) (fun _ value => value)

private theorem nestedDiagonalFlags_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (nestedDiagonalFlags dimension width).Realizable := by
  apply (diagonalFlags_realizable dimension width).reinterpretOutput
  · intro sizes
    simp [diagonalFlags, matrixTabulate, EncodedDomain.width, EncodedDomain.matrix,
      arrayOfLength, EncodedDomain.reindex, map_mul]
  · intro sizes value
    exact (matrix_nested_encode_bits booleans dimension dimension sizes value).symm

/-- Decide the ordinary universal off-diagonal zero condition. -/
private noncomputable def implementation (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((nestedDiagonalFlags dimension width).followedBy
    (mapArray (booleans.arrayOfLength dimension) booleans dimension
      (fun sizes flags => (arrayAllTrue dimension).compute sizes ⟨fun _ => flags, trivial⟩)) rfl (by intros; trivial)).followedBy
    (arrayAllTrue dimension) rfl (by intros; trivial)

/-- Entry reads, equality, zero tests, and both universal reductions are realized. -/
private theorem implementation_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (implementation dimension width).Realizable :=
  ((nestedDiagonalFlags_realizable dimension width).followedBy
    (mapArray_realizable (booleans.arrayOfLength dimension) booleans dimension
      (fun sizes flags => (arrayAllTrue dimension).compute sizes ⟨fun _ => flags, trivial⟩)
      (arrayAllTrue_realizable dimension)) rfl (by intros; trivial)).followedBy
    (arrayAllTrue_realizable dimension) rfl (by intros; trivial)

/-- The stopping test is true exactly for diagonal matrices, including dimension zero. -/
private theorem implementation_correct (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (matrix : (integerMatrices dimension dimension width).Carrier sizes) :
    (implementation dimension width).compute sizes ⟨fun _ => matrix, trivial⟩ = true ↔
      ∀ row column, row ≠ column → matrix.val row column = 0 := by
  classical
  change (arrayAllTrue dimension).compute sizes ⟨fun _ => fun row =>
    (arrayAllTrue dimension).compute sizes ⟨fun _ => fun column =>
      decide (row = column) || decide (matrix.val row column = 0), trivial⟩, trivial⟩ = true ↔ _
  rw [arrayAllTrue_correct]
  constructor
  · intro all row column different
    have flag := ((arrayAllTrue_correct dimension sizes _).mp (all row)) column
    simp only [Bool.or_eq_true, decide_eq_true_eq] at flag
    exact flag.resolve_left different
  · intro diagonal row
    apply (arrayAllTrue_correct dimension sizes _).mpr
    intro column
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases same : row = column
    · exact Or.inl same
    · exact Or.inr (diagonal row column same)

/-- Decide ordinary mathematical diagonality, including dimension zero. -/
noncomputable def integerMatrixIsDiagonal (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  decision (fun _ => integerMatrices dimension dimension width) (fun _ _ => True)
    (fun _ arguments => ∀ row column, row ≠ column → (arguments ()).val row column = 0)

theorem integerMatrixIsDiagonal_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (integerMatrixIsDiagonal dimension width).Realizable :=
  (implementation_realizable dimension width).decision _
    (fun sizes arguments _valid => implementation_correct dimension width sizes (arguments ()))

/-- The result is true exactly for diagonal matrices. -/
theorem integerMatrixIsDiagonal_correct (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (matrix : (integerMatrices dimension dimension width).Carrier sizes) :
    (integerMatrixIsDiagonal dimension width).compute sizes ⟨fun _ => matrix, trivial⟩ = true ↔
      ∀ row column, row ≠ column → matrix.val row column = 0 :=
  decision_correct _ _ _ sizes ⟨fun _ => matrix, trivial⟩

end Polytime2.Computation
