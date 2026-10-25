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

import Polytime2.Computation.Specification
import Polytime2.Matrices.IntegerPairTranspose
import Polytime2.Matrices.EuclideanMath
import Polytime2.Matrices.IntegerOperations
import Polytime2.Arithmetic.SignedDivision

/-! # Certified Euclidean row reduction with left-basis tracking

Inputs are distinct source and target rows, a column, the current integer
matrix, and its left basis. The source pivot must be positive. Compute one
negated quotient from the current matrix and apply it to both matrices. The
source row stays unchanged and the selected target entry becomes the Euclidean
remainder. Widths are derived internally; no global sweep bound is asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 5 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 0) (arguments 2)

private noncomputable def coefficient (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) where
  inputDomains := inputs rows columns width
  outputDomain := binaryIntegers width
  precondition := allowed rows columns width
  compute _ arguments := ⟨-((arguments.val 3).val (arguments.val 1) (arguments.val 2) /
    (arguments.val 3).val (arguments.val 0) (arguments.val 2)), by
    rw [Int.natAbs_neg]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt ((arguments.val 3).property _ _)⟩

private theorem coefficient_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (coefficient rows columns width).Realizable := by
  let computation := coefficient rows columns width
  let entry (source : Bool) sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (binaryIntegers width).Carrier sizes :=
    ⟨(arguments.val 3).val (if source then arguments.val 0 else arguments.val 1) (arguments.val 2),
      (arguments.val 3).property _ _⟩
  have entryReady (source : Bool) :
      (Computation.mk computation.inputDomains (binaryIntegers width) computation.precondition (entry source)).Realizable := by
    have selected := (integerMatrixEntry_realizable rows columns width).onArguments computation.inputDomains computation.precondition
      (fun name => match name with
        | 0 => if source then 0 else 1
        | 1 => 2
        | 2 => 3) (by
          intro name
          fin_cases name
          · cases source
            · rfl
            · rfl
          · rfl
          · rfl) (by intros; trivial)
    exact selected.withSpecification computation.precondition (entry source)
      (by intros; assumption) (by intro sizes arguments valid; cases source <;> rfl)
  have divided := (integerQuotient_realizable width).onResults computation.inputDomains computation.precondition entry
    (fun _ arguments => ne_of_gt arguments.property.2) entryReady
  have negated := divided.followedBy (integerNegate_realizable width) rfl (by intros; trivial)
  exact negated.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

private noncomputable def host (rows columns width : MvPolynomial Parameter ℕ) :=
  Sum.elim (inputs rows columns width) (fun _ : Unit => binaryIntegers width)

private def selection (left : Bool) : Fin 4 ↪ Fin 5 ⊕ Unit :=
  ⟨(fun name => match name with
    | 0 => .inl 1 | 1 => .inl 0 | 2 => .inr () | 3 => .inl (if left then 4 else 3)), by
    intro first second equal
    cases left <;> fin_cases first <;> fin_cases second <;> simp_all⟩

private noncomputable def application (rows columns width : MvPolynomial Parameter ℕ) (left : Bool) :=
  (integerRowAdd rows (if left then rows else columns) width).withArguments (host rows columns width)
    (selection left) (by intro name; cases left <;> fin_cases name <;> rfl)

private theorem application_realizable (rows columns width : MvPolynomial Parameter ℕ) (left : Bool) :
    (application rows columns width left).Realizable :=
  (integerRowAdd_realizable rows (if left then rows else columns) width).withArguments (host rows columns width)
    (selection left) (by intro name; cases left <;> fin_cases name <;> rfl)

private noncomputable def stage (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5 ⊕ Unit) where
  inputDomains := host rows columns width
  outputDomain := (integerMatrices rows columns (2 * width + 1)).prod (integerMatrices rows rows (2 * width + 1))
  precondition sizes arguments := allowed rows columns width sizes (fun name => arguments (.inl name))
  compute sizes arguments := ((application rows columns width false).compute sizes ⟨arguments.val, trivial⟩,
    (application rows columns width true).compute sizes ⟨arguments.val, trivial⟩)

private theorem stage_realizable (rows columns width : MvPolynomial Parameter ℕ) : (stage rows columns width).Realizable := by
  let computation := stage rows columns width
  have first := (application_realizable rows columns width false).withPrecondition computation.precondition (by intros; trivial)
  have second := (application_realizable rows columns width true).withPrecondition computation.precondition (by intros; trivial)
  exact first.prodMk second

/-- Reduce a target entry modulo a positive pivot and update the actual left basis. -/
private noncomputable def rowImplementation (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  (coefficient rows columns width).letThen (stage rows columns width) (fun _ => rfl) rfl (by intros; assumption)

private theorem rowImplementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (rowImplementation rows columns width).Realizable :=
  (coefficient_realizable rows columns width).letThen (stage_realizable rows columns width)
    (fun _ => rfl) rfl (by intros; assumption)

private noncomputable def columnInputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 5 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex columns
  | 2 => boundedIndex rows
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices columns columns width

private def columnAllowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (columnInputs rows columns width name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 2) (arguments 0)

private noncomputable def columnPrepared (rows columns width : MvPolynomial Parameter ℕ) :=
  (rowImplementation columns rows width).onResults (columnInputs rows columns width) (columnAllowed rows columns width)
    (fun name sizes arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => arguments.val 2
      | 3 => (integerMatrixTranspose rows columns width).compute sizes ⟨(fun _ => arguments.val 3), trivial⟩
      | 4 => (integerMatrixTranspose columns columns width).compute sizes ⟨(fun _ => arguments.val 4), trivial⟩)
    (fun _ arguments => arguments.property)

private theorem columnPrepared_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (columnPrepared rows columns width).Realizable := by
  let computation := columnPrepared rows columns width
  apply (rowImplementation_realizable columns rows width).onResults computation.inputDomains computation.precondition
    _ (by
      intro sizes arguments
      change arguments.val 0 ≠ arguments.val 1 ∧
        0 < (arguments.val 3).val (arguments.val 2) (arguments.val 0)
      exact arguments.property)
  intro name
  fin_cases name
  · exact Realizable.argument computation.inputDomains 0 computation.precondition
  · exact Realizable.argument computation.inputDomains 1 computation.precondition
  · exact Realizable.argument computation.inputDomains 2 computation.precondition
  · exact ((integerMatrixTranspose_realizable rows columns width).withArguments computation.inputDomains
      (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition computation.precondition (by intros; trivial)
  · exact ((integerMatrixTranspose_realizable columns columns width).withArguments computation.inputDomains
      (MultiTape.oneTape 4) (fun _ => rfl)).withPrecondition computation.precondition (by intros; trivial)

/-- Reduce a column entry modulo a positive pivot and update the actual right basis. -/
private noncomputable def columnImplementation (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  (columnPrepared rows columns width).followedBy (integerMatrixPairTranspose columns rows columns columns (2 * width + 1)) rfl (by intros; trivial)

private theorem columnImplementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (columnImplementation rows columns width).Realizable :=
  (columnPrepared_realizable rows columns width).followedBy (integerMatrixPairTranspose_realizable columns rows columns columns (2 * width + 1)) rfl (by intros; trivial)

/-- The mathematical row remainder operation and its actual basis. -/
noncomputable def integerRowRemainderWithLeft (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  specificationBy (inputs rows columns width)
    ((integerMatrices rows columns (2 * width + 1)).prod
      (integerMatrices rows rows (2 * width + 1)))
    (allowed rows columns width) (fun _ result => (result.1.val, result.2.val))
    (fun sizes arguments => IntegerMatrix.rowRemainderWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val)
    (fun sizes arguments => ⟨(rowImplementation rows columns width).compute sizes arguments, rfl⟩)

theorem integerRowRemainderWithLeft_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowRemainderWithLeft rows columns width).Realizable := by
  apply (rowImplementation_realizable rows columns width).specificationBy
  · intro sizes
    exact Subtype.val_injective.prodMap Subtype.val_injective
  · intros
    rfl

/-- The ordinary matrix operation, independent of quotient preparation. -/
theorem integerRowRemainderWithLeft_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRowRemainderWithLeft rows columns width).Arguments sizes //
      (integerRowRemainderWithLeft rows columns width).precondition sizes arguments}) :
    let result := (integerRowRemainderWithLeft rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.rowRemainderWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := by
  exact specificationBy_correct _ (integerRowRemainderWithLeft rows columns width).outputDomain _
    (fun _ result => (result.1.val, result.2.val)) _ _ sizes arguments

/-- The mathematical column remainder operation and its actual basis. -/
noncomputable def integerColumnRemainderWithRight (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) :=
  specificationBy (columnInputs rows columns width)
    ((integerMatrices rows columns (2 * width + 1)).prod
      (integerMatrices columns columns (2 * width + 1)))
    (columnAllowed rows columns width) (fun _ result => (result.1.val, result.2.val))
    (fun sizes arguments => IntegerMatrix.columnRemainderWithRight
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val)
    (fun sizes arguments => ⟨(columnImplementation rows columns width).compute sizes arguments, rfl⟩)

theorem integerColumnRemainderWithRight_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnRemainderWithRight rows columns width).Realizable := by
  apply (columnImplementation_realizable rows columns width).specificationBy
  · intro sizes
    exact Subtype.val_injective.prodMap Subtype.val_injective
  · intros
    rfl

/-- The ordinary matrix operation, independent of quotient preparation. -/
theorem integerColumnRemainderWithRight_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerColumnRemainderWithRight rows columns width).Arguments sizes //
      (integerColumnRemainderWithRight rows columns width).precondition sizes arguments}) :
    let result := (integerColumnRemainderWithRight rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.columnRemainderWithRight
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := by
  exact specificationBy_correct _ (integerColumnRemainderWithRight rows columns width).outputDomain _
    (fun _ result => (result.1.val, result.2.val)) _ _ sizes arguments

end Polytime2.Computation
