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

import Polytime2.StandardMatrixRowsPresentation
import Polytime2.MatrixRowField
import Polytime2.FieldRow

/-! # Standard-convention finite-field matrix row operations

The existing mathematical field identities specialize the shared row machine.
Inputs and outputs are ordinary matrices, with fixed field tables chosen by
the specialization and all size tapes supplied at runtime.
-/

namespace Polytime2.StandardMatrixRowField

open CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- The target row is multiplied by the runtime coefficient. -/
theorem scale_contract (enumeration : Scalar ≃ Fin cardinality) :
    let domain := FieldRow.scalarDomain enumeration
    CallingConvention.Realizes (mathematicalDomains domain) readOnly sizeTapes
      (machine false domain (fun _ => MatrixRowField.scale (Scalar := Scalar)))
      (entry (domain.width Empty.elim)) (exit (domain.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (_sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        output ⟨dataTape 5, rfl⟩ = MatrixOperations.scaleRow (Scalar := Scalar) (input ⟨inputTape, rfl⟩)
          ⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩ (input ⟨dataTape 3, rfl⟩)) := by
  intro domain
  apply (mathematical_contract false domain (fun _ => MatrixRowField.scale (Scalar := Scalar))).postcondition
  intro sizes input output correct
  obtain ⟨sourceValid, targetValid, correct⟩ := correct
  exact ⟨sourceValid, targetValid, correct.trans (MatrixRowField.scale_transform (Scalar := Scalar) _ _ _ _)⟩

/-- Inversion is a specialization-fixed finite-field operation. The caller's
pivot hypothesis supplies nonzeroness when row equivalence is needed. -/
theorem normalize_contract (enumeration : Scalar ≃ Fin cardinality) :
    let domain := FieldRow.scalarDomain enumeration
    CallingConvention.Realizes (mathematicalDomains domain) readOnly sizeTapes
      (machine false domain (fun _ => MatrixRowField.normalize (Scalar := Scalar)))
      (entry (domain.width Empty.elim)) (exit (domain.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (_sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        output ⟨dataTape 5, rfl⟩ = MatrixOperations.scaleRow (Scalar := Scalar) (input ⟨inputTape, rfl⟩)
          ⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩ ((input ⟨dataTape 3, rfl⟩) : Scalar)⁻¹) := by
  intro domain
  apply (mathematical_contract false domain (fun _ => MatrixRowField.normalize (Scalar := Scalar))).postcondition
  intro sizes input output correct
  obtain ⟨sourceValid, targetValid, correct⟩ := correct
  exact ⟨sourceValid, targetValid, correct.trans (MatrixRowField.normalize_transform (Scalar := Scalar) _ _ _ _)⟩

/-- Add the coefficient times the source row to the target row, including
coincident indices; all entries used in the sum come from the original matrix. -/
theorem add_contract (enumeration : Scalar ≃ Fin cardinality) :
    let domain := FieldRow.scalarDomain enumeration
    CallingConvention.Realizes (mathematicalDomains domain) readOnly sizeTapes
      (machine false domain (fun _ => MatrixRowField.add (Scalar := Scalar)))
      (entry (domain.width Empty.elim)) (exit (domain.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        let source : Fin (sizes 1) := ⟨(input ⟨dataTape 0, rfl⟩).val, sourceValid⟩
        let target : Fin (sizes 1) := ⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩
        let matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar := input ⟨inputTape, rfl⟩
        let coefficient : Scalar := input ⟨dataTape 3, rfl⟩
        output ⟨dataTape 5, rfl⟩ = Function.update matrix target
          (fun column => matrix target column + coefficient * matrix source column)) := by
  intro domain
  apply (mathematical_contract false domain (fun _ => MatrixRowField.add (Scalar := Scalar))).postcondition
  intro sizes input output correct
  obtain ⟨sourceValid, targetValid, correct⟩ := correct
  exact ⟨sourceValid, targetValid, correct.trans (MatrixRowField.add_transform (Scalar := Scalar) _ _ _ _)⟩

/-- This postcondition packages the row-add step used when clearing a pivot
entry. The caller supplies the scalar coefficient from its prior lookup. -/
theorem clear_target_contract (enumeration : Scalar ≃ Fin cardinality) :
    let domain := FieldRow.scalarDomain enumeration
    CallingConvention.Realizes (mathematicalDomains domain) readOnly sizeTapes
      (machine false domain (fun _ => MatrixRowField.add (Scalar := Scalar)))
      (entry (domain.width Empty.elim)) (exit (domain.width Empty.elim))
      (fun sizes input =>
        let source : Fin (2 ^ sizes 0) := input ⟨dataTape 0, rfl⟩
        let target : Fin (2 ^ sizes 0) := input ⟨dataTape 1, rfl⟩
        let matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar :=
          input ⟨inputTape, rfl⟩
        let coefficient : Scalar := input ⟨dataTape 3, rfl⟩
        ∃ (sourceValid : source.val < sizes 1)
          (targetValid : target.val < sizes 1),
          sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0 ∧
          ∃ column : Fin (sizes 2),
            matrix ⟨source.val, sourceValid⟩ column = 1 ∧
            coefficient = -matrix ⟨target.val, targetValid⟩ column)
      (fun sizes input output =>
        let source : Fin (2 ^ sizes 0) := input ⟨dataTape 0, rfl⟩
        let target : Fin (2 ^ sizes 0) := input ⟨dataTape 1, rfl⟩
        let matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar :=
          input ⟨inputTape, rfl⟩
        let coefficient : Scalar := input ⟨dataTape 3, rfl⟩
        ∃ (sourceValid : source.val < sizes 1)
          (targetValid : target.val < sizes 1)
          (column : Fin (sizes 2)),
          output ⟨dataTape 5, by decide⟩ = Function.update matrix
            ⟨target.val, targetValid⟩
            (fun index => matrix ⟨target.val, targetValid⟩ index +
              coefficient * matrix ⟨source.val, sourceValid⟩ index) ∧
          output ⟨dataTape 5, by decide⟩ ⟨target.val, targetValid⟩ column =
            (0 : Scalar)) := by
  classical
  intro domain
  obtain ⟨sizeReadOnly, halts, bound, execute⟩ :=
    add_contract enumeration
  refine ⟨sizeReadOnly, halts, bound, ?_⟩
  intro sizes input initial valid represented headers
  rcases valid with ⟨sourceValid, targetValid, columnsFit, capacity,
    column, pivotOne, coefficientEq⟩
  have baseValid :
      (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
      (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
      sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0 :=
    ⟨sourceValid, targetValid, columnsFit, capacity⟩
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute sizes input initial baseValid represented headers
  obtain ⟨outputSourceValid, outputTargetValid, matrixResult⟩ := correct
  let source : Fin (sizes 1) :=
    ⟨(input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val, outputSourceValid⟩
  let target : Fin (sizes 1) :=
    ⟨(input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val, outputTargetValid⟩
  let matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar :=
    input ⟨inputTape, rfl⟩
  let coefficient : Scalar := input ⟨dataTape 3, rfl⟩
  have sourceEq : source = ⟨(input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val,
      sourceValid⟩ := Fin.ext rfl
  have targetEq : target = ⟨(input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val,
      targetValid⟩ := Fin.ext rfl
  have pivotValue : matrix source column = 1 := by
    simpa [matrix, source, sourceEq] using pivotOne
  have cancelCoefficient : coefficient = -matrix target column := by
    simpa [matrix, coefficient, target, targetEq] using coefficientEq
  refine ⟨ticks, output, final, cost, trace, ?_, canonical⟩
  refine ⟨outputSourceValid, outputTargetValid, column, ?_, ?_⟩
  · simpa [source, target, matrix, coefficient] using matrixResult
  · have matrixResult' : output ⟨dataTape 5, by decide⟩ = Function.update matrix target
        (fun index => matrix target index + coefficient * matrix source index) := by
      simpa [source, target, matrix, coefficient] using matrixResult
    have entryResult := congrArg (fun result : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar =>
      result target column) matrixResult'
    have updateAtColumn := congrFun
      (Function.update_self target
        (fun index => matrix target index + coefficient * matrix source index) matrix) column
    rw [updateAtColumn] at entryResult
    have zeroValue : matrix target column + coefficient * matrix source column = 0 := by
      rw [cancelCoefficient, pivotValue]
      ring
    exact entryResult.trans zeroValue

omit [Field Scalar] in
/-- Swapping writes both selected rows and also permits identical indices. -/
theorem swap_contract (enumeration : Scalar ≃ Fin cardinality) :
    let domain := FieldRow.scalarDomain enumeration
    CallingConvention.Realizes (mathematicalDomains domain) readOnly sizeTapes
      (machine true domain (fun _ => MatrixRowField.swap (Scalar := Scalar)))
      (entry (domain.width Empty.elim)) (exit (domain.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        output ⟨dataTape 5, rfl⟩ = MatrixOperations.swapRows (Scalar := Scalar) (input ⟨inputTape, rfl⟩)
          ⟨(input ⟨dataTape 0, rfl⟩).val, sourceValid⟩ ⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩) := by
  intro domain
  apply (mathematical_contract true domain (fun _ => MatrixRowField.swap (Scalar := Scalar))).postcondition
  intro sizes input output correct
  obtain ⟨sourceValid, targetValid, correct⟩ := correct
  exact ⟨sourceValid, targetValid, correct.trans (MatrixRowField.swap_transform (Scalar := Scalar) _ _ _ _)⟩

end Polytime2.StandardMatrixRowField
