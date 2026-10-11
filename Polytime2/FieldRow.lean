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

import Polytime2.TableTraversal
import Polytime2.Matrix

/-! # Finite-field operations on stored rows

Coefficients are runtime data on a stationary tape. Row length varies at
runtime, while the field, arithmetic tables, and controller stay fixed.
These routines operate on row buffers; selecting rows in a matrix is separate.
-/

namespace Polytime2.FieldRow

open MultiTape TableTraversal

-- scalarLevel: the specialization-fixed finite field carrier.
universe scalarLevel
variable {Scalar : Type scalarLevel} [Field Scalar] [DecidableEq Scalar]
variable {rows columns : ℕ}

local instance fieldScalarInhabited : Inhabited Scalar := ⟨0⟩

def scaleTable (coefficient : Scalar) (entry : Unit → Scalar) : Unit → Scalar :=
  fun _ => coefficient * entry ()

def addTable (coefficient : Scalar) (entries : Bool → Scalar) : Bool → Scalar :=
  fun target => if target then entries true + coefficient * entries false else entries false

def swapTable (_coefficient : Scalar) (entries : Bool → Scalar) : Bool → Scalar :=
  fun target => entries (!target)

def rowFrame (parameter : Turing.Tape (Symbol Scalar))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (target : Fin rows)
    (left right : List (Symbol Scalar)) : Tapes (fun _ : TapeName Unit => Symbol Scalar) :=
  frame parameter (fun _ => some none :: left)
    (fun _ => word (List.ofFn (matrix target)) ++ none :: right)

def pairFrame (parameter : Turing.Tape (Symbol Scalar))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows)
    (left right : Bool → List (Symbol Scalar)) : Tapes (fun _ : TapeName Bool => Symbol Scalar) :=
  frame parameter (fun name => some none :: left name)
    (fun name => word (List.ofFn (matrix (if name then target else source))) ++ none :: right name)

/-- Scaling works even for coefficient zero; invertibility is a separate contract. -/
theorem scale_steps (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (target : Fin rows)
    (left right : List (Symbol Scalar)) :
    Steps (machine () (scaleTable (Scalar := Scalar))) (2 * columns + 3)
      (0, rowFrame parameter matrix target left right)
      (2, rowFrame parameter (MatrixOperations.scaleRow matrix target coefficient) target left right) := by
  have trace := TableTraversal.steps () (scaleTable (Scalar := Scalar)) parameter coefficient parameterHead
    (List.ofFn (fun column : Fin columns => fun _ : Unit => matrix target column))
    (fun _ => left) (fun _ => right)
  simpa [rowFrame, word, List.map_ofFn, Function.comp_def, scaleTable, MatrixOperations.scaleRow] using trace

/-- A runtime pivot coefficient can be inverted through the fixed field table. -/
theorem normalize_steps (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (target : Fin rows)
    (left right : List (Symbol Scalar)) :
    Steps (machine () (fun coefficient => scaleTable (coefficient⁻¹ : Scalar))) (2 * columns + 3)
      (0, rowFrame parameter matrix target left right)
      (2, rowFrame parameter (MatrixOperations.scaleRow matrix target coefficient⁻¹) target left right) := by
  have trace := TableTraversal.steps () (fun coefficient => scaleTable (coefficient⁻¹ : Scalar))
    parameter coefficient parameterHead
    (List.ofFn (fun column : Fin columns => fun _ : Unit => matrix target column))
    (fun _ => left) (fun _ => right)
  simpa [rowFrame, word, List.map_ofFn, Function.comp_def, scaleTable, MatrixOperations.scaleRow] using trace

/-- Source and target row buffers are separate tapes. The source is unchanged. -/
theorem add_steps (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows)
    (distinct : source ≠ target) (left right : Bool → List (Symbol Scalar)) :
    Steps (machine false (addTable (Scalar := Scalar))) (2 * columns + 3)
      (0, pairFrame parameter matrix source target left right)
      (2, pairFrame parameter (Function.update matrix target
        (fun column => matrix target column + coefficient * matrix source column)) source target left right) := by
  have trace := TableTraversal.steps false (addTable (Scalar := Scalar)) parameter coefficient parameterHead
    (List.ofFn (fun column : Fin columns => fun name : Bool => matrix (if name then target else source) column))
    left right
  convert trace using 1
  · simp
  · simp [pairFrame, word, List.map_ofFn, Function.comp_def]
  · congr 2
    funext name
    cases name with
    | inl name => rfl
    | inr name =>
      cases name <;> simp [pairFrame, frame, word, List.map_ofFn, Function.comp_def, addTable, Function.update, distinct]

/-- Exchanging equal rows is also covered; the row buffers need not be distinct mathematically. -/
theorem swap_steps (parameter : Turing.Tape (Symbol Scalar)) (coefficient : Scalar)
    (parameterHead : parameter.head = some (some coefficient))
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (source target : Fin rows)
    (left right : Bool → List (Symbol Scalar)) :
    Steps (machine false (swapTable (Scalar := Scalar))) (2 * columns + 3)
      (0, pairFrame parameter matrix source target left right)
      (2, pairFrame parameter (MatrixOperations.swapRows matrix source target) source target left right) := by
  have trace := TableTraversal.steps false (swapTable (Scalar := Scalar)) parameter coefficient parameterHead
    (List.ofFn (fun column : Fin columns => fun name : Bool => matrix (if name then target else source) column))
    left right
  convert trace using 1
  · simp
  · simp [pairFrame, word, List.map_ofFn, Function.comp_def]
  · congr 2
    funext name
    cases name with
    | inl name => rfl
    | inr name =>
      cases name <;> simp [pairFrame, frame, word, List.map_ofFn, Function.comp_def, swapTable, MatrixOperations.swapRows]

end Polytime2.FieldRow
