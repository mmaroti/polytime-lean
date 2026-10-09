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

import Polytime.Examples.Matrices
import Polytime.SizeEvaluation
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Runtime row-major matrix addresses

The row index, column index, and column count are unary runtime fields. A fixed
finite controller computes the scalar-bit address, retaining the fields and
arbitrary trailing input. Its time bound depends only on matrix dimensions.
-/

namespace Polytime.Examples.MatrixAddress

open UnaryMachine (Symbol units fields)

inductive Parameter | rowIndex | columnIndex | columnCount
  deriving DecidableEq

instance : Fintype Parameter :=
  ⟨{.rowIndex, .columnIndex, .columnCount}, by intro name; cases name <;> simp⟩

abbrev context : SizeContext := ⟨Parameter, inferInstance⟩

def assignment (row column columns : ℕ) : SizeAssignment context
  | .rowIndex => row
  | .columnIndex => column
  | .columnCount => columns

def expression (scalarWidth : ℕ) : SizeExpression context :=
  (.parameter .rowIndex * .parameter .columnCount + .parameter .columnIndex) * .constant scalarWidth

/-- A single controller computes every valid matrix-entry address. Its polynomial
witness involves only the dimensions, not independently varying runtime indices.
The returned scratch fields are fixed by the expression and retain the input fields. -/
theorem realizes (scalarWidth : ℕ) :
    ∃ (scratch : List (SizeExpression context)) (Controller : Type) (_finite : Fintype Controller)
      (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (row : Fin rows) (column : Fin columns) (tail : List Symbol),
          ∃ ticks, ticks ≤ bound.eval (Matrices.assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry [] (fields [row.val, column.val, columns] ++ tail))
              (Tape.configuration exit [] (units ((row.val * columns + column.val) * scalarWidth) ++ 1 ::
                (fields (scratch.map (·.eval (assignment row.val column.val columns))) ++
                  fields [row.val, column.val, columns] ++ tail))) := by
  obtain ⟨scratch, Controller, finite, inhabited, entry, exit, machine, cost, halt, runs⟩ :=
    Polytime.SizeEvaluation.realizes_header (expression scalarWidth)
      [.rowIndex, .columnIndex, .columnCount]
      (by intro name; cases name <;> simp)
  let dimensions : context.Parameter → Matrices.context.Parameter
    | .rowIndex => .K
    | .columnIndex => .L
    | .columnCount => .L
  refine ⟨scratch, Controller, finite, inhabited, entry, exit, machine,
    MvPolynomial.rename dimensions cost, halt, ?_⟩
  intro rows columns row column tail
  obtain ⟨ticks, bound, trace⟩ := runs (assignment row.val column.val columns) tail
  refine ⟨ticks, ?_, ?_⟩
  · calc
      ticks ≤ cost.eval (assignment row.val column.val columns) := bound
      _ ≤ cost.eval (fun name => Matrices.assignment rows columns (dimensions name)) :=
        SizePolynomial.eval_mono cost _ _ (by
          intro name; cases name <;> simp only [assignment, dimensions, Matrices.assignment]
          · exact Nat.le_of_lt row.isLt
          · exact Nat.le_of_lt column.isLt
          · exact le_rfl)
      _ = (MvPolynomial.rename dimensions cost).eval (Matrices.assignment rows columns) := by
        simp only [SizePolynomial.eval, MvPolynomial.eval_rename, Function.comp_def]
  · simpa only [List.map_cons, List.map_nil, List.map_append,
      SizeExpression.eval_parameter, expression, SizeExpression.eval_mul,
      SizeExpression.eval_add, SizeExpression.eval_constant, assignment,
      UnaryMachine.fields_cons, UnaryMachine.fields_append, List.append_assoc,
      List.cons_append] using trace

end Polytime.Examples.MatrixAddress
