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

import Polytime2.ScalarAccess
import Polytime2.Matrix
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Row-major matrix access

Independent row and column dimensions determine a dense scalar array. The
access contract assumes a prepared unary address; computing that address is
a separate runtime operation. No runtime dimension enters the controller.
-/

namespace Polytime2.MatrixAccess

open MultiTape TableTraversal

variable {Scalar : Type} {rows columns : ℕ}

def entries (matrix : Matrix (Fin rows) (Fin columns) Scalar) : List Scalar :=
  List.ofFn (fun index : Fin (rows * columns) =>
    matrix (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)

@[simp] theorem entries_length (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    (entries matrix).length = rows * columns := by simp [entries]

def address (row : Fin rows) (column : Fin columns) : Fin (rows * columns) :=
  finProdFinEquiv (row, column)

theorem address_value (row : Fin rows) (column : Fin columns) :
    (address row column).val = row.val * columns + column.val := by
  simp [address, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] theorem entries_address (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) :
    (entries matrix)[(address row column).val]'(by simp) = matrix row column := by
  simp only [entries, List.getElem_ofFn]
  change matrix (finProdFinEquiv.symm (finProdFinEquiv (row, column))).1
    (finProdFinEquiv.symm (finProdFinEquiv (row, column))).2 = matrix row column
  rw [Equiv.symm_apply_apply]

def update (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (value : Scalar) :
    Matrix (Fin rows) (Fin columns) Scalar :=
  Function.update matrix row (Function.update (matrix row) column value)

theorem entries_update (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (value : Scalar) :
    entries (update matrix row column value) = (entries matrix).set (address row column).val value := by
  apply List.ext_getElem
  · simp
  · intro index firstBound secondBound
    have indexBound : index < rows * columns := by simpa using firstBound
    let position : Fin (rows * columns) := ⟨index, indexBound⟩
    let pair := finProdFinEquiv.symm position
    by_cases same : index = (address row column).val
    · subst index
      rw [entries_address]
      simp [update, Function.update]
    · have different : pair.1 ≠ row ∨ pair.2 ≠ column := by
        by_contra equality
        push Not at equality
        have pairEquality : pair = (row, column) := Prod.ext equality.1 equality.2
        have indexEquality := congrArg finProdFinEquiv pairEquality
        have contradiction : index = (address row column).val := by
          change finProdFinEquiv (finProdFinEquiv.symm position) = address row column at indexEquality
          rw [Equiv.apply_symm_apply] at indexEquality
          exact congrArg Fin.val indexEquality
        exact same contradiction
      simp only [entries, List.getElem_ofFn, List.getElem_set]
      change update matrix row column value pair.1 pair.2 =
        if (address row column).val = index then value else matrix pair.1 pair.2
      rw [ite_eq_right (Ne.symm same)]
      rcases different with differentRow | differentColumn
      · simp [update, Function.update, differentRow]
      · by_cases sameRow : pair.1 = row
        · simp [update, Function.update, sameRow, differentColumn]
        · simp [update, Function.update, sameRow]

def frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) : Tapes (ScalarAccess.Alphabet Scalar) :=
  ScalarAccess.frame [3] (List.replicate (address row column).val 2 ++ [0])
    [some none] (word (entries matrix) ++ [none])
    (Turing.Tape.mk' (Turing.ListBlank.mk [some none]) (Turing.ListBlank.mk [some (some element)]))

theorem lookup_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    Steps (ScalarAccess.machine false) (2 * (row.val * columns + column.val) + 3)
      (0, frame matrix row column element)
      (2, frame matrix row column (matrix row column)) := by
  have trace := ScalarAccess.lookup_steps (entries matrix)
    ⟨(address row column).val, by simp⟩ element [] [] [some none] [none] [some none] []
  simp only [entries_address] at trace
  simpa [frame, address_value] using trace

theorem update_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    Steps (ScalarAccess.machine true) (2 * (row.val * columns + column.val) + 3)
      (0, frame matrix row column element)
      (2, frame (update matrix row column element) row column element) := by
  have trace := ScalarAccess.update_steps (entries matrix)
    ⟨(address row column).val, by simp⟩ element [] [] [some none] [none] [some none] []
  simpa [frame, address_value, entries_update] using trace

/-- Rows and columns are independent runtime size parameters. The address must
already be prepared; this certificate includes the access and head restoration. -/
theorem realizes [Fintype Scalar] (write : Bool) :
    Realizes (ScalarAccess.machine (Scalar := Scalar) write) 0 2
      (fun assignment initial =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
          initial = frame matrix row column element)
      (fun assignment initial final =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
          initial = frame matrix row column element ∧
          final = frame (if write then update matrix row column element else matrix)
            row column (if write then element else matrix row column)) := by
  refine ⟨by intro symbols; rfl, 2 * MvPolynomial.X false * MvPolynomial.X true + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, row, column, element, rfl⟩ := valid
  have addressBound : row.val * assignment true + column.val ≤ assignment false * assignment true := by
    have bound := (address row column).isLt
    rw [address_value] at bound
    omega
  have trace : Steps (ScalarAccess.machine write) (2 * (row.val * assignment true + column.val) + 3)
      (0, frame matrix row column element)
      (2, frame (if write then update matrix row column element else matrix)
        row column (if write then element else matrix row column)) := by
    cases write with
    | false => exact lookup_steps matrix row column element
    | true => exact update_steps matrix row column element
  refine ⟨2 * (row.val * assignment true + column.val) + 3, _, ?_, trace,
    matrix, row, column, element, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
  nlinarith

end Polytime2.MatrixAccess
