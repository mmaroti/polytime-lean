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

import Polytime2.Matrices.IntegerHermiteRow
import Polytime2.TM0.Computation

/-! # Realized Hermite column and row traversals

A rectangular matrix with a middle source row exercises the source skip,
negative-target Bézout change, and subsequent divisible cancellation. The
entire returned matrix and basis agree with an independently computed example.
The transposed example checks the dual row traversal and right-basis orientation.
-/

namespace Polytime2.Examples.IntegerHermiteColumn

open Polytime2.Computation Polytime2.IntegerMatrix

variable {Parameter : Type} [Fintype Parameter]

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteColumn rows columns width).TM0Realizable :=
  (integerHermiteColumn_realizable rows columns width).tm0

private def sample (rows columns : ℕ) : Matrix (Fin rows) (Fin columns) ℤ :=
  fun row column => if row.val = 1 then (if column.val = 0 then 6 else 1)
    else if row.val = 0 then (if column.val = 0 then -17 else 4)
    else (if column.val = 0 then 18 else 2)

private def expectedMatrix (rows columns : ℕ) : Matrix (Fin rows) (Fin columns) ℤ :=
  fun row column => if column.val = 0 then (if row.val = 1 then 1 else 0)
    else if row.val = 0 then 41 else if row.val = 1 then 7 else -124

private def expectedBasis (rows : ℕ) : Matrix (Fin rows) (Fin rows) ℤ :=
  fun row column => if row.val = 0 then (if column.val = 0 then 6 else if column.val = 1 then 17 else 0)
    else if row.val = 1 then (if column.val = 0 then 1 else if column.val = 1 then 3 else 0)
    else (if column.val = 0 then -18 else if column.val = 1 then -54 else 1)

private theorem sampleOracle (rows columns : ℕ) (rowCount : rows = 3) (columnCount : columns = 2)
    (source : Fin rows) (column : Fin columns) (sourceValue : source.val = 1) (columnValue : column.val = 0) :
    hermiteColumnPrefix source column rows (sample rows columns) 1 = (expectedMatrix rows columns, expectedBasis rows) := by
  subst rows
  subst columns
  have sourceEq : source = (1 : Fin 3) := Fin.ext sourceValue
  have columnEq : column = (0 : Fin 2) := Fin.ext columnValue
  subst source
  subst column
  apply Prod.ext <;> ext row position <;> fin_cases row <;> fin_cases position <;> decide +kernel

private noncomputable def arguments : (integerHermiteColumn (Parameter := Empty) 3 2 5).Arguments Empty.elim
  | 0 => ⟨1, by norm_num⟩
  | 1 => ⟨0, by norm_num⟩
  | 2 => ⟨sample _ _, by
      intro row column
      dsimp only [sample]
      split_ifs <;> norm_num⟩
  | 3 => ⟨1, by
      intro row column
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num⟩

private theorem arguments_valid :
    (integerHermiteColumn (Parameter := Empty) 3 2 5).precondition Empty.elim arguments := by
  change 0 < (arguments 2).val (arguments 0) (arguments 1)
  norm_num [arguments, sample]

/-- Both actual output matrices agree with the mathematical golden result. -/
example :
    let result := (integerHermiteColumn (Parameter := Empty) 3 2 5).compute Empty.elim ⟨arguments, arguments_valid⟩
    (result.1.val, result.2.val) =
      (expectedMatrix (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))
        (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)),
       expectedBasis (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))) := by
  have computed := integerHermiteColumn_correct (Parameter := Empty) 3 2 5 Empty.elim ⟨arguments, arguments_valid⟩
  exact computed.trans (sampleOracle _ _ (by norm_num) (by norm_num) (arguments 0) (arguments 1) rfl rfl)

/-- A positive one-row input performs no row updates, regardless of column count. -/
private theorem oneRowOracle (rows : ℕ) (rowCount : rows = 1) {Column : Type} [DecidableEq Column]
    (source : Fin rows) (column : Column) (matrix : Matrix (Fin rows) Column ℤ) (basis : Matrix (Fin rows) (Fin rows) ℤ) :
    hermiteColumnPrefix source column rows matrix basis = (matrix, basis) := by
  subst rows
  have sourceEq : source = 0 := Subsingleton.elim _ _
  subst source
  rfl

example (columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : {values : (integerHermiteColumn 1 columns width).Arguments sizes //
      (integerHermiteColumn 1 columns width).precondition sizes values}) :
    let result := (integerHermiteColumn 1 columns width).compute sizes values
    (result.1.val, result.2.val) = ((values.val 2).val, (values.val 3).val) := by
  exact (integerHermiteColumn_correct 1 columns width sizes values).trans
    (oneRowOracle (Column := Fin (MvPolynomial.eval sizes columns)) _ (by norm_num) (values.val 0) (values.val 1) (values.val 2).val (values.val 3).val)

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRow rows columns width).TM0Realizable :=
  (integerHermiteRow_realizable rows columns width).tm0

private noncomputable def rowArguments : (integerHermiteRow (Parameter := Empty) 2 3 5).Arguments Empty.elim
  | 0 => arguments 0
  | 1 => arguments 1
  | 2 => ⟨(arguments 2).val.transpose, fun row column => (arguments 2).property column row⟩
  | 3 => arguments 3

private theorem rowArguments_valid :
    (integerHermiteRow (Parameter := Empty) 2 3 5).precondition Empty.elim rowArguments := by
  exact arguments_valid

/-- The dual traversal transposes the actual basis, retaining right-multiplication orientation. -/
example :
    let result := (integerHermiteRow (Parameter := Empty) 2 3 5).compute Empty.elim ⟨rowArguments, rowArguments_valid⟩
    (result.1.val, result.2.val) =
      ((expectedMatrix (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))
        (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ))).transpose,
       (expectedBasis (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))).transpose) := by
  have computed := integerHermiteRow_correct (Parameter := Empty) 2 3 5 Empty.elim ⟨rowArguments, rowArguments_valid⟩
  have golden := congrArg (fun matrices => (matrices.1.transpose, matrices.2.transpose))
    (sampleOracle _ _ (by norm_num) (by norm_num) (arguments 0) (arguments 1) rfl rfl)
  apply computed.trans
  simpa only [hermiteRowPrefix, rowArguments, arguments, Matrix.transpose_transpose, Matrix.transpose_one] using golden

end Polytime2.Examples.IntegerHermiteColumn
