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

import Polytime2.Matrices.IntegerRowPair
import Polytime2.TM0.Computation

/-! # Unequal-width integer row and column transformations

One-bit coefficients act on four-bit matrix entries. The nonsymmetric example
checks the right-multiplication convention for columns. Zero-width coefficients
are also admissible. Generic certificates include empty matrix dimensions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.IntegerRowPairWidths

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerTwoProductsAtWidths coefficientWidth matrixWidth).TM0Realizable :=
  (integerTwoProductsAtWidths_realizable coefficientWidth matrixWidth).tm0

example (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerRowPairAtWidths rows columns coefficientWidth matrixWidth).TM0Realizable :=
  (integerRowPairAtWidths_realizable rows columns coefficientWidth matrixWidth).tm0

example (rows columns coefficientWidth matrixWidth : MvPolynomial Parameter ℕ) :
    (integerColumnPairAtWidths rows columns coefficientWidth matrixWidth).TM0Realizable :=
  (integerColumnPairAtWidths_realizable rows columns coefficientWidth matrixWidth).tm0

private def matrixValue (row column : ℕ) : ℤ :=
  if row = 0 then (if column = 0 then 12 else if column = 1 then -8 else 3)
  else if column = 0 then 5 else if column = 1 then 7 else -1

private noncomputable def rowArguments :
    (integerRowPairAtWidths (Parameter := Empty) 2 3 1 4).Arguments Empty.elim
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨1, by norm_num⟩
  | 2 | 3 | 5 => ⟨1, by norm_num⟩
  | 4 => ⟨0, by norm_num⟩
  | 6 => ⟨fun row column => matrixValue row.val column.val, by
      intro row column
      dsimp only [matrixValue]
      split_ifs <;> norm_num⟩

private theorem rowArguments_valid :
    (integerRowPairAtWidths (Parameter := Empty) 2 3 1 4).precondition Empty.elim rowArguments := by
  intro equal
  have values := congrArg Fin.val equal
  norm_num [rowArguments, integerRowPairAtWidths] at values

example : ((integerRowPairAtWidths (Parameter := Empty) 2 3 1 4).compute Empty.elim
    ⟨rowArguments, rowArguments_valid⟩).val = (fun row column =>
      if row.val = 0 then (if column.val = 0 then 17 else if column.val = 1 then -1 else 2)
      else if column.val = 0 then 5 else if column.val = 1 then 7 else -1) := by
  ext row column
  change IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ !![1, 1; 0, 1]
    (fun row column => matrixValue row.val column.val) row column = _
  have bounded := row.isLt
  norm_num at bounded
  have rows : row.val = 0 ∨ row.val = 1 := by omega
  rcases rows with rowValue | rowValue
  all_goals by_cases columnZero : column.val = 0 <;> by_cases columnOne : column.val = 1
  all_goals norm_num [IntegerMatrix.rowPair,
    Matrix.updateRow, Function.update, Fin.ext_iff, matrixValue, rowValue, columnZero, columnOne] at *

private noncomputable def columnArguments :
    (integerColumnPairAtWidths (Parameter := Empty) 2 3 1 4).Arguments Empty.elim
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨2, by norm_num⟩
  | 2 => rowArguments 2
  | 3 => rowArguments 3
  | 4 => rowArguments 4
  | 5 => rowArguments 5
  | 6 => rowArguments 6

private theorem columnArguments_valid :
    (integerColumnPairAtWidths (Parameter := Empty) 2 3 1 4).precondition Empty.elim columnArguments := by
  intro equal
  have values := congrArg Fin.val equal
  norm_num [columnArguments, integerColumnPairAtWidths] at values

example : ((integerColumnPairAtWidths (Parameter := Empty) 2 3 1 4).compute Empty.elim
    ⟨columnArguments, columnArguments_valid⟩).val = (fun row column =>
      if row.val = 0 then (if column.val = 0 then 12 else if column.val = 1 then -8 else 15)
      else if column.val = 0 then 5 else if column.val = 1 then 7 else 4) := by
  ext row column
  change IntegerMatrix.columnPair
    (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    (Column := Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))
    ⟨0, by norm_num⟩ ⟨2, by norm_num⟩ !![1, 1; 0, 1]
    (fun row column => matrixValue row.val column.val) row column = _
  have rowBound := row.isLt
  have columnBound := column.isLt
  norm_num at rowBound columnBound
  have rows : row.val = 0 ∨ row.val = 1 := by omega
  have columns : column.val = 0 ∨ column.val = 1 ∨ column.val = 2 := by omega
  rcases rows with rowValue | rowValue <;> rcases columns with columnValue | columnValue | columnValue
  all_goals norm_num [IntegerMatrix.columnPair,
    IntegerMatrix.rowPair, Matrix.updateRow, Function.update, Fin.ext_iff, matrixValue,
    rowValue, columnValue] at *

private noncomputable def zeroArguments :
    (integerRowPairAtWidths (Parameter := Empty) 2 3 0 4).Arguments Empty.elim
  | 0 => rowArguments 0
  | 1 => rowArguments 1
  | 2 | 3 | 4 | 5 => ⟨0, by norm_num⟩
  | 6 => rowArguments 6

private theorem zeroArguments_valid :
    (integerRowPairAtWidths (Parameter := Empty) 2 3 0 4).precondition Empty.elim zeroArguments := by
  intro equal
  have values := congrArg Fin.val equal
  norm_num [zeroArguments, rowArguments, integerRowPairAtWidths] at values

example : ((integerRowPairAtWidths (Parameter := Empty) 2 3 0 4).compute Empty.elim
    ⟨zeroArguments, zeroArguments_valid⟩).val = 0 := by
  ext row column
  change IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval Empty.elim (2 : MvPolynomial Empty ℕ)))
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ 0 (fun row column => matrixValue row.val column.val) row column = 0
  have bounded := row.isLt
  norm_num at bounded
  have rows : row.val = 0 ∨ row.val = 1 := by omega
  rcases rows with rowValue | rowValue
  all_goals simp [IntegerMatrix.rowPair, Matrix.updateRow, Function.update, Fin.ext_iff, rowValue]

end Polytime2.Examples.IntegerRowPairWidths
