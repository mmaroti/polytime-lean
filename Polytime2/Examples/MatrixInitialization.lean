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

import Polytime2.Matrices.IntegerBezoutTracking
import Polytime2.Matrices.Identity
import Polytime2.Matrices.IntegerNegate
import Polytime2.TM0.Computation

/-! # Integer basis initialization and single-row sign changes

Identity construction and sign changes have standalone certificates for all
runtime dimensions. The boundary examples check empty identity storage,
zero-width equality, sign-sensitive equality, and a negative one-by-one matrix.
-/

namespace Polytime2.Examples.MatrixInitialization

open Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

example (rows : MvPolynomial Parameter ℕ) : (integerIdentity rows).TM0Realizable :=
  (integerIdentity_realizable rows).tm0

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowNegate rows columns width).TM0Realizable :=
  (integerRowNegate_realizable rows columns width).tm0

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnNegate rows columns width).TM0Realizable :=
  (integerColumnNegate_realizable rows columns width).tm0

example (sizes : Parameter → ℕ) :
    (integerIdentity (0 : MvPolynomial Parameter ℕ)).outputDomain.width sizes = 0 := by
  change MvPolynomial.eval sizes ((0 * 0) * (EncodedDomain.binaryIntegers (1 : MvPolynomial Parameter ℕ)).widthPolynomial) = 0
  simp

example : (elementsEqual (EncodedDomain.bitVectors (0 : MvPolynomial Unit ℕ))).compute (fun _ => 0)
    ⟨(fun _ => (0 : BitVec (MvPolynomial.eval (fun _ : Unit => 0) (0 : MvPolynomial Unit ℕ)))), trivial⟩ = true := by
  simp [elementsEqual]
  rfl

example : (elementsEqual (EncodedDomain.binaryIntegers (1 : MvPolynomial Unit ℕ))).compute (fun _ => 0)
    ⟨(fun choice => if choice then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩), trivial⟩ = false := by
  classical
  dsimp [elementsEqual]
  apply decide_eq_false_iff_not.mpr
  intro equal
  have values := congrArg Subtype.val equal
  norm_num at values

private noncomputable def negativeArguments :
    (integerRowNegate (Parameter := Empty) 1 1 2).Arguments Empty.elim
  | false => ⟨0, by norm_num⟩
  | true => ⟨fun _ _ => -3, by intro row column; norm_num⟩

example : ((integerRowNegate (Parameter := Empty) 1 1 2).compute Empty.elim
    ⟨negativeArguments, trivial⟩).val = fun _ _ => 3 := by
  ext row column
  change IntegerMatrix.rowNegate (Row := Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)))
    ⟨0, by norm_num⟩ (fun _ _ => -3) row column = 3
  have same : row = ⟨0, by norm_num⟩ := by
    apply Fin.ext
    have bounded := row.isLt
    norm_num at bounded
    omega
  erw [IntegerMatrix.rowNegate_apply, ite_eq_left same]
  norm_num

example : (Matrix.rowScale (0 : Fin 1) (-1 : ℤ)).det = -1 :=
  IntegerMatrix.rowNegate_unimodular 0

/-- A first elimination retains an actual unimodular left transformation. -/
example (matrix : Matrix (Fin 2) (Fin 3) ℤ) :
    let updated := IntegerMatrix.bezoutRowsWithLeft 0 1 0 matrix 1
    updated.2 * matrix = updated.1 ∧ IsUnit updated.2.det := by
  constructor
  · simpa using IntegerMatrix.bezoutRowsWithLeft_equation 0 1 0 matrix matrix 1 1 (by simp)
  · exact IntegerMatrix.bezoutRowsWithLeft_unimodular 0 1 (by decide) 0 matrix 1 (by simp)

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutRowsWithLeft rows columns width).TM0Realizable :=
  (integerBezoutRowsWithLeft_realizable rows columns width).tm0

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerBezoutColumnsWithRight rows columns width).TM0Realizable :=
  (integerBezoutColumnsWithRight_realizable rows columns width).tm0

/-- Coefficients come from the current matrix, even for a nonidentity left basis. -/
example : (IntegerMatrix.bezoutRowsWithLeft (0 : Fin 2) 1 0
    (!![30, 7, 0; 18, -2, 0] : Matrix (Fin 2) (Fin 3) ℤ) !![1, 2; 0, 1]).2 =
      !![2, 1; -3, -1] := by
  have coefficients : IntegerMatrix.bezoutMatrix 30 18 = !![2, -3; -3, 5] := by
    ext row column
    fin_cases row <;> fin_cases column <;> decide +kernel
  change IntegerMatrix.rowPair (0 : Fin 2) 1 (IntegerMatrix.bezoutMatrix 30 18) !![1, 2; 0, 1] = _
  rw [coefficients]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [IntegerMatrix.rowPair]

end Polytime2.Examples.MatrixInitialization
