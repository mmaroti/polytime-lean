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

import Polytime2.Matrices.BezoutCoefficients
import Polytime2.Matrices.DiagonalPairMath
import Polytime2.Arithmetic.SignedMultiplication

/-! # Certified coefficients for diagonal pair cleanup

One normalized Bézout coefficient record is retained. Two existing integer
multiplications produce the right transformation, with sufficient coefficient
width derived internally. The output is an internal pair of coefficient records;
public matrix operations use their ordinary mathematical transformation meaning.
-/

namespace Polytime2.Computation.Realizable.Internal.DiagonalCoefficients

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def rightWidth (width : MvPolynomial Parameter ℕ) := 2 * (2 * width + 1)
noncomputable def rightDomain (width : MvPolynomial Parameter ℕ) := record 4 (fun _ => binaryIntegers (rightWidth width))

noncomputable def rightFromLeft (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := BezoutCoefficients.domain width
  outputDomain := rightDomain width
  precondition _ _ := True
  compute sizes arguments index := match index with
    | 0 => ⟨1, by simp [rightWidth, map_mul, map_add]⟩
    | 1 => (integerMultiply (2 * width + 1)).compute sizes
        ⟨(fun choice => if choice then arguments.val () 2 else arguments.val () 1), trivial⟩
    | 2 => ⟨1, by simp [rightWidth, map_mul, map_add]⟩
    | 3 => (integerMultiply (2 * width + 1)).compute sizes
        ⟨(fun choice => if choice then arguments.val () 3 else arguments.val () 0), trivial⟩

theorem rightFromLeft_realizable (width : MvPolynomial Parameter ℕ) : (rightFromLeft width).Realizable := by
  let inputs := (rightFromLeft width).inputDomains
  let allowed := (rightFromLeft width).precondition
  let coefficientWidth := 2 * width + 1
  have projection (index : Fin 4) := (recordProjection_realizable 4 (fun _ => binaryIntegers coefficientWidth) index)
  have multiply (first second : Fin 4) := (integerMultiply_realizable coefficientWidth).onResults inputs allowed
    (fun choice _ arguments => if choice then arguments.val () second else arguments.val () first)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact projection first
      · exact projection second)
  let one (_ : Empty → Bool) : {value : ℤ // value.natAbs < 2} := ⟨1, by decide⟩
  have constant := (((integerBooleanOperation_realizable (Parameter := Parameter) one).followedBy
    (integerWidenTo_realizable 1 (4 * width + 1) (rightWidth width) (by dsimp [rightWidth]; ring)) rfl
      (by intros; trivial)).withArguments inputs ⟨Empty.elim, by intro name; exact name.elim⟩
        (by intro name; exact name.elim))
  apply Realizable.recordOutputs inputs 4 (fun _ => binaryIntegers (rightWidth width)) allowed
    (fun index sizes arguments => (rightFromLeft width).compute sizes arguments index)
  intro index
  fin_cases index
  · exact constant
  · exact multiply 1 2
  · exact constant
  · exact multiply 0 3

noncomputable def stage (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := BezoutCoefficients.domain width
  outputDomain := (BezoutCoefficients.domain width).prod (rightDomain width)
  precondition _ _ := True
  compute sizes arguments := (arguments.val (), (rightFromLeft width).compute sizes arguments)

theorem stage_realizable (width : MvPolynomial Parameter ℕ) : (stage width).Realizable := by
  exact (Realizable.argument (stage width).inputDomains () (fun _ _ => True)).prodMk (rightFromLeft_realizable width)

noncomputable def computation (width : MvPolynomial Parameter ℕ) :=
  (BezoutCoefficients.computation width).followedBy (stage width) rfl (by intros; trivial)

theorem realizable (width : MvPolynomial Parameter ℕ) : (computation width).Realizable :=
  (BezoutCoefficients.realizable width).followedBy (stage_realizable width) rfl (by intros; trivial)

/-- Both records encode exactly the actual left and right diagonal-pair transformations. -/
theorem compute_matrices (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (computation width).Arguments sizes // True}) :
    let result := (computation width).compute sizes arguments
    !![(result.1 0).val, (result.1 1).val; (result.1 2).val, (result.1 3).val] =
        IntegerMatrix.bezoutMatrix (arguments.val false).val (arguments.val true).val ∧
      !![(result.2 0).val, (result.2 1).val; (result.2 2).val, (result.2 3).val] =
        IntegerMatrix.diagonalPairRight (arguments.val false).val (arguments.val true).val := by
  constructor
  · exact BezoutCoefficients.compute_matrix width sizes arguments
  · unfold IntegerMatrix.diagonalPairRight
    rw [← BezoutCoefficients.compute_matrix width sizes arguments]
    rfl

end Polytime2.Computation.Realizable.Internal.DiagonalCoefficients
