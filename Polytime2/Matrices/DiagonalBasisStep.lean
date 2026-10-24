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

import Polytime2.Matrices.IntegerDiagonalPair
import Polytime2.Matrices.IntegerRowPair

/-! # Certified coupled diagonal cleanup and basis updates

Inputs are two distinct active coordinates, their diagonal entries, and the
current left and right square basis matrices. Compute one pair-cleanup result,
retain it, and apply its left transformation to the left basis and its right
transformation to the right basis. All result widths are derived from the two
mathematical input widths. No unimodularity premise is needed to execute a step.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def basisStepInputs (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Fin 6 → EncodedDomain Parameter := fun name => match name with
  | 0 | 1 => boundedIndex length
  | 2 | 3 => binaryIntegers diagonalWidth
  | 4 | 5 => integerMatrices length length basisWidth

private noncomputable def basisStepHost (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :=
  Sum.elim (basisStepInputs length diagonalWidth basisWidth)
    (fun _ : Unit => (integerDiagonalPair diagonalWidth).outputDomain)

private def basisStepAllowed (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (basisStepHost length diagonalWidth basisWidth name).Carrier sizes) :=
  arguments (.inl 0) ≠ arguments (.inl 1)

private noncomputable def squarePairAction (length coefficientWidth basisWidth : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) : Computation Parameter (Fin 7) where
  inputDomains := (integerRowPairAtWidths length length coefficientWidth basisWidth).inputDomains
  outputDomain := (integerRowPairAtWidths length length coefficientWidth basisWidth).outputDomain
  precondition := (integerRowPairAtWidths length length coefficientWidth basisWidth).precondition
  compute sizes arguments := if chooseRight then
    (integerColumnPairAtWidths length length coefficientWidth basisWidth).compute sizes arguments
    else (integerRowPairAtWidths length length coefficientWidth basisWidth).compute sizes arguments

private theorem squarePairAction_realizable (length coefficientWidth basisWidth : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) : (squarePairAction length coefficientWidth basisWidth chooseRight).Realizable := by
  cases chooseRight
  · exact integerRowPairAtWidths_realizable length length coefficientWidth basisWidth
  · exact integerColumnPairAtWidths_realizable length length coefficientWidth basisWidth

private noncomputable def basisCoefficientWidth (width : MvPolynomial Parameter ℕ) (chooseRight : Bool) :=
  if chooseRight then 2 * (2 * width + 1) else 2 * width + 1

private noncomputable def basisApplicationArguments (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) (name : Fin 7) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (basisStepHost length diagonalWidth basisWidth name).Carrier sizes //
      basisStepAllowed length diagonalWidth basisWidth sizes arguments}) :
    ((squarePairAction length (basisCoefficientWidth diagonalWidth chooseRight) basisWidth chooseRight).inputDomains name).Carrier sizes :=
  let entry row column := (Realizable.Internal.diagonalCoefficientEntry diagonalWidth chooseRight row column).compute sizes
    ⟨(fun _ => (arguments.val (.inr ())).2), trivial⟩
  match name with
  | 0 => arguments.val (.inl 0)
  | 1 => arguments.val (.inl 1)
  | 2 => entry 0 0
  | 3 => entry 0 1
  | 4 => entry 1 0
  | 5 => entry 1 1
  | 6 => if chooseRight then arguments.val (.inl 5) else arguments.val (.inl 4)

private noncomputable def basisApplication (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) :=
  (squarePairAction length (basisCoefficientWidth diagonalWidth chooseRight) basisWidth chooseRight).onResults
    (basisStepHost length diagonalWidth basisWidth) (basisStepAllowed length diagonalWidth basisWidth)
    (basisApplicationArguments length diagonalWidth basisWidth chooseRight) (fun _ arguments => arguments.property)

private theorem basisApplication_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (chooseRight : Bool) : (basisApplication length diagonalWidth basisWidth chooseRight).Realizable := by
  let domains := basisStepHost length diagonalWidth basisWidth
  let allowed := basisStepAllowed length diagonalWidth basisWidth
  have entry (row column : Fin 2) := (((pairProjection_realizable (integerGcdLcm diagonalWidth).outputDomain
    (integerDiagonalPairCoefficients diagonalWidth).outputDomain true).followedBy
      (Realizable.Internal.diagonalCoefficientEntry_realizable diagonalWidth chooseRight row column) rfl
        (by intros; trivial)).withArguments domains (MultiTape.oneTape (.inr ())) (fun _ => rfl)).withPrecondition allowed
          (by intros; trivial)
  apply (squarePairAction_realizable length (basisCoefficientWidth diagonalWidth chooseRight) basisWidth chooseRight).onResults
    domains allowed (basisApplicationArguments length diagonalWidth basisWidth chooseRight)
    (fun _ arguments => arguments.property)
  intro name
  fin_cases name
  · exact Realizable.argument domains (.inl 0) allowed
  · exact Realizable.argument domains (.inl 1) allowed
  · exact entry 0 0
  · exact entry 0 1
  · exact entry 1 0
  · exact entry 1 1
  · cases chooseRight
    · exact Realizable.argument domains (.inl 4) allowed
    · exact Realizable.argument domains (.inl 5) allowed

private noncomputable def basisStage (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6 ⊕ Unit) where
  inputDomains := basisStepHost length diagonalWidth basisWidth
  outputDomain := (integerGcdLcm diagonalWidth).outputDomain.prod
    ((basisApplication length diagonalWidth basisWidth false).outputDomain.prod
      (basisApplication length diagonalWidth basisWidth true).outputDomain)
  precondition := basisStepAllowed length diagonalWidth basisWidth
  compute sizes arguments := ((arguments.val (.inr ())).1,
    ((basisApplication length diagonalWidth basisWidth false).compute sizes arguments,
      (basisApplication length diagonalWidth basisWidth true).compute sizes arguments))

private theorem basisStage_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (basisStage length diagonalWidth basisWidth).Realizable := by
  let domains := basisStepHost length diagonalWidth basisWidth
  let allowed := basisStepAllowed length diagonalWidth basisWidth
  have bases := (basisApplication_realizable length diagonalWidth basisWidth false).prodMk (basisApplication_realizable length diagonalWidth basisWidth true)
  exact ((Realizable.argument domains (.inr ()) allowed).fst).prodMk bases

/-- Normalize two diagonal entries and update both accumulated square basis matrices. -/
noncomputable def integerDiagonalBasisStep (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) where
  inputDomains := basisStepInputs length diagonalWidth basisWidth
  outputDomain := (basisStage length diagonalWidth basisWidth).outputDomain
  precondition _ arguments := arguments 0 ≠ arguments 1
  compute sizes arguments :=
    let prepared := (integerDiagonalPair diagonalWidth).compute sizes
      ⟨(fun choice => if choice then arguments.val 3 else arguments.val 2), trivial⟩
    (basisStage length diagonalWidth basisWidth).compute sizes
      ⟨(fun name => match name with | .inl original => arguments.val original | .inr _ => prepared), arguments.property⟩

theorem integerDiagonalBasisStep_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (integerDiagonalBasisStep length diagonalWidth basisWidth).Realizable := by
  let computation := integerDiagonalBasisStep length diagonalWidth basisWidth
  have prepared := (integerDiagonalPair_realizable diagonalWidth).onArguments computation.inputDomains computation.precondition
    (fun choice => if choice then 3 else 2) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have complete := prepared.letThen (basisStage_realizable length diagonalWidth basisWidth)
    (fun _ => rfl) rfl (by intros; assumption)
  exact complete.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- Both returned bases use the same pair of transformations prepared from the supplied diagonal entries. -/
theorem integerDiagonalBasisStep_correct (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerDiagonalBasisStep length diagonalWidth basisWidth).Arguments sizes //
      (integerDiagonalBasisStep length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments
    (result.2.1.val, result.2.2.val) =
      (IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes length)) (arguments.val 0) (arguments.val 1)
        (IntegerMatrix.bezoutMatrix (arguments.val 2).val (arguments.val 3).val) (arguments.val 4).val,
      IntegerMatrix.columnPair (Column := Fin (MvPolynomial.eval sizes length)) (arguments.val 0) (arguments.val 1)
        (IntegerMatrix.diagonalPairRight (arguments.val 2).val (arguments.val 3).val) (arguments.val 5).val) := by
  rfl

/-- The returned diagonal entries are the gcd and signed lcm of the supplied entries. -/
theorem integerDiagonalBasisStep_values (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerDiagonalBasisStep length diagonalWidth basisWidth).Arguments sizes //
      (integerDiagonalBasisStep length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments
    result.1.1.val = (Int.gcd (arguments.val 2).val (arguments.val 3).val : ℤ) ∧
      result.1.2.val = (arguments.val 2).val / (Int.gcd (arguments.val 2).val (arguments.val 3).val : ℤ) *
        (arguments.val 3).val := ⟨rfl, rfl⟩

/-- On natural diagonal entries, both returned scalar values match the mathematical pair update. -/
theorem integerDiagonalBasisStep_natural_values (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerDiagonalBasisStep length diagonalWidth basisWidth).Arguments sizes //
      (integerDiagonalBasisStep length diagonalWidth basisWidth).precondition sizes arguments})
    (diagonal : Fin (MvPolynomial.eval sizes length) → ℕ)
    (firstEntry : (arguments.val 2).val = (diagonal (arguments.val 0) : ℤ))
    (secondEntry : (arguments.val 3).val = (diagonal (arguments.val 1) : ℤ)) :
    let result := (integerDiagonalBasisStep length diagonalWidth basisWidth).compute sizes arguments
    result.1.1.val = (Nat.gcd (diagonal (arguments.val 0)) (diagonal (arguments.val 1)) : ℤ) ∧
      result.1.2.val = (Nat.lcm (diagonal (arguments.val 0)) (diagonal (arguments.val 1)) : ℤ) := by
  have values := integerDiagonalBasisStep_values length diagonalWidth basisWidth sizes arguments
  rw [firstEntry, secondEntry, Int.gcd_natCast_natCast] at values
  refine ⟨values.1, values.2.trans ?_⟩
  simpa only [Nat.cast_mul, Int.natCast_ediv] using congrArg (fun value : ℕ => (value : ℤ))
    (IntegerMatrix.diagonalPair_lcm (diagonal (arguments.val 0)) (diagonal (arguments.val 1)))

end Polytime2.Computation
