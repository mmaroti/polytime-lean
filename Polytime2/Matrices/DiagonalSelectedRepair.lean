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

import Polytime2.Matrices.DiagonalBasisNarrow
import Polytime2.Matrices.DiagonalRepairCoordinates
import Polytime2.Arrays.Operations

/-! # Selecting and applying a fixed-workspace diagonal repair

The inputs are a natural diagonal and its accumulated left and right bases.
When adjacent divisibility fails and the logical prefix bound leaves sufficient
workspace, select the first failing pair, read its entries, and perform the
coupled repair. Return the actual coordinates, new diagonal entries, and both
updated bases. All runtime operations use existing mathematical compositions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def selectedInputs (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Fin 3 → EncodedDomain Parameter
  | 0 => (binaryNaturalsOfWidth diagonalWidth).arrayOfLength length
  | 1 | 2 => integerMatrices length length basisWidth

private def selectedAllowed (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (selectedInputs length diagonalWidth basisWidth name).Carrier sizes) :=
  ¬IntegerMatrix.diagonalDivisibilityChain (fun index => (arguments 0 index).val) ∧
    ∃ prefixWidth : ℕ,
      (∀ row column, ((arguments 1).val row column).natAbs < 2 ^ prefixWidth) ∧
      (∀ row column, ((arguments 2).val row column).natAbs < 2 ^ prefixWidth) ∧
      prefixWidth + (4 * MvPolynomial.eval sizes diagonalWidth + 3) ≤ MvPolynomial.eval sizes basisWidth

private noncomputable def selectedCoordinates (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :=
  ((diagonalRepairCoordinates length diagonalWidth).withArguments (selectedInputs length diagonalWidth basisWidth)
    (MultiTape.oneTape 0) (fun _ => rfl)).withPrecondition (selectedAllowed length diagonalWidth basisWidth)
      (fun _ _ valid => valid.1)

private noncomputable def selectedArguments (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (name : Fin 6) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (selectedInputs length diagonalWidth basisWidth name).Carrier sizes //
      selectedAllowed length diagonalWidth basisWidth sizes arguments}) :
    ((diagonalBasisStepWithin length diagonalWidth basisWidth).inputDomains name).Carrier sizes :=
  let pair := (selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments
  match name with
  | 0 => pair.1
  | 1 => pair.2
  | 2 => ⟨((arguments.val 0 pair.1).val : ℤ), by simpa using (arguments.val 0 pair.1).isLt⟩
  | 3 => ⟨((arguments.val 0 pair.2).val : ℤ), by simpa using (arguments.val 0 pair.2).isLt⟩
  | 4 => arguments.val 1
  | 5 => arguments.val 2

private theorem selectedArguments_valid (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (selectedInputs length diagonalWidth basisWidth name).Carrier sizes //
      selectedAllowed length diagonalWidth basisWidth sizes arguments}) :
    (diagonalBasisStepWithin length diagonalWidth basisWidth).precondition sizes
      (fun name => selectedArguments length diagonalWidth basisWidth name sizes arguments) := by
  have correct := diagonalRepairCoordinates_correct length diagonalWidth sizes
    ⟨(fun _ => arguments.val 0), arguments.property.1⟩
  refine ⟨?_, arguments.property.2⟩
  intro same
  have values := congrArg Fin.val same
  change ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).1.val =
    ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).2.val at values
  have adjacent : ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).2.val =
      ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).1.val + 1 := correct.1
  omega

/-- Select and perform one effective repair within a fixed basis workspace. -/
noncomputable def diagonalSelectedRepair (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) where
  inputDomains := selectedInputs length diagonalWidth basisWidth
  outputDomain := ((boundedIndex length).prod (boundedIndex length)).prod
    (diagonalBasisStepWithin length diagonalWidth basisWidth).outputDomain
  precondition := selectedAllowed length diagonalWidth basisWidth
  compute sizes arguments := ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments,
    (diagonalBasisStepWithin length diagonalWidth basisWidth).compute sizes
      ⟨(fun name => selectedArguments length diagonalWidth basisWidth name sizes arguments),
        selectedArguments_valid length diagonalWidth basisWidth sizes arguments⟩)

theorem diagonalSelectedRepair_realizable (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalSelectedRepair length diagonalWidth basisWidth).Realizable := by
  let computation := diagonalSelectedRepair length diagonalWidth basisWidth
  have coordinates : (selectedCoordinates length diagonalWidth basisWidth).Realizable :=
    ((diagonalRepairCoordinates_realizable length diagonalWidth).withArguments computation.inputDomains
      (MultiTape.oneTape 0) (fun _ => rfl)).withPrecondition computation.precondition (fun _ _ valid => valid.1)
  have coordinate (chooseSecond : Bool) :
      (Computation.mk computation.inputDomains (boundedIndex length) computation.precondition
        (fun sizes arguments => if chooseSecond then
          ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).2 else
          ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).1)).Realizable := by
    cases chooseSecond
    · exact coordinates.fst
    · exact coordinates.snd
  have entry (chooseSecond : Bool) :
      (Computation.mk computation.inputDomains (binaryIntegers diagonalWidth) computation.precondition
        (fun sizes arguments => ⟨((arguments.val 0
          (if chooseSecond then ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).2
           else ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).1)).val : ℤ),
          by simpa using (arguments.val 0 _).isLt⟩)).Realizable := by
    let results (choice : Bool) (sizes : Parameter → ℕ)
        (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
        ((arrayLookup (binaryNaturalsOfWidth diagonalWidth) length).inputDomains choice).Carrier sizes :=
      match choice with
      | false => if chooseSecond then ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).2
          else ((selectedCoordinates length diagonalWidth basisWidth).compute sizes arguments).1
      | true => arguments.val 0
    have read := (arrayLookup_realizable (binaryNaturalsOfWidth diagonalWidth) length).onResults
      computation.inputDomains computation.precondition results (by intros; trivial) (by
        intro choice
        cases choice
        · cases chooseSecond
          · exact coordinate false
          · exact coordinate true
        · exact Realizable.argument computation.inputDomains 0 computation.precondition)
    have converted := read.followedBy (integerOfMagnitude_realizable diagonalWidth) rfl (by intros; trivial)
    exact converted.withSpecification computation.precondition _ (by intros; assumption) (by intros; rfl)
  have repaired := (diagonalBasisStepWithin_realizable length diagonalWidth basisWidth).onResults
    computation.inputDomains computation.precondition (selectedArguments length diagonalWidth basisWidth)
    (selectedArguments_valid length diagonalWidth basisWidth) (by
      intro name
      fin_cases name
      · exact coordinate false
      · exact coordinate true
      · exact entry false
      · exact entry true
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact Realizable.argument computation.inputDomains 2 computation.precondition)
  exact (coordinates.prodMk repaired).withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

/-- The selected coordinates agree with the mathematical cleanup schedule. -/
theorem diagonalSelectedRepair_coordinates (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalSelectedRepair length diagonalWidth basisWidth).Arguments sizes //
      (diagonalSelectedRepair length diagonalWidth basisWidth).precondition sizes arguments}) :
    some ((diagonalSelectedRepair length diagonalWidth basisWidth).compute sizes arguments).1 =
      IntegerMatrix.diagonalViolation (fun index => (arguments.val 0 index).val) :=
  diagonalRepairCoordinates_spec length diagonalWidth sizes ⟨(fun _ => arguments.val 0), arguments.property.1⟩

/-- The returned entries are the natural gcd and lcm at the selected coordinates. -/
theorem diagonalSelectedRepair_values (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalSelectedRepair length diagonalWidth basisWidth).Arguments sizes //
      (diagonalSelectedRepair length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalSelectedRepair length diagonalWidth basisWidth).compute sizes arguments
    result.2.1.1.val = (Nat.gcd (arguments.val 0 result.1.1).val (arguments.val 0 result.1.2).val : ℤ) ∧
      result.2.1.2.val = (Nat.lcm (arguments.val 0 result.1.1).val (arguments.val 0 result.1.2).val : ℤ) := by
  let innerArguments := fun name => selectedArguments length diagonalWidth basisWidth name sizes arguments
  have valid := selectedArguments_valid length diagonalWidth basisWidth sizes arguments
  exact integerDiagonalBasisStep_natural_values length diagonalWidth basisWidth sizes
    ⟨innerArguments, valid.1⟩ (fun index => (arguments.val 0 index).val) rfl rfl

/-- The returned bases are exactly the mathematical two-coordinate actions. -/
theorem diagonalSelectedRepair_bases (length diagonalWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalSelectedRepair length diagonalWidth basisWidth).Arguments sizes //
      (diagonalSelectedRepair length diagonalWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalSelectedRepair length diagonalWidth basisWidth).compute sizes arguments
    let first := ((arguments.val 0 result.1.1).val : ℤ)
    let second := ((arguments.val 0 result.1.2).val : ℤ)
    (result.2.2.1.val, result.2.2.2.val) =
      (IntegerMatrix.rowPair (Row := Fin (MvPolynomial.eval sizes length)) result.1.1 result.1.2
        (IntegerMatrix.bezoutMatrix first second) (arguments.val 1).val,
       IntegerMatrix.columnPair (Column := Fin (MvPolynomial.eval sizes length)) result.1.1 result.1.2
        (IntegerMatrix.diagonalPairRight first second) (arguments.val 2).val) := by
  let innerArguments := fun name => selectedArguments length diagonalWidth basisWidth name sizes arguments
  have valid := selectedArguments_valid length diagonalWidth basisWidth sizes arguments
  exact integerDiagonalBasisStep_correct length diagonalWidth basisWidth sizes ⟨innerArguments, valid.1⟩

end Polytime2.Computation.Realizable.Internal
