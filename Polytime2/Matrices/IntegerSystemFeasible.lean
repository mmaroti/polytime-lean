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

import Polytime2.Matrices.IntegerSmithReduction
import Polytime2.Matrices.IntegerDiagonalFeasible
import Polytime2.Matrices.IntegerDiagonalSolution
import Polytime2.Matrices.IntegerMulVec
import Polytime2.Matrices.IntegerQuotientCoordinates
import Polytime2.Computation.Specification

/-! # Integer linear-system feasibility

Input an arbitrary rectangular integer matrix and an integer target vector,
with independent magnitude widths. Return true exactly when an integer vector
solves the system. All Smith capacities and the transformed-target width are
derived internally from the original input sizes. No rank or nonsingularity
precondition is required.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    Bool → EncodedDomain Parameter :=
  fun choice => if choice then (binaryIntegers targetWidth).arrayOfLength rows
    else integerMatrices rows columns matrixWidth

private noncomputable def smith (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (integerSmithReduction rows columns matrixWidth).onResults (inputs rows columns matrixWidth targetWidth)
    (fun _ _ => True) (fun _ _ arguments => arguments.val false) (by intros; trivial)

private theorem smith_realizable (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (smith rows columns matrixWidth targetWidth).Realizable := by
  apply (integerSmithReduction_realizable rows columns matrixWidth).onResults _ _ _ (by intros; trivial)
  intro singleton
  cases singleton
  exact Realizable.argument _ false _

private theorem smith_isSmithForm (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (smith rows columns matrixWidth targetWidth).Arguments sizes) :
    let result := (smith rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩
    IntegerMatrix.IsSmithForm (arguments false).val result.2.1.val result.2.2.1.val result.2.2.2.val result.1.val := by
  have form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
    ⟨fun _ => arguments false, trivial⟩
  exact form

private noncomputable def transformed (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (integerMatrixMulVec rows rows (smithReductionLeftWidth rows columns matrixWidth) targetWidth).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => ((smith rows columns matrixWidth targetWidth).compute sizes arguments).2.2.1
      | true => arguments.val true) (by intros; trivial)

private theorem transformed_realizable (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (transformed rows columns matrixWidth targetWidth).Realizable := by
  have actual := smith_realizable rows columns matrixWidth targetWidth
  apply (integerMatrixMulVec_realizable rows rows (smithReductionLeftWidth rows columns matrixWidth) targetWidth).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact actual.snd.snd.fst
  · exact Realizable.argument _ true _

/-- Decide whether an arbitrary rectangular integer system has an integer solution. -/
private noncomputable def feasibleImplementation
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerDiagonalFeasible rows columns (smithReductionDiagonalWidth rows columns matrixWidth)
    (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => ((smith rows columns matrixWidth targetWidth).compute sizes arguments).2.1
      | true => (transformed rows columns matrixWidth targetWidth).compute sizes arguments)
    (by intros; trivial)

/-- Smith reduction, target transport, and diagonal divisibility compose polynomially. -/
private theorem feasibleImplementation_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (feasibleImplementation rows columns matrixWidth targetWidth).Realizable := by
  apply (integerDiagonalFeasible_realizable rows columns (smithReductionDiagonalWidth rows columns matrixWidth)
    (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact (((smith_realizable rows columns matrixWidth targetWidth).snd).fst)
  · exact transformed_realizable rows columns matrixWidth targetWidth

/-- The returned Boolean has the ordinary existential integer-system specification. -/
private theorem feasibleImplementation_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (feasibleImplementation rows columns matrixWidth targetWidth).Arguments sizes) :
    (feasibleImplementation rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  let result := (smith rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩
  have form := smith_isSmithForm rows columns matrixWidth targetWidth sizes arguments
  have tested := integerDiagonalFeasible_correct rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth) sizes
    (fun choice => match choice with
      | false => result.2.1
      | true => (transformed rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩)
    result.1.val form.2.2.2
  have equivalent := IntegerMatrix.feasible_iff_transformed (arguments false).val result.2.1.val
    result.2.2.1.val result.2.2.2.val form.1 form.2.1 form.2.2.1 (fun row => (arguments true row).val)
  exact tested.trans equivalent.symm

/-- Decide the ordinary mathematical integer-image predicate. -/
noncomputable def integerSystemFeasible
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  decision (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun _ arguments => ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val)

/-- The Smith-based implementation certifies the mathematical decision. -/
theorem integerSystemFeasible_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemFeasible rows columns matrixWidth targetWidth).Realizable :=
  (feasibleImplementation_realizable rows columns matrixWidth targetWidth).decision _
    (fun sizes arguments _valid => feasibleImplementation_correct rows columns matrixWidth targetWidth sizes arguments)

/-- The result is true exactly for targets in the ordinary integer image. -/
theorem integerSystemFeasible_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemFeasible rows columns matrixWidth targetWidth).Arguments sizes) :
    (integerSystemFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val :=
  decision_correct _ _ _ sizes ⟨arguments, trivial⟩

private noncomputable def coordinates (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (integerDiagonalSolution rows columns (smithReductionDiagonalWidth rows columns matrixWidth)
    (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => ((smith rows columns matrixWidth targetWidth).compute sizes arguments).2.1
      | true => (transformed rows columns matrixWidth targetWidth).compute sizes arguments) (by intros; trivial)

private theorem coordinates_realizable (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (coordinates rows columns matrixWidth targetWidth).Realizable := by
  apply (integerDiagonalSolution_realizable rows columns (smithReductionDiagonalWidth rows columns matrixWidth)
    (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact (((smith_realizable rows columns matrixWidth targetWidth).snd).fst)
  · exact transformed_realizable rows columns matrixWidth targetWidth

/-- Derive the original-coordinate witness capacity from the mathematical input sizes. -/
noncomputable def integerSystemWitnessWidth (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  columns + smithReductionRightWidth rows columns matrixWidth +
    (smithReductionDiagonalWidth rows columns matrixWidth +
      (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth))

/-- Recover an original-coordinate candidate, which solves the system whenever it is feasible. -/
private noncomputable def witnessImplementation
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerMatrixMulVec columns columns (smithReductionRightWidth rows columns matrixWidth)
    (smithReductionDiagonalWidth rows columns matrixWidth +
      (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth))).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => ((smith rows columns matrixWidth targetWidth).compute sizes arguments).2.2.2
      | true => (coordinates rows columns matrixWidth targetWidth).compute sizes arguments) (by intros; trivial)

/-- Coordinate division and multiplication by the actual right basis are realized. -/
private theorem witnessImplementation_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (witnessImplementation rows columns matrixWidth targetWidth).Realizable := by
  apply (integerMatrixMulVec_realizable columns columns (smithReductionRightWidth rows columns matrixWidth)
    (smithReductionDiagonalWidth rows columns matrixWidth +
      (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth))).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact ((((smith_realizable rows columns matrixWidth targetWidth).snd).snd).snd)
  · exact coordinates_realizable rows columns matrixWidth targetWidth

/-- The deterministic witness is the right Smith basis applied to the ordinary
coordinate quotients. Feasibility is needed only for its solution contract. -/
noncomputable def integerSystemWitness
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specificationBy (inputs rows columns matrixWidth targetWidth)
    ((binaryIntegers (integerSystemWitnessWidth rows columns matrixWidth targetWidth)).arrayOfLength columns)
    (fun _ _ => True) (fun _ result column => (result column).val)
    (fun sizes arguments =>
      let result := (integerSmithReduction rows columns matrixWidth).compute sizes
        ⟨fun _ => arguments.val false, trivial⟩
      result.2.2.2.val.mulVec (IntegerMatrix.diagonalQuotientSolution result.2.1.val
        (result.2.2.1.val.mulVec (fun row => (arguments.val true row).val))))
    (fun sizes arguments => ⟨(witnessImplementation rows columns matrixWidth targetWidth).compute sizes arguments, rfl⟩)

theorem integerSystemWitness_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemWitness rows columns matrixWidth targetWidth).Realizable := by
  apply (witnessImplementation_realizable rows columns matrixWidth targetWidth).specificationBy
  · intro sizes
    exact Function.Injective.piMap (fun _ => Subtype.val_injective)
  · intros
    rfl

/-- Observe the integer witness without exposing coordinate preparation or widths. -/
theorem integerSystemWitness_value
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemWitness rows columns matrixWidth targetWidth).Arguments sizes) :
    let result := (integerSmithReduction rows columns matrixWidth).compute sizes
      ⟨fun _ => arguments false, trivial⟩
    (fun column => ((integerSystemWitness rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ column).val) =
      result.2.2.2.val.mulVec (IntegerMatrix.diagonalQuotientSolution result.2.1.val
        (result.2.2.1.val.mulVec (fun row => (arguments true row).val))) := by
  exact specificationBy_correct _ (integerSystemWitness rows columns matrixWidth targetWidth).outputDomain _
    (fun _ result column => (result column).val) _ _ sizes ⟨arguments, trivial⟩

/-- A feasible system is solved by the computed original-coordinate witness. -/
theorem integerSystemWitness_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemWitness rows columns matrixWidth targetWidth).Arguments sizes)
    (feasible : ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val) :
    (arguments false).val.mulVec (fun column =>
      ((integerSystemWitness rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ column).val) =
      fun row => (arguments true row).val := by
  let result := (smith rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩
  have form := smith_isSmithForm rows columns matrixWidth targetWidth sizes arguments
  have diagonalFeasible := (IntegerMatrix.smithFeasible_iff (arguments false).val result.2.1.val
    result.2.2.1.val result.2.2.2.val result.1.val form (fun row => (arguments true row).val)).mp feasible
  have solution := IntegerMatrix.smithSolution_correct (arguments false).val result.2.1.val
    result.2.2.1.val result.2.2.2.val result.1.val form (fun row => (arguments true row).val) diagonalFeasible
  rw [← IntegerMatrix.diagonalQuotientSolution_eq result.2.1.val result.1.val form.2.2.2] at solution
  rw [integerSystemWitness_value]
  exact solution


/-- Return the actual torsion and free coordinates of an integer target. -/
private noncomputable def quotientImplementation
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerMatrixCyclicCoordinates rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (smithReductionLeftWidth rows columns matrixWidth) targetWidth).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun name sizes arguments =>
      let result := (integerSmithReduction rows columns matrixWidth).compute sizes
        ⟨fun _ => arguments.val false, trivial⟩
      match name with
      | 0 => result.2.1
      | 1 => result.2.2.1
      | 2 => arguments.val true) (by intros; trivial)

/-- Smith reduction and normalization of the transformed target compose. -/
private theorem quotientImplementation_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (quotientImplementation rows columns matrixWidth targetWidth).Realizable := by
  have payload := (smith_realizable rows columns matrixWidth targetWidth).snd
  apply (integerMatrixCyclicCoordinates_realizable rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (smithReductionLeftWidth rows columns matrixWidth) targetWidth).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro name
  fin_cases name
  · exact payload.fst
  · exact payload.snd.fst
  · exact Realizable.argument _ true _

private theorem quotientImplementation_observe
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (quotientImplementation rows columns matrixWidth targetWidth).Arguments sizes) :
    let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
      ⟨fun _ => arguments false, trivial⟩
    (fun row =>
      let result := (quotientImplementation rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ row
      (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus)) =
      (fun row =>
        let modulus := (IntegerMatrix.rowDiagonal smith.2.1.val row).natAbs
        ⟨modulus, (smith.2.2.1.val.mulVec (fun row => (arguments true row).val) row : ZMod modulus)⟩) := by
  let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
    ⟨fun _ => arguments false, trivial⟩
  exact integerMatrixCyclicCoordinates_observe rows columns
    (smithReductionDiagonalWidth rows columns matrixWidth)
    (smithReductionLeftWidth rows columns matrixWidth) targetWidth sizes
    (fun name => match name with | 0 => smith.2.1 | 1 => smith.2.2.1 | 2 => arguments true)

/-- The ordinary quotient coordinates for the deterministic Smith presentation.
Only the modulus and its actual group element enter the mathematical contract. -/
noncomputable def integerSystemQuotientCoordinates
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specificationBy (inputs rows columns matrixWidth targetWidth)
    ((boundedCyclic (smithReductionDiagonalWidth rows columns matrixWidth)
      (smithReductionDiagonalWidth rows columns matrixWidth +
        (rows + smithReductionLeftWidth rows columns matrixWidth + targetWidth))).arrayOfLength rows)
    (fun _ _ => True)
    (fun _ result row => (⟨(result row).1.val, (result row).2.val⟩ : (modulus : ℕ) × ZMod modulus))
    (fun sizes arguments row =>
      let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
        ⟨fun _ => arguments.val false, trivial⟩
      let modulus := (IntegerMatrix.rowDiagonal smith.2.1.val row).natAbs
      ⟨modulus, (smith.2.2.1.val.mulVec (fun row => (arguments.val true row).val) row : ZMod modulus)⟩)
    (fun sizes arguments => ⟨(quotientImplementation rows columns matrixWidth targetWidth).compute sizes arguments,
      quotientImplementation_observe rows columns matrixWidth targetWidth sizes arguments.val⟩)

theorem integerSystemQuotientCoordinates_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).Realizable := by
  apply (quotientImplementation_realizable rows columns matrixWidth targetWidth).specificationBy
  · intro sizes
    exact Function.Injective.piMap (fun _ => Fin.val_injective.sigma_map (fun _ => Subtype.val_injective))
  · intro sizes arguments valid
    exact quotientImplementation_observe rows columns matrixWidth targetWidth sizes arguments

/-- Observe the whole mathematical quotient map without unpacking its preparation. -/
theorem integerSystemQuotientCoordinates_observe
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).Arguments sizes) :
    let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
      ⟨fun _ => arguments false, trivial⟩
    (fun row =>
      let result := (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ row
      (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus)) =
      (fun row =>
        let modulus := (IntegerMatrix.rowDiagonal smith.2.1.val row).natAbs
        ⟨modulus, (smith.2.2.1.val.mulVec (fun row => (arguments true row).val) row : ZMod modulus)⟩) := by
  exact specificationBy_correct _ (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).outputDomain _
    (fun _ result row => (⟨(result row).1.val, (result row).2.val⟩ : (modulus : ℕ) × ZMod modulus)) _ _ sizes ⟨arguments, trivial⟩

end Polytime2.Computation
