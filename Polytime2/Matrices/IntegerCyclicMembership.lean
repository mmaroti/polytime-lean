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

import Polytime2.Matrices.IntegerAugmentedMatrix
import Polytime2.Matrices.IntegerSystemSolve
import Polytime2.Computation.Specification

/-! # Membership in products of cyclic groups

Input integer representatives of a generator matrix and target vector, and
one bounded natural modulus per coordinate. Decide whether an integer linear
combination of the generators represents the target in the product of ZMod
coordinates. Positive moduli give the finite cyclic case; modulus zero is
also supported as an integer coordinate. All augmentation and storage costs
are included in the realization.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    Fin 3 → EncodedDomain Parameter
  | 0 => integerMatrices rows generators generatorWidth
  | 1 => (binaryNaturalsOfWidth modulusWidth).arrayOfLength rows
  | 2 => (binaryIntegers targetWidth).arrayOfLength rows

private noncomputable def augmented (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (integerAugmentedMatrix rows generators generatorWidth modulusWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => arguments.val 0 | true => arguments.val 1)
    (by intros; trivial)

private theorem augmented_realizable (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (augmented rows generators generatorWidth modulusWidth targetWidth).Realizable := by
  apply (integerAugmentedMatrix_realizable rows generators generatorWidth modulusWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact Realizable.argument _ (0 : Fin 3) _
  · exact Realizable.argument _ (1 : Fin 3) _

set_option maxHeartbeats 800000 in
private theorem augmented_correct (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (augmented rows generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    ((augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩).val =
      (IntegerMatrix.augmentedMatrix (arguments 0).val (fun row => ((arguments 1 row).val : ℤ))).submatrix id
        (fun column => finSumFinEquiv.symm (Fin.cast (map_add (MvPolynomial.eval sizes) generators rows) column)) := by
  have same := integerAugmentedMatrix_correct rows generators generatorWidth modulusWidth sizes
    (fun choice => match choice with | false => arguments 0 | true => arguments 1)
  exact same

private noncomputable def columns (rows generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    Fin (MvPolynomial.eval sizes (generators + rows)) ≃
      Fin (MvPolynomial.eval sizes generators) ⊕ Fin (MvPolynomial.eval sizes rows) :=
  (finCongr (map_add (MvPolynomial.eval sizes) generators rows)).trans finSumFinEquiv.symm

private theorem augmented_feasible_iff (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (augmented rows generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    let matrix := (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩
    (∃ values, matrix.val.mulVec values = fun row => (arguments 2 row).val) ↔
      ∃ coefficients : Fin (MvPolynomial.eval sizes generators) → ℤ, ∀ row,
        (∑ generator, (coefficients generator : ZMod (arguments 1 row).val) *
          ((arguments 0).val row generator : ZMod (arguments 1 row).val)) =
            ((arguments 2 row).val : ZMod (arguments 1 row).val) := by
  have matrixEq := augmented_correct rows generators generatorWidth modulusWidth targetWidth sizes arguments
  dsimp only
  rw [matrixEq]
  exact (IntegerMatrix.feasible_reindex_columns_iff _ (columns rows generators sizes) _).trans
    (IntegerMatrix.cyclic_span_iff_augmented (arguments 0).val (fun row => (arguments 1 row).val)
      (fun row => (arguments 2 row).val)).symm

/-- Decide cyclic span membership while retaining every generator and modulus column. -/
private noncomputable def membershipImplementation
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  (integerSystemFeasible rows (generators + rows) (integerAugmentedWidth generatorWidth modulusWidth) targetWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes arguments
      | true => arguments.val 2) (by intros; trivial)

/-- Augmentation and certified integer-system feasibility compose polynomially. -/
private theorem membershipImplementation_realizable
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (membershipImplementation rows generators generatorWidth modulusWidth targetWidth).Realizable := by
  apply (integerSystemFeasible_realizable rows (generators + rows)
    (integerAugmentedWidth generatorWidth modulusWidth) targetWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact augmented_realizable rows generators generatorWidth modulusWidth targetWidth
  · exact Realizable.argument _ (2 : Fin 3) _

set_option maxHeartbeats 4000000 in
/-- The Boolean result is exactly existence of integer coefficients in the cyclic coordinates. -/
private theorem membershipImplementation_correct
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (membershipImplementation rows generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    (membershipImplementation rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∃ coefficients : Fin (MvPolynomial.eval sizes generators) → ℤ, ∀ row,
        (∑ generator, (coefficients generator : ZMod (arguments 1 row).val) *
          ((arguments 0).val row generator : ZMod (arguments 1 row).val)) =
            ((arguments 2 row).val : ZMod (arguments 1 row).val) := by
  let matrix := (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩
  have decided := integerSystemFeasible_correct rows (generators + rows)
    (integerAugmentedWidth generatorWidth modulusWidth) targetWidth sizes
    (fun choice => match choice with | false => matrix | true => arguments 2)
  have callEqual : (membershipImplementation rows generators generatorWidth modulusWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ =
      (integerSystemFeasible rows (generators + rows) (integerAugmentedWidth generatorWidth modulusWidth) targetWidth).compute sizes
        ⟨(fun choice => match choice with | false => matrix | true => arguments 2), trivial⟩ := by
    rfl
  have decision := (congrArg (fun flag : Bool => flag = true) callEqual).to_iff.trans decided
  exact decision.trans (augmented_feasible_iff rows generators generatorWidth modulusWidth targetWidth sizes arguments)

/-- Decide cyclic span membership as an ordinary existence predicate. -/
noncomputable def integerCyclicMembership
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  decision (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True)
    (fun sizes arguments => ∃ coefficients : Fin (MvPolynomial.eval sizes generators) → ℤ, ∀ row,
      (∑ generator, (coefficients generator : ZMod (arguments 1 row).val) *
        ((arguments 0).val row generator : ZMod (arguments 1 row).val)) =
          ((arguments 2 row).val : ZMod (arguments 1 row).val))

theorem integerCyclicMembership_realizable
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicMembership rows generators generatorWidth modulusWidth targetWidth).Realizable :=
  (membershipImplementation_realizable rows generators generatorWidth modulusWidth targetWidth).decision _
    (fun sizes arguments _valid => membershipImplementation_correct rows generators generatorWidth modulusWidth targetWidth sizes arguments)

/-- The result is true exactly when integer coefficients represent the cyclic target. -/
theorem integerCyclicMembership_correct
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicMembership rows generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    (integerCyclicMembership rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∃ coefficients : Fin (MvPolynomial.eval sizes generators) → ℤ, ∀ row,
        (∑ generator, (coefficients generator : ZMod (arguments 1 row).val) *
          ((arguments 0).val row generator : ZMod (arguments 1 row).val)) =
            ((arguments 2 row).val : ZMod (arguments 1 row).val) :=
  decision_correct _ _ _ sizes ⟨arguments, trivial⟩

/-- Capacity of both generator and modulus coefficients, derived from the cyclic input. -/
noncomputable def integerCyclicWitnessWidth
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :=
  integerSystemWitnessWidth rows (generators + rows) (integerAugmentedWidth generatorWidth modulusWidth) targetWidth

private noncomputable def solved (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (integerSystemSolve rows (generators + rows) (integerAugmentedWidth generatorWidth modulusWidth) targetWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes arguments
      | true => arguments.val 2) (by intros; trivial)

private theorem solved_realizable (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (solved rows generators generatorWidth modulusWidth targetWidth).Realizable := by
  apply (integerSystemSolve_realizable rows (generators + rows)
    (integerAugmentedWidth generatorWidth modulusWidth) targetWidth).onResults
    (inputs rows generators generatorWidth modulusWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact augmented_realizable rows generators generatorWidth modulusWidth targetWidth
  · exact Realizable.argument _ (2 : Fin 3) _

private noncomputable def coefficientCarrier
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :=
  Option ((Fin (MvPolynomial.eval sizes generators) ⊕ Fin (MvPolynomial.eval sizes rows)) →
    (binaryIntegers (integerCyclicWitnessWidth rows generators generatorWidth modulusWidth targetWidth)).Carrier sizes)

private noncomputable def coefficientEquiv
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    coefficientCarrier rows generators generatorWidth modulusWidth targetWidth sizes ≃
      (solved rows generators generatorWidth modulusWidth targetWidth).outputDomain.Carrier sizes :=
  Equiv.optionCongr (Equiv.arrowCongr (columns rows generators sizes)
    (Equiv.refl ((binaryIntegers (integerCyclicWitnessWidth rows generators generatorWidth modulusWidth targetWidth)).Carrier sizes))).symm

/-- Return actual generator and modulus coefficients, or the no-membership alternative. -/
noncomputable def integerCyclicSolve
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  (solved rows generators generatorWidth modulusWidth targetWidth).reinterpretOutput
    ((solved rows generators generatorWidth modulusWidth targetWidth).outputDomain.reindex
      (coefficientCarrier rows generators generatorWidth modulusWidth targetWidth)
      (coefficientEquiv rows generators generatorWidth modulusWidth targetWidth))
    (fun sizes => (coefficientEquiv rows generators generatorWidth modulusWidth targetWidth sizes).symm)

/-- Reindexing the augmented solution retains exactly its canonical optional word. -/
theorem integerCyclicSolve_realizable
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).Realizable :=
  (solved_realizable rows generators generatorWidth modulusWidth targetWidth).reindexOutput
    (coefficientCarrier rows generators generatorWidth modulusWidth targetWidth)
    (coefficientEquiv rows generators generatorWidth modulusWidth targetWidth)

set_option maxHeartbeats 4000000 in
/-- The returned coefficients satisfy the full augmented integer equation. -/
theorem integerCyclicSolve_some_equation
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).Arguments sizes)
    (values : (Fin (MvPolynomial.eval sizes generators) ⊕ Fin (MvPolynomial.eval sizes rows)) →
      (binaryIntegers (integerCyclicWitnessWidth rows generators generatorWidth modulusWidth targetWidth)).Carrier sizes)
    (returned : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values) :
    (IntegerMatrix.augmentedMatrix (arguments 0).val (fun row => ((arguments 1 row).val : ℤ))).mulVec
      (fun index => (values index).val) = fun row => (arguments 2 row).val := by
  have recovered := (Equiv.symm_apply_eq (coefficientEquiv rows generators generatorWidth modulusWidth targetWidth sizes)).mp returned
  have equation := integerSystemSolve_some_correct rows (generators + rows)
    (integerAugmentedWidth generatorWidth modulusWidth) targetWidth sizes
    (fun choice => match choice with
      | false => (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩
      | true => arguments 2)
    (fun index => values (columns rows generators sizes index)) recovered
  have matrixEq := augmented_correct rows generators generatorWidth modulusWidth targetWidth sizes arguments
  rw [matrixEq] at equation
  change ((IntegerMatrix.augmentedMatrix (arguments 0).val (fun row => ((arguments 1 row).val : ℤ))).submatrix
    id (columns rows generators sizes)).mulVec (fun column => (values (columns rows generators sizes column)).val) =
      (fun row => (arguments 2 row).val) at equation
  rw [Matrix.submatrix_mulVec_equiv] at equation
  simpa only [Function.comp_def, Equiv.apply_symm_apply, Function.id_def] using equation

/-- The generator part of every returned witness represents the cyclic target. -/
theorem integerCyclicSolve_some_correct
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).Arguments sizes)
    (values : (Fin (MvPolynomial.eval sizes generators) ⊕ Fin (MvPolynomial.eval sizes rows)) →
      (binaryIntegers (integerCyclicWitnessWidth rows generators generatorWidth modulusWidth targetWidth)).Carrier sizes)
    (returned : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values) :
    ∀ row, (∑ generator, ((values (.inl generator)).val : ZMod (arguments 1 row).val) *
      ((arguments 0).val row generator : ZMod (arguments 1 row).val)) = ((arguments 2 row).val : ZMod (arguments 1 row).val) :=
  IntegerMatrix.cyclic_coefficients_of_augmented_solution _ _ _ _
    (integerCyclicSolve_some_equation rows generators generatorWidth modulusWidth targetWidth sizes arguments values returned)

set_option maxHeartbeats 4000000 in
/-- No witness is returned precisely when no integer coefficients represent the cyclic target. -/
theorem integerCyclicSolve_none_iff
    (rows generators generatorWidth modulusWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).Arguments sizes) :
    (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none ↔
      ¬ ∃ coefficients : Fin (MvPolynomial.eval sizes generators) → ℤ, ∀ row,
        (∑ generator, (coefficients generator : ZMod (arguments 1 row).val) *
          ((arguments 0).val row generator : ZMod (arguments 1 row).val)) = ((arguments 2 row).val : ZMod (arguments 1 row).val) := by
  have noSolution := integerSystemSolve_none_iff rows (generators + rows)
    (integerAugmentedWidth generatorWidth modulusWidth) targetWidth sizes
    (fun choice => match choice with
      | false => (augmented rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩
      | true => arguments 2)
  have resultEq : (integerCyclicSolve rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none ↔
      (solved rows generators generatorWidth modulusWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none := by
    exact Equiv.symm_apply_eq (coefficientEquiv rows generators generatorWidth modulusWidth targetWidth sizes)
  exact resultEq.trans (noSolution.trans
    (not_congr (augmented_feasible_iff rows generators generatorWidth modulusWidth targetWidth sizes arguments)))

end Polytime2.Computation
