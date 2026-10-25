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

import Polytime2.Matrices.IntegerSystemFeasible
import Polytime2.Computation.Optional

/-! # Explicit integer solutions or no solution

Input an arbitrary bounded rectangular integer matrix and target vector.
Return none exactly when the system has no integer solution; otherwise return
an actual bounded integer solution vector. The output width is derived from
the original dimensions and entry widths. Empty and singular matrices require
no extra preconditions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open scoped Classical

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def solutionDomain (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :=
  (binaryIntegers (integerSystemWitnessWidth rows columns matrixWidth targetWidth)).arrayOfLength columns

private noncomputable def inputs (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    Bool → EncodedDomain Parameter :=
  fun choice => if choice then (binaryIntegers targetWidth).arrayOfLength rows
    else integerMatrices rows columns matrixWidth

private noncomputable def prepared (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (inputs rows columns matrixWidth targetWidth name).Carrier sizes) :
    (optionalWhen (solutionDomain rows columns matrixWidth targetWidth)).Arguments sizes :=
  fun choice => match choice with
    | false => (integerSystemFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩
    | true => (integerSystemWitness rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩

/-- Return an actual integer solution, or the mathematical no-solution outcome. -/
private noncomputable def implementation
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (optionalWhen (solutionDomain rows columns matrixWidth targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => prepared rows columns matrixWidth targetWidth sizes arguments.val choice)
    (by intros; trivial)

/-- Feasibility, witness recovery, and the generic optional constructor compose. -/
private theorem implementation_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (implementation rows columns matrixWidth targetWidth).Realizable := by
  apply (optionalWhen_realizable (solutionDomain rows columns matrixWidth targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · have ready := (integerSystemFeasible_realizable rows columns matrixWidth targetWidth).withSpecification
      (fun _ _ => True) (fun sizes arguments => prepared rows columns matrixWidth targetWidth sizes arguments.val false)
      (by intros; trivial) (by intros; rfl)
    exact ready
  · have ready := (integerSystemWitness_realizable rows columns matrixWidth targetWidth).withSpecification
      (fun _ _ => True) (fun sizes arguments => prepared rows columns matrixWidth targetWidth sizes arguments.val true)
      (by intros; trivial) (by intros; rfl)
    exact ready

/-- Return the chosen bounded witness precisely when an ordinary integer
solution exists. The public answer contains no optional-constructor pipeline. -/
noncomputable def integerSystemSolve
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool := by
  classical
  exact specification (inputs rows columns matrixWidth targetWidth)
    (optional (solutionDomain rows columns matrixWidth targetWidth)) (fun _ _ => True)
    (fun sizes arguments =>
      if ∃ values, (arguments.val false).val.mulVec values = fun row => (arguments.val true row).val then
        some ((integerSystemWitness rows columns matrixWidth targetWidth).compute sizes arguments)
      else none)

/-- The composed implementation certifies the mathematical optional answer. -/
theorem integerSystemSolve_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemSolve rows columns matrixWidth targetWidth).Realizable := by
  classical
  apply (implementation_realizable rows columns matrixWidth targetWidth).specification
  intro sizes arguments valid
  dsimp only [optionalWhen, prepared]
  by_cases feasible : ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val
  · have tested := (integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments).mpr feasible
    simp only [tested, feasible, ite_true]
  · have tested : (integerSystemFeasible rows columns matrixWidth targetWidth).compute sizes ⟨arguments, valid⟩ = false := by
      apply Bool.eq_false_iff.mpr
      exact fun accepted => feasible ((integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments).mp accepted)
    simp only [tested, feasible, ite_false, Bool.false_eq_true]

/-- Evaluate only the public mathematical choice, leaving its implementation hidden. -/
theorem integerSystemSolve_compute
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes) :
    (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ =
      if ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val then
        some ((integerSystemWitness rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩)
      else none := by
  classical
  exact specification_compute _ _ _ _ _ _

/-- Every returned vector solves the original integer system. -/
theorem integerSystemSolve_some_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes)
    (values : ((binaryIntegers (integerSystemWitnessWidth rows columns matrixWidth targetWidth)).arrayOfLength columns).Carrier sizes)
    (returned : (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values) :
    (arguments false).val.mulVec (fun column => (values column).val) = fun row => (arguments true row).val := by
  classical
  rw [integerSystemSolve_compute] at returned
  split_ifs at returned with feasible
  · cases Option.some.inj returned
    exact integerSystemWitness_correct rows columns matrixWidth targetWidth sizes arguments feasible

/-- No result is returned exactly when the mathematical system is infeasible. -/
theorem integerSystemSolve_none_iff
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes) :
    (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none ↔
      ¬ ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  classical
  rw [integerSystemSolve_compute]
  split_ifs <;> simp_all

end Polytime2.Computation
