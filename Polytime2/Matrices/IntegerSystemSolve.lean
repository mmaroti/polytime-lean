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
noncomputable def integerSystemSolve
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (optionalWhen (solutionDomain rows columns matrixWidth targetWidth)).onResults
    (inputs rows columns matrixWidth targetWidth) (fun _ _ => True)
    (fun choice sizes arguments => prepared rows columns matrixWidth targetWidth sizes arguments.val choice)
    (by intros; trivial)

set_option maxHeartbeats 4000000 in
/-- Feasibility, witness recovery, and the generic optional constructor compose. -/
theorem integerSystemSolve_realizable
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) :
    (integerSystemSolve rows columns matrixWidth targetWidth).Realizable := by
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

set_option maxHeartbeats 4000000 in
/-- Every returned vector solves the original system. -/
theorem integerSystemSolve_some_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes)
    (values : ((binaryIntegers (integerSystemWitnessWidth rows columns matrixWidth targetWidth)).arrayOfLength columns).Carrier sizes)
    (returned : (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = some values) :
    (arguments false).val.mulVec (fun column => (values column).val) = fun row => (arguments true row).val := by
  have specified := (optionalWhen_some_iff (solutionDomain rows columns matrixWidth targetWidth) sizes
    (prepared rows columns matrixWidth targetWidth sizes arguments) values).mp returned
  dsimp only [prepared] at specified
  have feasible := (integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments).mp specified.1
  have solution := integerSystemWitness_correct rows columns matrixWidth targetWidth sizes arguments feasible
  have same := congrArg (fun candidate : (solutionDomain rows columns matrixWidth targetWidth).Carrier sizes =>
    (arguments false).val.mulVec (fun column => (candidate column).val)) specified.2
  exact same.symm.trans solution

set_option maxHeartbeats 4000000 in
/-- The absent result is equivalent to nonexistence of any integer solution. -/
theorem integerSystemSolve_none_iff
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerSystemSolve rows columns matrixWidth targetWidth).Arguments sizes) :
    (integerSystemSolve rows columns matrixWidth targetWidth).compute sizes ⟨arguments, trivial⟩ = none ↔
      ¬ ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  have rejected := optionalWhen_none_iff (solutionDomain rows columns matrixWidth targetWidth) sizes
    (prepared rows columns matrixWidth targetWidth sizes arguments)
  dsimp only [prepared] at rejected
  exact rejected.trans (not_congr (integerSystemFeasible_correct rows columns matrixWidth targetWidth sizes arguments))

end Polytime2.Computation
