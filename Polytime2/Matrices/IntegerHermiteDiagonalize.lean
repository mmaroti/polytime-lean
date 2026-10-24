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

import Polytime2.Matrices.HermiteAlternatingController

/-! # Polynomial-budget integer Hermite diagonalization

Positive lower triangular square input is diagonalized with both actual bases.
The input width and dimension derive the common entry/determinant width, all
basis capacities, and the pair budget. No storage or stopping controls are
required from callers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def initial (dimension width budget : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := integerMatrices dimension dimension width
  outputDomain := hermiteAlternatingState dimension (hermiteAlternatingEntryWidth dimension width) budget
  precondition _ arguments := (arguments ()).val.IsLowerTriangular ∧ ∀ index, 0 < (arguments ()).val index index
  compute sizes arguments :=
    let common := hermiteAlternatingEntryWidth dimension width
    let extra := budget * (hermiteAlternatingBasisWidth dimension common + dimension + 1)
    let basisWidth := hermiteAlternatingRunBasisWidth dimension common budget
    let matrix := (integerMatrixWiden dimension dimension width (dimension * (width + dimension) + 1)
      common (by dsimp [common, hermiteAlternatingEntryWidth]; ring)).compute sizes ⟨arguments.val, trivial⟩
    let basis := (integerMatrixWiden dimension dimension 1 extra basisWidth rfl).compute sizes
      ⟨fun _ => (integerIdentity dimension).compute sizes ⟨(fun name => nomatch name), trivial⟩, trivial⟩
    (matrix, basis, basis)

private theorem initial_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (initial dimension width budget).Realizable := by
  let computation := initial dimension width budget
  let common := hermiteAlternatingEntryWidth dimension width
  let extra := budget * (hermiteAlternatingBasisWidth dimension common + dimension + 1)
  let basisWidth := hermiteAlternatingRunBasisWidth dimension common budget
  have matrix := (integerMatrixWiden_realizable dimension dimension width (dimension * (width + dimension) + 1)
    common (by dsimp [common, hermiteAlternatingEntryWidth]; ring)).withPrecondition computation.precondition (by intros; trivial)
  have identity := (integerIdentity_realizable dimension).onResults computation.inputDomains computation.precondition
    (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)
  have basis := identity.followedBy (integerMatrixWiden_realizable dimension dimension 1 extra basisWidth rfl)
    rfl (by intros; trivial)
  have bases := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ basis basis
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ matrix bases

/-- Run a prescribed mathematical pair budget, preparing every fixed workspace internally. -/
noncomputable def integerHermiteAlternatingRun (dimension width budget : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (hermiteAlternatingController dimension (hermiteAlternatingEntryWidth dimension width) budget).onResults
    (initial dimension width budget).inputDomains (initial dimension width budget).precondition
    (fun name sizes arguments => match name with
      | .inl _ => ((initial dimension width budget).compute sizes arguments).1
      | .inr false => (initial dimension width budget).compute sizes arguments
      | .inr true => id)
    (by
      intro sizes arguments
      exact ⟨arguments.property.1, arguments.property.2,
        hermiteAlternatingEntryWidth_det_bound dimension width sizes (arguments.val ()), rfl⟩)

/-- Initialization, budget enumeration, and the entire fixed-workspace fold are certified. -/
theorem integerHermiteAlternatingRun_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingRun dimension width budget).Realizable := by
  let computation := integerHermiteAlternatingRun dimension width budget
  apply (hermiteAlternatingController_realizable dimension (hermiteAlternatingEntryWidth dimension width) budget).onResults
    computation.inputDomains computation.precondition _ _
  intro name
  rcases name with singleton | choice
  · exact (initial_realizable dimension width budget).followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  · cases choice
    · exact initial_realizable dimension width budget
    · exact (arrayPositions_realizable budget).onResults computation.inputDomains computation.precondition
        (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)

/-- The public bounded runtime returns exactly the mathematical run and both accumulated bases. -/
theorem integerHermiteAlternatingRun_correct (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingRun dimension width budget).Arguments sizes //
      (integerHermiteAlternatingRun dimension width budget).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingRun dimension width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes budget) (arguments.val ()).val :=
  hermiteAlternatingController_correct dimension (hermiteAlternatingEntryWidth dimension width) budget sizes
    ⟨(fun name => match name with
      | .inl _ => ((initial dimension width budget).compute sizes arguments).1
      | .inr false => (initial dimension width budget).compute sizes arguments
      | .inr true => id),
      ⟨arguments.property.1, arguments.property.2,
        hermiteAlternatingEntryWidth_det_bound dimension width sizes (arguments.val ()), rfl⟩⟩

/-- A polynomial pair budget derived from the mathematical dimension and entry width. -/
noncomputable def hermiteAlternatingBudget (dimension width : MvPolynomial Parameter ℕ) :=
  width * dimension * dimension + 2

/-- Diagonalize positive lower triangular input, deriving the pair budget internally. -/
noncomputable def integerHermiteDiagonalize (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  integerHermiteAlternatingRun dimension width (hermiteAlternatingBudget dimension width)

/-- Complete polynomial-budget diagonalization has a polynomial-time realization. -/
theorem integerHermiteDiagonalize_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteDiagonalize dimension width).Realizable :=
  integerHermiteAlternatingRun_realizable dimension width (hermiteAlternatingBudget dimension width)

/-- The result is positive diagonal and retains the presentation and both unit determinants. -/
theorem integerHermiteDiagonalize_specification (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteDiagonalize dimension width).Arguments sizes //
      (integerHermiteDiagonalize dimension width).precondition sizes arguments}) :
    let result := (integerHermiteDiagonalize dimension width).compute sizes arguments
    result.2.1.val * (arguments.val ()).val * result.2.2.val = result.1.val ∧
      IsUnit result.2.1.val.det ∧ IsUnit result.2.2.val.det ∧
      (∀ row column, row ≠ column → result.1.val row column = 0) ∧
      (∀ index, 0 < result.1.val index index) := by
  let budget := MvPolynomial.eval sizes (hermiteAlternatingBudget dimension width)
  have presentation := IntegerMatrix.hermiteAlternatingRun_preserves budget (arguments.val ()).val
  have shape := IntegerMatrix.hermiteAlternatingRun_triangular budget (arguments.val ()).val
    arguments.property.1 arguments.property.2
  have diagonal : ∀ row column, row ≠ column →
      (IntegerMatrix.hermiteAlternatingRun budget (arguments.val ()).val).1 row column = 0 := by
    simpa [budget, hermiteAlternatingBudget] using
      IntegerMatrix.hermiteAlternatingRun_polynomial_budget (MvPolynomial.eval sizes width) (arguments.val ()).val
        arguments.property.1 arguments.property.2 (arguments.val ()).property
  have same := integerHermiteAlternatingRun_correct dimension width (hermiteAlternatingBudget dimension width) sizes arguments
  rw [← same] at presentation shape diagonal
  exact ⟨presentation.1, presentation.2.1, presentation.2.2, diagonal, shape.2⟩

end Polytime2.Computation
