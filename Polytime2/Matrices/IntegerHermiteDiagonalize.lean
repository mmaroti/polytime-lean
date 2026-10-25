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

import Polytime2.Computation.Specification
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
  exact matrix.prodMk (basis.prodMk basis)

/-- Run a prescribed mathematical pair budget, preparing every fixed workspace internally. -/
private noncomputable def implementation (dimension width budget : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
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
private theorem implementation_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (implementation dimension width budget).Realizable := by
  let computation := implementation dimension width budget
  apply (hermiteAlternatingController_realizable dimension (hermiteAlternatingEntryWidth dimension width) budget).onResults
    computation.inputDomains computation.precondition _ _
  intro name
  rcases name with singleton | choice
  · exact (initial_realizable dimension width budget).fst
  · cases choice
    · exact initial_realizable dimension width budget
    · exact (arrayPositions_realizable budget).onResults computation.inputDomains computation.precondition
        (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)

/-- The public bounded runtime returns exactly the mathematical run and both accumulated bases. -/
private theorem implementation_correct (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation dimension width budget).Arguments sizes //
      (implementation dimension width budget).precondition sizes arguments}) :
    let result := (implementation dimension width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes budget) (arguments.val ()).val :=
  hermiteAlternatingController_correct dimension (hermiteAlternatingEntryWidth dimension width) budget sizes
    ⟨(fun name => match name with
      | .inl _ => ((initial dimension width budget).compute sizes arguments).1
      | .inr false => (initial dimension width budget).compute sizes arguments
      | .inr true => id),
      ⟨arguments.property.1, arguments.property.2,
        hermiteAlternatingEntryWidth_det_bound dimension width sizes (arguments.val ()), rfl⟩⟩

/-- The mathematical traversal and its actual accumulated bases. Workspace
preparation and controller wiring stay behind the computation boundary. -/
noncomputable def integerHermiteAlternatingRun (dimension width budget : MvPolynomial Parameter ℕ) :
    Computation Parameter (Unit) :=
  specificationBy (fun _ => integerMatrices dimension dimension width)
    (hermiteAlternatingState dimension (hermiteAlternatingEntryWidth dimension width) budget) (fun _ arguments => (arguments ()).val.IsLowerTriangular ∧ ∀ index, 0 < (arguments ()).val index index)
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.val))
    (fun sizes arguments => IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes budget) (arguments.val ()).val)
    (fun sizes arguments => ⟨(implementation dimension width budget).compute sizes arguments,
      implementation_correct dimension width budget sizes arguments⟩)

theorem integerHermiteAlternatingRun_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingRun dimension width budget).Realizable := by
  apply (implementation_realizable dimension width budget).specificationBy
  · intro sizes
    exact Subtype.val_injective.prodMap (Subtype.val_injective.prodMap Subtype.val_injective)
  · intro sizes arguments valid
    exact implementation_correct dimension width budget sizes ⟨arguments, valid⟩

/-- Observe the ordinary mathematical answer without expanding the controller. -/
theorem integerHermiteAlternatingRun_correct (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingRun dimension width budget).Arguments sizes //
      (integerHermiteAlternatingRun dimension width budget).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingRun dimension width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes budget) (arguments.val ()).val := by
  exact specificationBy_correct _ (integerHermiteAlternatingRun dimension width budget).outputDomain _
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.val)) _ _ sizes arguments

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

end Polytime2.Computation
