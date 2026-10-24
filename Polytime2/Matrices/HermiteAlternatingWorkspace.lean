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

import Polytime2.Matrices.IntegerHermiteAlternatingStep

/-! # Fixed-width storage for an alternating Hermite pair

At a common entry and determinant bound, each pair returns its matrix at the
same width and each basis at a dimension-derived polynomial width. The public
wrapper prepares that common bound from the original input width, requiring
only positive lower triangular input.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- A dimension-derived magnitude width for each pair's two actual bases. -/
noncomputable def hermiteAlternatingBasisWidth (dimension width : MvPolynomial Parameter ℕ) :=
  1 + dimension * IntegerMatrix.hermiteSweepBasisIncrement dimension width

namespace Realizable.Internal

private def allowed (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteAlternatingStepRaw dimension width).Arguments sizes) : Prop :=
  (arguments ()).val.IsLowerTriangular ∧ (∀ index, 0 < (arguments ()).val index index) ∧
    (arguments ()).val.det.natAbs < 2 ^ MvPolynomial.eval sizes width

private theorem fits (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingStepRaw dimension width).Arguments sizes //
      allowed dimension width sizes arguments}) :
    let result := (integerHermiteAlternatingStepRaw dimension width).compute sizes ⟨arguments.val, trivial⟩
    (∀ row column, (result.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, (result.2.1.val row column).natAbs <
      2 ^ MvPolynomial.eval sizes (hermiteAlternatingBasisWidth dimension width)) ∧
    (∀ row column, (result.2.2.val row column).natAbs <
      2 ^ MvPolynomial.eval sizes (hermiteAlternatingBasisWidth dimension width)) := by
  have matrix := IntegerMatrix.hermiteAlternatingStep_entry_le_det (arguments.val ()).val
    arguments.property.1 arguments.property.2.1
  have bases := IntegerMatrix.hermiteAlternatingStep_basis_bound (MvPolynomial.eval sizes width)
    (arguments.val ()).val arguments.property.1 arguments.property.2.1 (arguments.val ()).property arguments.property.2.2
  have same := integerHermiteAlternatingStepRaw_correct dimension width sizes ⟨arguments.val, trivial⟩
  rw [← same] at matrix bases
  refine ⟨fun row column => (matrix row column).trans_lt arguments.property.2.2, ?_⟩
  simpa [hermiteAlternatingBasisWidth, IntegerMatrix.hermiteSweepBasisIncrement] using bases

/-- Internal pair kernel at a common determinant bound, retaining fixed entry width. -/
noncomputable def integerHermiteAlternatingPair (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerHermiteAlternatingStepRaw dimension width).inputDomains
  outputDomain := (integerMatrices dimension dimension width).prod
    ((integerMatrices dimension dimension (hermiteAlternatingBasisWidth dimension width)).prod
      (integerMatrices dimension dimension (hermiteAlternatingBasisWidth dimension width)))
  precondition := allowed dimension width
  compute sizes arguments :=
    let result := (integerHermiteAlternatingStepRaw dimension width).compute sizes ⟨arguments.val, trivial⟩
    (⟨result.1.val, (fits dimension width sizes arguments).1⟩,
      ⟨result.2.1.val, (fits dimension width sizes arguments).2.1⟩,
      ⟨result.2.2.val, (fits dimension width sizes arguments).2.2⟩)

/-- Existing matrix resizing discards only bits proved to be zero. -/
theorem integerHermiteAlternatingPair_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingPair dimension width).Realizable := by
  let computation := integerHermiteAlternatingPair dimension width
  let firstWidth := hermiteRowsWorkspace width dimension
  let capacity := 1 + firstWidth + hermiteRowsWorkspace firstWidth dimension
  let basisWidth := hermiteAlternatingBasisWidth dimension width
  have actual := (integerHermiteAlternatingStepRaw_realizable dimension width).withPrecondition
    computation.precondition (by intros; trivial)
  have matrix := actual.fst
  have bases := actual.snd
  have left := bases.fst
  have right := bases.snd
  have matrixReady := matrix.followedBy (integerMatrixResize_realizable dimension dimension capacity width)
    rfl (by intro sizes arguments valid; exact (fits dimension width sizes ⟨arguments, valid⟩).1)
  have leftReady := left.followedBy (integerMatrixResize_realizable dimension dimension firstWidth basisWidth)
    rfl (by intro sizes arguments valid; exact (fits dimension width sizes ⟨arguments, valid⟩).2.1)
  have rightReady := right.followedBy (integerMatrixResize_realizable dimension dimension capacity basisWidth)
    rfl (by intro sizes arguments valid; exact (fits dimension width sizes ⟨arguments, valid⟩).2.2)
  have paired := leftReady.prodMk rightReady
  exact matrixReady.prodMk paired

/-- Resizing retains exactly the mathematical pair and both actual bases. -/
theorem integerHermiteAlternatingPair_correct (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingPair dimension width).Arguments sizes //
      (integerHermiteAlternatingPair dimension width).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingPair dimension width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingStep (arguments.val ()).val :=
  integerHermiteAlternatingStepRaw_correct dimension width sizes ⟨arguments.val, trivial⟩

end Realizable.Internal

/-- Common magnitude width for entries and determinant, derived from the input. -/
noncomputable def hermiteAlternatingEntryWidth (dimension width : MvPolynomial Parameter ℕ) :=
  width + dimension * (width + dimension) + 1

/-- The common entry width also bounds the determinant of the original matrix. -/
theorem hermiteAlternatingEntryWidth_det_bound (dimension width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (matrix : (integerMatrices dimension dimension width).Carrier sizes) :
    matrix.val.det.natAbs < 2 ^ MvPolynomial.eval sizes (hermiteAlternatingEntryWidth dimension width) := by
  have bound := IntegerMatrix.determinant_bound (MvPolynomial.eval sizes width)
    (MvPolynomial.eval sizes dimension) matrix.val matrix.property
  exact bound.trans_le (pow_le_pow_right₀ (by decide) (by
    simp only [hermiteAlternatingEntryWidth, map_add, map_mul, map_one]
    omega))

private noncomputable def prepare (dimension width : MvPolynomial Parameter ℕ) :=
  (Realizable.Internal.integerMatrixWiden dimension dimension width
    (dimension * (width + dimension) + 1) (hermiteAlternatingEntryWidth dimension width)
    (by dsimp [hermiteAlternatingEntryWidth]; ring)).withPrecondition
    (fun _ arguments => (arguments ()).val.IsLowerTriangular ∧ ∀ index, 0 < (arguments ()).val index index)
    (by intros; trivial)

private theorem prepare_permitted (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (prepare dimension width).Arguments sizes)
    (valid : (prepare dimension width).precondition sizes arguments) :
    (Realizable.Internal.integerHermiteAlternatingPair dimension (hermiteAlternatingEntryWidth dimension width)).precondition sizes
      (fun _ => (prepare dimension width).compute sizes ⟨arguments, valid⟩) := by
  change (arguments ()).val.IsLowerTriangular ∧ (∀ index, 0 < (arguments ()).val index index) ∧
    (arguments ()).val.det.natAbs < 2 ^ MvPolynomial.eval sizes (hermiteAlternatingEntryWidth dimension width)
  refine ⟨valid.1, valid.2, ?_⟩
  exact hermiteAlternatingEntryWidth_det_bound dimension width sizes (arguments ())

/-- One pair on positive lower triangular input, with all storage derived internally. -/
noncomputable def integerHermiteAlternatingStep (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (prepare dimension width).followedBy
    (Realizable.Internal.integerHermiteAlternatingPair dimension (hermiteAlternatingEntryWidth dimension width))
    rfl (prepare_permitted dimension width)

/-- Preparing the common width and resizing all three outputs are certified. -/
theorem integerHermiteAlternatingStep_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingStep dimension width).Realizable := by
  have prepared := (Realizable.Internal.integerMatrixWiden_realizable dimension dimension width
    (dimension * (width + dimension) + 1) (hermiteAlternatingEntryWidth dimension width)
    (by dsimp [hermiteAlternatingEntryWidth]; ring)).withPrecondition
    (prepare dimension width).precondition (by intros; trivial)
  exact prepared.followedBy
    (Realizable.Internal.integerHermiteAlternatingPair_realizable dimension (hermiteAlternatingEntryWidth dimension width))
    rfl (prepare_permitted dimension width)

/-- The prepared, bounded pair still returns exactly the mathematical alternating step. -/
theorem integerHermiteAlternatingStep_correct (dimension width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingStep dimension width).Arguments sizes //
      (integerHermiteAlternatingStep dimension width).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingStep dimension width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingStep (arguments.val ()).val :=
  Realizable.Internal.integerHermiteAlternatingPair_correct dimension (hermiteAlternatingEntryWidth dimension width) sizes
    ⟨fun _ => (prepare dimension width).compute sizes arguments,
      prepare_permitted dimension width sizes arguments.val arguments.property⟩

end Polytime2.Computation
