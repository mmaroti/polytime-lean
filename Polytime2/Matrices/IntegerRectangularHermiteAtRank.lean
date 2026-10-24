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

import Polytime2.Matrices.IntegerLeadingBlock
import Polytime2.Matrices.IntegerRectangularHermite

/-! # Rectangular Hermite reduction at an active rank

Extract the leading active square block and lift its diagonalization to the
full rectangular dimensions. Output capacities depend only on the host row
count and input width, so the active rank can subsequently be decoded inside
a computed-size call.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def active (rows columns rank width : MvPolynomial Parameter ℕ) :=
  (integerMatrixLeadingBlock rows columns rank width).withPrecondition
    (integerLeadingBlockDiagonalize rows columns rank width).precondition (fun _ _ valid => valid.choose)

private noncomputable def raw (rows columns rank width : MvPolynomial Parameter ℕ) :=
  (active rows columns rank width).followedBy (integerRectangularHermite rows columns rank width) rfl
    (fun _ _ valid => ⟨valid.choose, valid.choose_spec⟩)

private theorem raw_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (raw rows columns rank width).Realizable :=
  ((integerMatrixLeadingBlock_realizable rows columns rank width).withPrecondition
    (integerLeadingBlockDiagonalize rows columns rank width).precondition (fun _ _ valid => valid.choose)).followedBy
    (integerRectangularHermite_realizable rows columns rank width) rfl (fun _ _ valid => ⟨valid.choose, valid.choose_spec⟩)

/-- A host-dimension output capacity independent of the active rank. -/
noncomputable def rectangularHermiteOutputWidth (rows width : MvPolynomial Parameter ℕ) :=
  hermiteAlternatingEntryWidth rows width +
    hermiteAlternatingRunBasisWidth rows (hermiteAlternatingEntryWidth rows width) (hermiteAlternatingBudget rows width) + 1

private theorem outputFits (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (raw rows columns rank width).Arguments sizes //
      (raw rows columns rank width).precondition sizes arguments}) :
    let result := (raw rows columns rank width).compute sizes arguments
    let bound := 2 ^ MvPolynomial.eval sizes (rectangularHermiteOutputWidth rows width)
    (∀ row column, (result.1.val row column).natAbs < bound) ∧
    (∀ row column, (result.2.1.val row column).natAbs < bound) ∧
    (∀ row column, (result.2.2.val row column).natAbs < bound) := by
  have rankBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows := arguments.property.choose.1
  have entryLe : MvPolynomial.eval sizes (hermiteAlternatingEntryWidth rank width) ≤
      MvPolynomial.eval sizes (hermiteAlternatingEntryWidth rows width) := by
    simp only [hermiteAlternatingEntryWidth, map_add, map_mul, map_one]
    gcongr
  have basisLe : MvPolynomial.eval sizes
      (hermiteAlternatingRunBasisWidth rank (hermiteAlternatingEntryWidth rank width) (hermiteAlternatingBudget rank width)) ≤
      MvPolynomial.eval sizes
      (hermiteAlternatingRunBasisWidth rows (hermiteAlternatingEntryWidth rows width) (hermiteAlternatingBudget rows width)) := by
    simp [hermiteAlternatingRunBasisWidth, hermiteAlternatingBasisWidth, hermiteAlternatingBudget,
      IntegerMatrix.hermiteSweepBasisIncrement, hermiteAlternatingEntryWidth]
    gcongr
  have entryCapacity : MvPolynomial.eval sizes (hermiteAlternatingEntryWidth rank width + 1) ≤
      MvPolynomial.eval sizes (rectangularHermiteOutputWidth rows width) := by
    simp only [rectangularHermiteOutputWidth, map_add, map_one]
    omega
  have basisCapacity : MvPolynomial.eval sizes
      (hermiteAlternatingRunBasisWidth rank (hermiteAlternatingEntryWidth rank width) (hermiteAlternatingBudget rank width) + 1) ≤
      MvPolynomial.eval sizes (rectangularHermiteOutputWidth rows width) := by
    simp only [rectangularHermiteOutputWidth, map_add, map_one]
    omega
  let result := (raw rows columns rank width).compute sizes arguments
  exact ⟨fun row column => (result.1.property row column).trans_le (pow_le_pow_right₀ (by decide) entryCapacity),
    fun row column => (result.2.1.property row column).trans_le (pow_le_pow_right₀ (by decide) basisCapacity),
    fun row column => (result.2.2.property row column).trans_le (pow_le_pow_right₀ (by decide) basisCapacity)⟩

/-- Reduce a leading active block, returning all full matrices at a host-derived width. -/
noncomputable def integerRectangularHermiteAtRank (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (raw rows columns rank width).inputDomains
  outputDomain := (integerMatrices rows columns (rectangularHermiteOutputWidth rows width)).prod
    ((integerMatrices rows rows (rectangularHermiteOutputWidth rows width)).prod
      (integerMatrices columns columns (rectangularHermiteOutputWidth rows width)))
  precondition := (raw rows columns rank width).precondition
  compute sizes arguments :=
    let result := (raw rows columns rank width).compute sizes arguments
    (⟨result.1.val, (outputFits rows columns rank width sizes arguments).1⟩,
      ⟨result.2.1.val, (outputFits rows columns rank width sizes arguments).2.1⟩,
      ⟨result.2.2.val, (outputFits rows columns rank width sizes arguments).2.2⟩)

/-- Extraction, square reduction, rectangular lifting, and host-width resizing are realized. -/
theorem integerRectangularHermiteAtRank_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermiteAtRank rows columns rank width).Realizable := by
  let computation := integerRectangularHermiteAtRank rows columns rank width
  let entryWidth := hermiteAlternatingEntryWidth rank width + 1
  let basisWidth := hermiteAlternatingRunBasisWidth rank (hermiteAlternatingEntryWidth rank width) (hermiteAlternatingBudget rank width) + 1
  let target := rectangularHermiteOutputWidth rows width
  have actual := raw_realizable rows columns rank width
  have matrix := actual.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have bases := actual.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have left := bases.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have right := bases.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have matrixReady := matrix.followedBy (integerMatrixResize_realizable rows columns entryWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).1)
  have leftReady := left.followedBy (integerMatrixResize_realizable rows rows basisWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).2.1)
  have rightReady := right.followedBy (integerMatrixResize_realizable columns columns basisWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).2.2)
  have paired := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ leftReady rightReady
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ matrixReady paired

/-- Host-width preparation preserves the exact mathematical rectangular reduction. -/
theorem integerRectangularHermiteAtRank_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteAtRank rows columns rank width).Arguments sizes //
      (integerRectangularHermiteAtRank rows columns rank width).precondition sizes arguments}) :
    let result := (integerRectangularHermiteAtRank rows columns rank width).compute sizes arguments
    let bounds := arguments.property.choose
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.rectangularHermiteRun bounds.1 bounds.2 (MvPolynomial.eval sizes width)
        ((arguments.val ()).val.submatrix (Fin.castLE bounds.1) (Fin.castLE bounds.2)) :=
  integerRectangularHermite_correct rows columns rank width sizes
    ⟨fun _ => (active rows columns rank width).compute sizes arguments,
      ⟨arguments.property.choose, arguments.property.choose_spec⟩⟩

/-- For a supported rectangular input, both full bases retain its presentation. -/
theorem integerRectangularHermiteAtRank_preserves (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteAtRank rows columns rank width).Arguments sizes //
      (integerRectangularHermiteAtRank rows columns rank width).precondition sizes arguments})
    (zeroRows : ∀ row, MvPolynomial.eval sizes rank ≤ row.val → (arguments.val ()).val row = 0)
    (zeroColumns : ∀ column, MvPolynomial.eval sizes rank ≤ column.val → (arguments.val ()).val.transpose column = 0) :
    let result := (integerRectangularHermiteAtRank rows columns rank width).compute sizes arguments
    result.2.1.val * (arguments.val ()).val * result.2.2.val = result.1.val ∧
      IsUnit result.2.1.val.det ∧ IsUnit result.2.2.val.det := by
  have preserved := IntegerMatrix.rectangularHermiteRun_of_supported arguments.property.choose.1 arguments.property.choose.2
    (MvPolynomial.eval sizes width) (arguments.val ()).val zeroRows zeroColumns
  rw [← integerRectangularHermiteAtRank_correct rows columns rank width sizes arguments] at preserved
  exact preserved

end Polytime2.Computation
